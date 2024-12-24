Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUP_UNIQUE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_NOT_LE_spec.
Require Import SELECT_UNIQUE_spec.
Require Import sup_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339379_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
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
Lemma lem5154373 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5154374 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5154375 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5154374 t1) (@lem5154373 t1)). Qed.
Lemma lem5154376 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5154375 t1 t2). Qed.
Lemma lem5154377 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5154378 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5154377 t1 t2) (@lem5154376 t1 t2)). Qed.
Lemma lem5154379 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5154378 t1 t2 t3). Qed.
Lemma lem5154380 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5154381 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5154380 t1 t2 t3) (@lem5154379 t1 t2 t3)). Qed.
Lemma lem5154382 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5154381 t1 t2 t3)). Qed.
Lemma lem5154383 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem5154384 {A : Type'} (P : A -> Prop) (h1 : term7 A) : term8 A P.
Proof. exact (@lem5154383 A h1 P). Qed.
Lemma lem5154385 {A : Type'} (P : A -> Prop) : (term8 A P) = (term9 A P).
Proof. exact (eq_refl (term8 A P)). Qed.
Lemma lem5154386 {A : Type'} (P : A -> Prop) (h1 : term7 A) : term9 A P.
Proof. exact (EQ_MP (@lem5154385 A P) (@lem5154384 A P h1)). Qed.
Lemma lem5154387 {A : Type'} (P : A -> Prop) (x : A) (h1 : term7 A) : term10 A P x.
Proof. exact (@lem5154386 A P h1 x). Qed.
Lemma lem5154388 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem5154389 {A : Type'} (P : A -> Prop) (x : A) (h1 : term7 A) : term11 A P x.
Proof. exact (EQ_MP (@lem5154388 A P x) (@lem5154387 A P x h1)). Qed.
Lemma lem5154390 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) : term12 A P x.
Proof. exact (h1). Qed.
Lemma lem5154391 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) (h2 : term7 A) : (@ε A P) = x.
Proof. exact (@lem5154389 A P x h2 (@lem5154390 A P x h1)). Qed.
Lemma lem5154392 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) : term13 A P x.
Proof. exact (fun h0 : term7 A => @lem5154391 A P x h1 h0). Qed.
Lemma lem5154393 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem5154394 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) (h2 : term7 A) : (@ε A P) = x.
Proof. exact (@lem5154392 A P x h1 (@lem5154393 A h2)). Qed.
Lemma lem5154395 {A : Type'} (P : A -> Prop) (x : A) (h1 : term7 A) : term11 A P x.
Proof. exact (fun h0 : term12 A P x => @lem5154394 A P x h0 h1). Qed.
Lemma lem5154396 {A : Type'} (P : A -> Prop) (h1 : term7 A) : term9 A P.
Proof. exact (fun x : A => @lem5154395 A P x h1). Qed.
Lemma lem5154397 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (fun P : A -> Prop => @lem5154396 A P h1). Qed.
Lemma lem5154398 {A : Type'} : term14 A.
Proof. exact (fun h0 : term7 A => @lem5154397 A h0). Qed.
Lemma lem5154399 {A : Type'} : term7 A.
Proof. exact (@lem5154398 A (@lem9522 A)). Qed.
Lemma lem5154400 {A : Type'} (P : A -> Prop) : term8 A P.
Proof. exact (@lem5154399 A P). Qed.
Lemma lem5154401 {A : Type'} (P : A -> Prop) : (term8 A P) = (term9 A P).
Proof. exact (eq_refl (term8 A P)). Qed.
Lemma lem5154402 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (EQ_MP (@lem5154401 A P) (@lem5154400 A P)). Qed.
Lemma lem5154403 {A : Type'} (P : A -> Prop) (x : A) : term10 A P x.
Proof. exact (@lem5154402 A P x). Qed.
Lemma lem5154404 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem5154406 (s : real -> Prop) : term15 s.
Proof. exact (@lem5133933 s). Qed.
Lemma lem5154407 (s : real -> Prop) : (term15 s) = ((sup s) = (term16 s)).
Proof. exact (eq_refl (term15 s)). Qed.
Lemma lem5154409 (b : real) (s : real -> Prop) (h1 : term17 b s) : term17 b s.
Proof. exact (h1). Qed.
Lemma lem5154410 (b : real) (s : real -> Prop) (h1 : term18 b s) : term18 b s.
Proof. exact (h1). Qed.
Lemma lem5154411 (s : real -> Prop) (b : real) (h1 : term19 s b) : term19 s b.
Proof. exact (h1). Qed.
Lemma lem5154415 (s : real -> Prop) : (sup s) = (term16 s).
Proof. exact (EQ_MP (@lem5154407 s) (@lem5154406 s)). Qed.
Lemma lem5154436 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5154437 (s : real -> Prop) : (term20 s) = (term21 s).
Proof. exact (MK_COMB (@lem5154436) (@lem5154415 s)). Qed.
Lemma lem5154438 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5154439 (s : real -> Prop) (b : real) : ((sup s) = b) = ((term16 s) = b).
Proof. exact (MK_COMB (@lem5154437 s) (@lem5154438 b)). Qed.
Lemma lem5154442 (s : real -> Prop) (b : real) : ((term16 s) = b) = ((sup s) = b).
Proof. exact (SYM (@lem5154439 s b)). Qed.
Lemma lem5154444 {A : Type'} (P : A -> Prop) (x : A) : term11 A P x.
Proof. exact (EQ_MP (@lem5154404 A P x) (@lem5154403 A P x)). Qed.
Lemma lem5154445 (P : real -> Prop) (x : real) : term22 P x.
Proof. exact (@lem5154444 real P x). Qed.
Lemma lem5154446 (s : real -> Prop) (b : real) : term23 s b.
Proof. exact (@lem5154445 (term24 s) b). Qed.
Lemma lem5154448 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5154449 (s : real -> Prop) (b : real) : (term26 s b) = (term27 s b).
Proof. exact (@lem5154448 (term26 s b)). Qed.
Lemma lem5154450 (s : real -> Prop) (b : real) : (term27 s b) = (term26 s b).
Proof. exact (SYM (@lem5154449 s b)). Qed.
Lemma lem5154451 (s : real -> Prop) (b : real) (h1 : term28 s b) : term28 s b.
Proof. exact (h1). Qed.
Lemma lem5154454 (s : real -> Prop) (b : real) (h1 : term29 s b) : term29 s b.
Proof. exact (h1). Qed.
Lemma lem5154455 (s : real -> Prop) (b : real) : term30 s b.
Proof. exact (fun h0 : term29 s b => @lem5154454 s b h0). Qed.
Lemma lem5154456 (s : real -> Prop) (b : real) (h1 : term30 s b) : term30 s b.
Proof. exact (h1). Qed.
Lemma lem5154457 (s : real -> Prop) (b : real) (h1 : term29 s b) : term29 s b.
Proof. exact (h1). Qed.
Lemma lem5154458 (s : real -> Prop) (b : real) (h1 : term29 s b) (h2 : term30 s b) : term29 s b.
Proof. exact (@lem5154456 s b h2 (@lem5154457 s b h1)). Qed.
Lemma lem5154459 (s : real -> Prop) (b : real) (h1 : term29 s b) : term31 s b.
Proof. exact (fun h0 : term30 s b => @lem5154458 s b h1 h0). Qed.
Lemma lem5154460 (s : real -> Prop) (b : real) (h1 : term30 s b) : term30 s b.
Proof. exact (h1). Qed.
Lemma lem5154461 (s : real -> Prop) (b : real) (h1 : term29 s b) (h2 : term30 s b) : term29 s b.
Proof. exact (@lem5154459 s b h1 (@lem5154460 s b h2)). Qed.
Lemma lem5154462 (s : real -> Prop) (b : real) (h1 : term30 s b) : term30 s b.
Proof. exact (fun h0 : term29 s b => @lem5154461 s b h0 h1). Qed.
Lemma lem5154463 (s : real -> Prop) (b : real) : term32 s b.
Proof. exact (fun h0 : term30 s b => @lem5154462 s b h0). Qed.
Lemma lem5154466 (s : real -> Prop) (b : real) : term30 s b.
Proof. exact (@lem5154463 s b (@lem5154455 s b)). Qed.
Lemma lem5154580 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5154581 : term33 = term34.
Proof. exact (@lem5154580 term35). Qed.
Lemma lem5154590 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem5154591 : term37 = term38.
Proof. exact (MK_COMB (@lem5154590) (@lem5154581)). Qed.
Lemma lem5154594 (s : real -> Prop) (b : real) : (term39 s b) = (term39 s b).
Proof. exact (eq_refl (term39 s b)). Qed.
Lemma lem5154595 (s : real -> Prop) (b : real) : (term40 s b) = (term41 s b).
Proof. exact (MK_COMB (@lem5154594 s b) (@lem5154591)). Qed.
Lemma lem5154598 (b : real) (s : real -> Prop) : (term42 b s) = (term42 b s).
Proof. exact (eq_refl (term42 b s)). Qed.
Lemma lem5154599 (s : real -> Prop) (b : real) : (term43 s b) = (term44 s b).
Proof. exact (MK_COMB (@lem5154598 b s) (@lem5154595 s b)). Qed.
Lemma lem5154602 (s : real -> Prop) (b : real) : (term45 s b) = (term45 s b).
Proof. exact (eq_refl (term45 s b)). Qed.
Lemma lem5154603 (s : real -> Prop) (b : real) : (term29 s b) = (term46 s b).
Proof. exact (MK_COMB (@lem5154602 s b) (@lem5154599 s b)). Qed.
Lemma lem5154606 (b : real) : (term47 b) = (term48 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5154603 s b)). Qed.
Lemma lem5154607 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5154608 (b : real) : (term49 b) = (term50 b).
Proof. exact (MK_COMB (@lem5154607) (@lem5154606 b)). Qed.
Lemma lem5154613 : term51 = term52.
Proof. exact (fun_ext (fun b : real => @lem5154608 b)). Qed.
Lemma lem5154614 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154615 : term53 = term54.
Proof. exact (MK_COMB (@lem5154614) (@lem5154613)). Qed.
Lemma lem5154620 (s : real -> Prop) (y : real) : (term55 s y) = (term56 s y).
Proof. exact (eq_refl (term55 s y)). Qed.
Lemma lem5154621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5154622 (s : real -> Prop) (y : real) : (term57 s y) = (term58 s y).
Proof. exact (MK_COMB (@lem5154621) (@lem5154620 s y)). Qed.
Lemma lem5154623 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5154624 (s : real -> Prop) (y : real) (b : real) : ((term55 s y) = (y = b)) = ((term56 s y) = (y = b)).
Proof. exact (MK_COMB (@lem5154622 s y) (@lem5154623 y b)). Qed.
Lemma lem5154625 (s : real -> Prop) (b : real) : (term59 s b) = (term60 s b).
Proof. exact (fun_ext (fun y : real => @lem5154624 s y b)). Qed.
Lemma lem5154626 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154627 (s : real -> Prop) (b : real) : (term26 s b) = (term61 s b).
Proof. exact (MK_COMB (@lem5154626) (@lem5154625 s b)). Qed.
Lemma lem5154628 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5154629 (s : real -> Prop) (b : real) : (term28 s b) = (term62 s b).
Proof. exact (MK_COMB (@lem5154628) (@lem5154627 s b)). Qed.
Lemma lem5154630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5154631 (s : real -> Prop) (b : real) : (term39 s b) = (term63 s b).
Proof. exact (MK_COMB (@lem5154630) (@lem5154629 s b)). Qed.
Lemma lem5154632 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem5154633 (s : real -> Prop) (b : real) : (term41 s b) = (term64 s b).
Proof. exact (MK_COMB (@lem5154631 s b) (@lem5154632)). Qed.
Lemma lem5154634 (b : real) (s : real -> Prop) : (term42 b s) = (term42 b s).
Proof. exact (eq_refl (term42 b s)). Qed.
Lemma lem5154635 (s : real -> Prop) (b : real) : (term44 s b) = (term65 s b).
Proof. exact (MK_COMB (@lem5154634 b s) (@lem5154633 s b)). Qed.
Lemma lem5154636 (s : real -> Prop) (b : real) : (term45 s b) = (term45 s b).
Proof. exact (eq_refl (term45 s b)). Qed.
Lemma lem5154637 (s : real -> Prop) (b : real) : (term46 s b) = (term66 s b).
Proof. exact (MK_COMB (@lem5154636 s b) (@lem5154635 s b)). Qed.
Lemma lem5154638 (b : real) : (term48 b) = (term67 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5154637 s b)). Qed.
Lemma lem5154639 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5154640 (b : real) : (term50 b) = (term68 b).
Proof. exact (MK_COMB (@lem5154639) (@lem5154638 b)). Qed.
Lemma lem5154641 : term52 = term69.
Proof. exact (fun_ext (fun b : real => @lem5154640 b)). Qed.
Lemma lem5154642 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154643 : term54 = term70.
Proof. exact (MK_COMB (@lem5154642) (@lem5154641)). Qed.
Lemma lem5154646 : term53 = term70.
Proof. exact (TRANS (@lem5154615) (@lem5154643)). Qed.
Lemma lem5154653 (y : real) (x : real) : ((term71 x y) = (real_lt y x)) = ((term71 x y) = (real_lt y x)).
Proof. exact (eq_refl ((term71 x y) = (real_lt y x))). Qed.
Lemma lem5154654 (x : real) : (term72 x) = (term72 x).
Proof. exact (fun_ext (fun y : real => @lem5154653 y x)). Qed.
Lemma lem5154655 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154656 (x : real) : (term73 x) = (term73 x).
Proof. exact (MK_COMB (@lem5154655) (@lem5154654 x)). Qed.
Lemma lem5154657 : term74 = term74.
Proof. exact (fun_ext (fun x : real => @lem5154656 x)). Qed.
Lemma lem5154658 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154659 : term35 = term35.
Proof. exact (MK_COMB (@lem5154658) (@lem5154657)). Qed.
Lemma lem5154660 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5154661 : term34 = term34.
Proof. exact (MK_COMB (@lem5154660) (@lem5154659)). Qed.
Lemma lem5154670 (x : real) (y : real) : ((term75 y x) = (x = y)) = ((term75 y x) = (x = y)).
Proof. exact (eq_refl ((term75 y x) = (x = y))). Qed.
Lemma lem5154671 (x : real) : (term76 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem5154670 x y)). Qed.
Lemma lem5154672 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154673 (x : real) : (term77 x) = (term77 x).
Proof. exact (MK_COMB (@lem5154672) (@lem5154671 x)). Qed.
Lemma lem5154674 : term78 = term78.
Proof. exact (fun_ext (fun x : real => @lem5154673 x)). Qed.
Lemma lem5154675 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154676 : term79 = term79.
Proof. exact (MK_COMB (@lem5154675) (@lem5154674)). Qed.
Lemma lem5154677 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5154678 : term36 = term36.
Proof. exact (MK_COMB (@lem5154677) (@lem5154676)). Qed.
Lemma lem5154679 : term38 = term38.
Proof. exact (MK_COMB (@lem5154678) (@lem5154661)). Qed.
Lemma lem5154680 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5154681 (y : real) (b : real) : (real_le y b) = (real_le y b).
Proof. exact (eq_refl (real_le y b)). Qed.
Lemma lem5154686 (s : real -> Prop) (x : real) (b : real) : (term80 s x b) = (term80 s x b).
Proof. exact (eq_refl (term80 s x b)). Qed.
Lemma lem5154687 (s : real -> Prop) (b : real) : (term81 s b) = (term81 s b).
Proof. exact (fun_ext (fun x : real => @lem5154686 s x b)). Qed.
Lemma lem5154688 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154689 (s : real -> Prop) (b : real) : (term19 s b) = (term19 s b).
Proof. exact (MK_COMB (@lem5154688) (@lem5154687 s b)). Qed.
Lemma lem5154690 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5154691 (s : real -> Prop) (b : real) : (term45 s b) = (term45 s b).
Proof. exact (MK_COMB (@lem5154690) (@lem5154689 s b)). Qed.
Lemma lem5154692 (s : real -> Prop) (y : real) (b : real) : (term82 s y b) = (term82 s y b).
Proof. exact (MK_COMB (@lem5154691 s b) (@lem5154681 y b)). Qed.
Lemma lem5154693 (s : real -> Prop) (y : real) : (term83 s y) = (term83 s y).
Proof. exact (fun_ext (fun b : real => @lem5154692 s y b)). Qed.
Lemma lem5154694 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154695 (s : real -> Prop) (y : real) : (term84 s y) = (term84 s y).
Proof. exact (MK_COMB (@lem5154694) (@lem5154693 s y)). Qed.
Lemma lem5154700 (s : real -> Prop) (x : real) (y : real) : (term80 s x y) = (term80 s x y).
Proof. exact (eq_refl (term80 s x y)). Qed.
Lemma lem5154701 (s : real -> Prop) (y : real) : (term81 s y) = (term81 s y).
Proof. exact (fun_ext (fun x : real => @lem5154700 s x y)). Qed.
Lemma lem5154702 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154703 (s : real -> Prop) (y : real) : (term19 s y) = (term19 s y).
Proof. exact (MK_COMB (@lem5154702) (@lem5154701 s y)). Qed.
Lemma lem5154704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5154705 (s : real -> Prop) (y : real) : (term85 s y) = (term85 s y).
Proof. exact (MK_COMB (@lem5154704) (@lem5154703 s y)). Qed.
Lemma lem5154706 (s : real -> Prop) (y : real) : (term56 s y) = (term56 s y).
Proof. exact (MK_COMB (@lem5154705 s y) (@lem5154695 s y)). Qed.
Lemma lem5154707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5154708 (s : real -> Prop) (y : real) : (term58 s y) = (term58 s y).
Proof. exact (MK_COMB (@lem5154707) (@lem5154706 s y)). Qed.
Lemma lem5154709 (s : real -> Prop) (y : real) (b : real) : ((term56 s y) = (y = b)) = ((term56 s y) = (y = b)).
Proof. exact (MK_COMB (@lem5154708 s y) (@lem5154680 y b)). Qed.
Lemma lem5154710 (s : real -> Prop) (b : real) : (term60 s b) = (term60 s b).
Proof. exact (fun_ext (fun y : real => @lem5154709 s y b)). Qed.
Lemma lem5154711 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154712 (s : real -> Prop) (b : real) : (term61 s b) = (term61 s b).
Proof. exact (MK_COMB (@lem5154711) (@lem5154710 s b)). Qed.
Lemma lem5154713 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5154714 (s : real -> Prop) (b : real) : (term62 s b) = (term62 s b).
Proof. exact (MK_COMB (@lem5154713) (@lem5154712 s b)). Qed.
Lemma lem5154715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5154716 (s : real -> Prop) (b : real) : (term63 s b) = (term63 s b).
Proof. exact (MK_COMB (@lem5154715) (@lem5154714 s b)). Qed.
Lemma lem5154717 (s : real -> Prop) (b : real) : (term64 s b) = (term64 s b).
Proof. exact (MK_COMB (@lem5154716 s b) (@lem5154679)). Qed.
Lemma lem5154722 (s : real -> Prop) (b' : real) (x : real) : (term86 s b' x) = (term86 s b' x).
Proof. exact (eq_refl (term86 s b' x)). Qed.
Lemma lem5154723 (s : real -> Prop) (b' : real) : (term87 s b') = (term87 s b').
Proof. exact (fun_ext (fun x : real => @lem5154722 s b' x)). Qed.
Lemma lem5154724 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5154725 (s : real -> Prop) (b' : real) : (term88 s b') = (term88 s b').
Proof. exact (MK_COMB (@lem5154724) (@lem5154723 s b')). Qed.
Lemma lem5154728 (b' : real) (b : real) : (term89 b' b) = (term89 b' b).
Proof. exact (eq_refl (term89 b' b)). Qed.
Lemma lem5154729 (b : real) (s : real -> Prop) (b' : real) : (term90 b s b') = (term90 b s b').
Proof. exact (MK_COMB (@lem5154728 b' b) (@lem5154725 s b')). Qed.
Lemma lem5154730 (b : real) (s : real -> Prop) : (term91 b s) = (term91 b s).
Proof. exact (fun_ext (fun b' : real => @lem5154729 b s b')). Qed.
Lemma lem5154731 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154732 (b : real) (s : real -> Prop) : (term18 b s) = (term18 b s).
Proof. exact (MK_COMB (@lem5154731) (@lem5154730 b s)). Qed.
Lemma lem5154733 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5154734 (b : real) (s : real -> Prop) : (term42 b s) = (term42 b s).
Proof. exact (MK_COMB (@lem5154733) (@lem5154732 b s)). Qed.
Lemma lem5154735 (s : real -> Prop) (b : real) : (term65 s b) = (term65 s b).
Proof. exact (MK_COMB (@lem5154734 b s) (@lem5154717 s b)). Qed.
Lemma lem5154740 (s : real -> Prop) (x : real) (b : real) : (term80 s x b) = (term80 s x b).
Proof. exact (eq_refl (term80 s x b)). Qed.
Lemma lem5154741 (s : real -> Prop) (b : real) : (term81 s b) = (term81 s b).
Proof. exact (fun_ext (fun x : real => @lem5154740 s x b)). Qed.
Lemma lem5154742 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154743 (s : real -> Prop) (b : real) : (term19 s b) = (term19 s b).
Proof. exact (MK_COMB (@lem5154742) (@lem5154741 s b)). Qed.
Lemma lem5154744 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5154745 (s : real -> Prop) (b : real) : (term45 s b) = (term45 s b).
Proof. exact (MK_COMB (@lem5154744) (@lem5154743 s b)). Qed.
Lemma lem5154746 (s : real -> Prop) (b : real) : (term66 s b) = (term66 s b).
Proof. exact (MK_COMB (@lem5154745 s b) (@lem5154735 s b)). Qed.
Lemma lem5154747 (b : real) : (term67 b) = (term67 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5154746 s b)). Qed.
Lemma lem5154748 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5154749 (b : real) : (term68 b) = (term68 b).
Proof. exact (MK_COMB (@lem5154748) (@lem5154747 b)). Qed.
Lemma lem5154750 : term69 = term69.
Proof. exact (fun_ext (fun b : real => @lem5154749 b)). Qed.
Lemma lem5154751 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154752 : term70 = term70.
Proof. exact (MK_COMB (@lem5154751) (@lem5154750)). Qed.
Lemma lem5154857 : term53 = term70.
Proof. exact (TRANS (@lem5154646) (@lem5154752)). Qed.
Lemma lem5154858 : term70 = term53.
Proof. exact (SYM (@lem5154857)). Qed.
Lemma lem5154859 (s : real -> Prop) (b : real) (h1 : term19 s b) : term19 s b.
Proof. exact (h1). Qed.
Lemma lem5154860 (b : real) (s : real -> Prop) (h1 : term18 b s) : term18 b s.
Proof. exact (h1). Qed.
Lemma lem5154861 (s : real -> Prop) (b : real) (h1 : term62 s b) : term62 s b.
Proof. exact (h1). Qed.
Lemma lem5154862 (h1 : term79) : term79.
Proof. exact (h1). Qed.
Lemma lem5154863 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem5154870 (s : real -> Prop) (x : real) (b : real) : (term80 s x b) = (term92 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5154871 (s : real -> Prop) (b : real) : (term81 s b) = (term93 s b).
Proof. exact (fun_ext (fun x : real => @lem5154870 s x b)). Qed.
Lemma lem5154872 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154925 (s : real -> Prop) (b : real) : (term19 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5154872) (@lem5154871 s b)). Qed.
Lemma lem5154926 (s : real -> Prop) (b : real) (h1 : term19 s b) : term94 s b.
Proof. exact (EQ_MP (@lem5154925 s b) (@lem5154859 s b h1)). Qed.
Lemma lem5154932 (s : real -> Prop) (b' : real) (x : real) : (term86 s b' x) = (term86 s b' x).
Proof. exact (eq_refl (term86 s b' x)). Qed.
Lemma lem5154933 (s : real -> Prop) (b' : real) : (term87 s b') = (term87 s b').
Proof. exact (fun_ext (fun x : real => @lem5154932 s b' x)). Qed.
Lemma lem5154934 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5154935 (s : real -> Prop) (b' : real) : (term88 s b') = (term88 s b').
Proof. exact (MK_COMB (@lem5154934) (@lem5154933 s b')). Qed.
Lemma lem5154937 (b' : real) (b : real) : (term95 b' b) = (term95 b' b).
Proof. exact (eq_refl (term95 b' b)). Qed.
Lemma lem5154938 (b : real) (s : real -> Prop) (b' : real) : (term96 b s b') = (term96 b s b').
Proof. exact (MK_COMB (@lem5154937 b' b) (@lem5154935 s b')). Qed.
Lemma lem5154939 (b : real) (s : real -> Prop) (b' : real) : (term90 b s b') = (term96 b s b').
Proof. exact (@lem17265 (real_lt b' b) (term88 s b')). Qed.
Lemma lem5154940 (b : real) (s : real -> Prop) (b' : real) : (term90 b s b') = (term96 b s b').
Proof. exact (TRANS (@lem5154939 b s b') (@lem5154938 b s b')). Qed.
Lemma lem5154941 (b : real) (s : real -> Prop) : (term91 b s) = (term97 b s).
Proof. exact (fun_ext (fun b' : real => @lem5154940 b s b')). Qed.
Lemma lem5154942 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5154943 (b : real) (s : real -> Prop) : (term18 b s) = (term98 b s).
Proof. exact (MK_COMB (@lem5154942) (@lem5154941 b s)). Qed.
Lemma lem5155042 {A : Type'} (P : Prop) (Q : A -> Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5155043 (P : Prop) (Q : real -> Prop) : (term101 P Q) = (term102 P Q).
Proof. exact (@lem5155042 real P Q). Qed.
Lemma lem5155044 (b : real) (s : real -> Prop) (b' : real) : (term103 b s b') = (term104 b s b').
Proof. exact (@lem5155043 (term105 b' b) (term87 s b')). Qed.
Lemma lem5155045 (s : real -> Prop) (b' : real) (x : real) : (term106 s b' x) = (term86 s b' x).
Proof. exact (eq_refl (term106 s b' x)). Qed.
Lemma lem5155046 (s : real -> Prop) (b' : real) : (term107 s b') = (term87 s b').
Proof. exact (fun_ext (fun x : real => @lem5155045 s b' x)). Qed.
Lemma lem5155047 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155048 (s : real -> Prop) (b' : real) : (term108 s b') = (term88 s b').
Proof. exact (MK_COMB (@lem5155047) (@lem5155046 s b')). Qed.
Lemma lem5155049 (b' : real) (b : real) : (term95 b' b) = (term95 b' b).
Proof. exact (eq_refl (term95 b' b)). Qed.
Lemma lem5155050 (b : real) (s : real -> Prop) (b' : real) : (term103 b s b') = (term96 b s b').
Proof. exact (MK_COMB (@lem5155049 b' b) (@lem5155048 s b')). Qed.
Lemma lem5155051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155052 (b : real) (s : real -> Prop) (b' : real) : (term109 b s b') = (term110 b s b').
Proof. exact (MK_COMB (@lem5155051) (@lem5155050 b s b')). Qed.
Lemma lem5155053 (s : real -> Prop) (b' : real) (x : real) : (term106 s b' x) = (term86 s b' x).
Proof. exact (eq_refl (term106 s b' x)). Qed.
Lemma lem5155054 (b' : real) (b : real) : (term95 b' b) = (term95 b' b).
Proof. exact (eq_refl (term95 b' b)). Qed.
Lemma lem5155055 (b : real) (s : real -> Prop) (b' : real) (x : real) : (term111 b s b' x) = (term112 b s b' x).
Proof. exact (MK_COMB (@lem5155054 b' b) (@lem5155053 s b' x)). Qed.
Lemma lem5155056 (b : real) (s : real -> Prop) (b' : real) : (term113 b s b') = (term114 b s b').
Proof. exact (fun_ext (fun x : real => @lem5155055 b s b' x)). Qed.
Lemma lem5155057 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155058 (b : real) (s : real -> Prop) (b' : real) : (term104 b s b') = (term115 b s b').
Proof. exact (MK_COMB (@lem5155057) (@lem5155056 b s b')). Qed.
Lemma lem5155059 (b : real) (s : real -> Prop) (b' : real) : ((term103 b s b') = (term104 b s b')) = ((term96 b s b') = (term115 b s b')).
Proof. exact (MK_COMB (@lem5155052 b s b') (@lem5155058 b s b')). Qed.
Lemma lem5155060 (b : real) (s : real -> Prop) (b' : real) : (term96 b s b') = (term115 b s b').
Proof. exact (EQ_MP (@lem5155059 b s b') (@lem5155044 b s b')). Qed.
Lemma lem5155061 (b : real) (s : real -> Prop) : (term97 b s) = (term116 b s).
Proof. exact (fun_ext (fun b' : real => @lem5155060 b s b')). Qed.
Lemma lem5155062 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155063 (b : real) (s : real -> Prop) : (term98 b s) = (term117 b s).
Proof. exact (MK_COMB (@lem5155062) (@lem5155061 b s)). Qed.
Lemma lem5155065 {A B : Type'} (P : type1413 A B) : (term118 A B P) = (term119 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5155066 (P : type1626) : (term120 P) = (term121 P).
Proof. exact (@lem5155065 real real P). Qed.
Lemma lem5155067 (b : real) (s : real -> Prop) : (term122 b s) = (term123 b s).
Proof. exact (@lem5155066 (term124 b s)). Qed.
Lemma lem5155068 (b : real) (s : real -> Prop) (b' : real) : (term125 b s b') = (term114 b s b').
Proof. exact (eq_refl (term125 b s b')). Qed.
Lemma lem5155069 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5155070 (b : real) (s : real -> Prop) (b' : real) (x : real) : (term126 b s b' x) = (term127 b s b' x).
Proof. exact (MK_COMB (@lem5155068 b s b') (@lem5155069 x)). Qed.
Lemma lem5155071 (b : real) (s : real -> Prop) (b' : real) (x : real) : (term127 b s b' x) = (term112 b s b' x).
Proof. exact (eq_refl (term127 b s b' x)). Qed.
Lemma lem5155072 (b : real) (s : real -> Prop) (b' : real) (x : real) : (term126 b s b' x) = (term112 b s b' x).
Proof. exact (TRANS (@lem5155070 b s b' x) (@lem5155071 b s b' x)). Qed.
Lemma lem5155073 (b : real) (s : real -> Prop) (b' : real) : (term128 b s b') = (term114 b s b').
Proof. exact (fun_ext (fun x : real => @lem5155072 b s b' x)). Qed.
Lemma lem5155074 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155075 (b : real) (s : real -> Prop) (b' : real) : (term129 b s b') = (term115 b s b').
Proof. exact (MK_COMB (@lem5155074) (@lem5155073 b s b')). Qed.
Lemma lem5155076 (b : real) (s : real -> Prop) : (term130 b s) = (term116 b s).
Proof. exact (fun_ext (fun b' : real => @lem5155075 b s b')). Qed.
Lemma lem5155077 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155078 (b : real) (s : real -> Prop) : (term122 b s) = (term117 b s).
Proof. exact (MK_COMB (@lem5155077) (@lem5155076 b s)). Qed.
Lemma lem5155079 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155080 (b : real) (s : real -> Prop) : (term131 b s) = (term132 b s).
Proof. exact (MK_COMB (@lem5155079) (@lem5155078 b s)). Qed.
Lemma lem5155081 (b : real) (s : real -> Prop) (b' : real) : (term125 b s b') = (term114 b s b').
Proof. exact (eq_refl (term125 b s b')). Qed.
Lemma lem5155082 (x : real -> real) (b' : real) : (x b') = (x b').
Proof. exact (eq_refl (x b')). Qed.
Lemma lem5155083 (b : real) (s : real -> Prop) (x : real -> real) (b' : real) : (term133 b s x b') = (term134 b s x b').
Proof. exact (MK_COMB (@lem5155081 b s b') (@lem5155082 x b')). Qed.
Lemma lem5155084 (b : real) (s : real -> Prop) (x : real -> real) (b' : real) : (term134 b s x b') = (term135 b s x b').
Proof. exact (eq_refl (term134 b s x b')). Qed.
Lemma lem5155085 (b : real) (s : real -> Prop) (x : real -> real) (b' : real) : (term133 b s x b') = (term135 b s x b').
Proof. exact (TRANS (@lem5155083 b s x b') (@lem5155084 b s x b')). Qed.
Lemma lem5155086 (b : real) (s : real -> Prop) (x : real -> real) : (term136 b s x) = (term137 b s x).
Proof. exact (fun_ext (fun b' : real => @lem5155085 b s x b')). Qed.
Lemma lem5155087 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155088 (b : real) (s : real -> Prop) (x : real -> real) : (term138 b s x) = (term139 b s x).
Proof. exact (MK_COMB (@lem5155087) (@lem5155086 b s x)). Qed.
Lemma lem5155089 (b : real) (s : real -> Prop) : (term140 b s) = (term141 b s).
Proof. exact (fun_ext (fun x : real -> real => @lem5155088 b s x)). Qed.
Lemma lem5155090 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5155091 (b : real) (s : real -> Prop) : (term123 b s) = (term142 b s).
Proof. exact (MK_COMB (@lem5155090) (@lem5155089 b s)). Qed.
Lemma lem5155092 (b : real) (s : real -> Prop) : ((term122 b s) = (term123 b s)) = ((term117 b s) = (term142 b s)).
Proof. exact (MK_COMB (@lem5155080 b s) (@lem5155091 b s)). Qed.
Lemma lem5155093 (b : real) (s : real -> Prop) : (term117 b s) = (term142 b s).
Proof. exact (EQ_MP (@lem5155092 b s) (@lem5155067 b s)). Qed.
Lemma lem5155095 (b : real) (s : real -> Prop) : (term98 b s) = (term142 b s).
Proof. exact (TRANS (@lem5155063 b s) (@lem5155093 b s)). Qed.
Lemma lem5155096 (b : real) (s : real -> Prop) : (term18 b s) = (term142 b s).
Proof. exact (TRANS (@lem5154943 b s) (@lem5155095 b s)). Qed.
Lemma lem5155097 (b : real) (s : real -> Prop) (h1 : term18 b s) : term142 b s.
Proof. exact (EQ_MP (@lem5155096 b s) (@lem5154860 b s h1)). Qed.
Lemma lem5155106 (s : real -> Prop) (x : real) (y : real) : (term143 s x y) = (term144 s x y).
Proof. exact (@lem17362 (@IN real x s) (real_le x y)). Qed.
Lemma lem5155111 (s : real -> Prop) (x : real) (y : real) : (term80 s x y) = (term92 s x y).
Proof. exact (@lem17265 (@IN real x s) (real_le x y)). Qed.
Lemma lem5155112 (P : real -> Prop) : (term145 P) = (term146 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5155113 (s : real -> Prop) (y : real) : (term147 s y) = (term148 s y).
Proof. exact (@lem5155112 (term81 s y)). Qed.
Lemma lem5155114 (s : real -> Prop) (x : real) (y : real) : (term149 s y x) = (term80 s x y).
Proof. exact (eq_refl (term149 s y x)). Qed.
Lemma lem5155115 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5155116 (s : real -> Prop) (x : real) (y : real) : (term150 s y x) = (term143 s x y).
Proof. exact (MK_COMB (@lem5155115) (@lem5155114 s x y)). Qed.
Lemma lem5155117 (s : real -> Prop) (x : real) (y : real) : (term150 s y x) = (term144 s x y).
Proof. exact (TRANS (@lem5155116 s x y) (@lem5155106 s x y)). Qed.
Lemma lem5155118 (s : real -> Prop) (y : real) : (term151 s y) = (term152 s y).
Proof. exact (fun_ext (fun x : real => @lem5155117 s x y)). Qed.
Lemma lem5155119 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155120 (s : real -> Prop) (y : real) : (term148 s y) = (term153 s y).
Proof. exact (MK_COMB (@lem5155119) (@lem5155118 s y)). Qed.
Lemma lem5155121 (s : real -> Prop) (y : real) : (term147 s y) = (term153 s y).
Proof. exact (TRANS (@lem5155113 s y) (@lem5155120 s y)). Qed.
Lemma lem5155122 (s : real -> Prop) (y : real) : (term81 s y) = (term93 s y).
Proof. exact (fun_ext (fun x : real => @lem5155111 s x y)). Qed.
Lemma lem5155123 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155124 (s : real -> Prop) (y : real) : (term19 s y) = (term94 s y).
Proof. exact (MK_COMB (@lem5155123) (@lem5155122 s y)). Qed.
Lemma lem5155133 (s : real -> Prop) (x : real) (b : real) : (term143 s x b) = (term144 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5155138 (s : real -> Prop) (x : real) (b : real) : (term80 s x b) = (term92 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5155139 (P : real -> Prop) : (term145 P) = (term146 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5155140 (s : real -> Prop) (b : real) : (term147 s b) = (term148 s b).
Proof. exact (@lem5155139 (term81 s b)). Qed.
Lemma lem5155141 (s : real -> Prop) (x : real) (b : real) : (term149 s b x) = (term80 s x b).
Proof. exact (eq_refl (term149 s b x)). Qed.
Lemma lem5155142 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5155143 (s : real -> Prop) (x : real) (b : real) : (term150 s b x) = (term143 s x b).
Proof. exact (MK_COMB (@lem5155142) (@lem5155141 s x b)). Qed.
Lemma lem5155144 (s : real -> Prop) (x : real) (b : real) : (term150 s b x) = (term144 s x b).
Proof. exact (TRANS (@lem5155143 s x b) (@lem5155133 s x b)). Qed.
Lemma lem5155145 (s : real -> Prop) (b : real) : (term151 s b) = (term152 s b).
Proof. exact (fun_ext (fun x : real => @lem5155144 s x b)). Qed.
Lemma lem5155146 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155147 (s : real -> Prop) (b : real) : (term148 s b) = (term153 s b).
Proof. exact (MK_COMB (@lem5155146) (@lem5155145 s b)). Qed.
Lemma lem5155148 (s : real -> Prop) (b : real) : (term147 s b) = (term153 s b).
Proof. exact (TRANS (@lem5155140 s b) (@lem5155147 s b)). Qed.
Lemma lem5155149 (s : real -> Prop) (b : real) : (term81 s b) = (term93 s b).
Proof. exact (fun_ext (fun x : real => @lem5155138 s x b)). Qed.
Lemma lem5155150 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155151 (s : real -> Prop) (b : real) : (term19 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5155150) (@lem5155149 s b)). Qed.
Lemma lem5155152 (y : real) (b : real) : (term71 y b) = (term71 y b).
Proof. exact (eq_refl (term71 y b)). Qed.
Lemma lem5155153 (y : real) (b : real) : (real_le y b) = (real_le y b).
Proof. exact (eq_refl (real_le y b)). Qed.
Lemma lem5155154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5155155 (s : real -> Prop) (b : real) : (term85 s b) = (term154 s b).
Proof. exact (MK_COMB (@lem5155154) (@lem5155151 s b)). Qed.
Lemma lem5155156 (s : real -> Prop) (y : real) (b : real) : (term155 s y b) = (term156 s y b).
Proof. exact (MK_COMB (@lem5155155 s b) (@lem5155152 y b)). Qed.
Lemma lem5155157 (s : real -> Prop) (y : real) (b : real) : (term157 s y b) = (term155 s y b).
Proof. exact (@lem17362 (term19 s b) (real_le y b)). Qed.
Lemma lem5155158 (s : real -> Prop) (y : real) (b : real) : (term157 s y b) = (term156 s y b).
Proof. exact (TRANS (@lem5155157 s y b) (@lem5155156 s y b)). Qed.
Lemma lem5155159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155160 (s : real -> Prop) (b : real) : (term158 s b) = (term159 s b).
Proof. exact (MK_COMB (@lem5155159) (@lem5155148 s b)). Qed.
Lemma lem5155161 (s : real -> Prop) (y : real) (b : real) : (term160 s y b) = (term161 s y b).
Proof. exact (MK_COMB (@lem5155160 s b) (@lem5155153 y b)). Qed.
Lemma lem5155162 (s : real -> Prop) (y : real) (b : real) : (term82 s y b) = (term160 s y b).
Proof. exact (@lem17265 (term19 s b) (real_le y b)). Qed.
Lemma lem5155163 (s : real -> Prop) (y : real) (b : real) : (term82 s y b) = (term161 s y b).
Proof. exact (TRANS (@lem5155162 s y b) (@lem5155161 s y b)). Qed.
Lemma lem5155164 (P : real -> Prop) : (term145 P) = (term146 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5155165 (s : real -> Prop) (y : real) : (term162 s y) = (term163 s y).
Proof. exact (@lem5155164 (term83 s y)). Qed.
Lemma lem5155166 (s : real -> Prop) (y : real) (b : real) : (term164 s y b) = (term82 s y b).
Proof. exact (eq_refl (term164 s y b)). Qed.
Lemma lem5155167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5155168 (s : real -> Prop) (y : real) (b : real) : (term165 s y b) = (term157 s y b).
Proof. exact (MK_COMB (@lem5155167) (@lem5155166 s y b)). Qed.
Lemma lem5155169 (s : real -> Prop) (y : real) (b : real) : (term165 s y b) = (term156 s y b).
Proof. exact (TRANS (@lem5155168 s y b) (@lem5155158 s y b)). Qed.
Lemma lem5155170 (s : real -> Prop) (y : real) : (term166 s y) = (term167 s y).
Proof. exact (fun_ext (fun b : real => @lem5155169 s y b)). Qed.
Lemma lem5155171 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155172 (s : real -> Prop) (y : real) : (term163 s y) = (term168 s y).
Proof. exact (MK_COMB (@lem5155171) (@lem5155170 s y)). Qed.
Lemma lem5155173 (s : real -> Prop) (y : real) : (term162 s y) = (term168 s y).
Proof. exact (TRANS (@lem5155165 s y) (@lem5155172 s y)). Qed.
Lemma lem5155174 (s : real -> Prop) (y : real) : (term83 s y) = (term169 s y).
Proof. exact (fun_ext (fun b : real => @lem5155163 s y b)). Qed.
Lemma lem5155175 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155176 (s : real -> Prop) (y : real) : (term84 s y) = (term170 s y).
Proof. exact (MK_COMB (@lem5155175) (@lem5155174 s y)). Qed.
Lemma lem5155177 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155178 (s : real -> Prop) (y : real) : (term158 s y) = (term159 s y).
Proof. exact (MK_COMB (@lem5155177) (@lem5155121 s y)). Qed.
Lemma lem5155179 (s : real -> Prop) (y : real) : (term171 s y) = (term172 s y).
Proof. exact (MK_COMB (@lem5155178 s y) (@lem5155173 s y)). Qed.
Lemma lem5155180 (s : real -> Prop) (y : real) : (term173 s y) = (term171 s y).
Proof. exact (@lem17045 (term19 s y) (term84 s y)). Qed.
Lemma lem5155181 (s : real -> Prop) (y : real) : (term173 s y) = (term172 s y).
Proof. exact (TRANS (@lem5155180 s y) (@lem5155179 s y)). Qed.
Lemma lem5155182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5155183 (s : real -> Prop) (y : real) : (term85 s y) = (term154 s y).
Proof. exact (MK_COMB (@lem5155182) (@lem5155124 s y)). Qed.
Lemma lem5155184 (s : real -> Prop) (y : real) : (term56 s y) = (term174 s y).
Proof. exact (MK_COMB (@lem5155183 s y) (@lem5155176 s y)). Qed.
Lemma lem5155185 (y : real) (b : real) : (term175 y b) = (term175 y b).
Proof. exact (eq_refl (term175 y b)). Qed.
Lemma lem5155186 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5155187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5155188 (s : real -> Prop) (y : real) : (term176 s y) = (term177 s y).
Proof. exact (MK_COMB (@lem5155187) (@lem5155181 s y)). Qed.
Lemma lem5155189 (s : real -> Prop) (y : real) (b : real) : (term178 s y b) = (term179 s y b).
Proof. exact (MK_COMB (@lem5155188 s y) (@lem5155186 y b)). Qed.
Lemma lem5155190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5155191 (s : real -> Prop) (y : real) : (term180 s y) = (term181 s y).
Proof. exact (MK_COMB (@lem5155190) (@lem5155184 s y)). Qed.
Lemma lem5155192 (s : real -> Prop) (y : real) (b : real) : (term182 s y b) = (term183 s y b).
Proof. exact (MK_COMB (@lem5155191 s y) (@lem5155185 y b)). Qed.
Lemma lem5155193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155194 (s : real -> Prop) (y : real) (b : real) : (term184 s y b) = (term185 s y b).
Proof. exact (MK_COMB (@lem5155193) (@lem5155192 s y b)). Qed.
Lemma lem5155195 (s : real -> Prop) (y : real) (b : real) : (term186 s y b) = (term187 s y b).
Proof. exact (MK_COMB (@lem5155194 s y b) (@lem5155189 s y b)). Qed.
Lemma lem5155196 (s : real -> Prop) (y : real) (b : real) : (term188 s y b) = (term186 s y b).
Proof. exact (@lem17646 (term56 s y) (y = b)). Qed.
Lemma lem5155197 (s : real -> Prop) (y : real) (b : real) : (term188 s y b) = (term187 s y b).
Proof. exact (TRANS (@lem5155196 s y b) (@lem5155195 s y b)). Qed.
Lemma lem5155198 (P : real -> Prop) : (term145 P) = (term146 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5155199 (s : real -> Prop) (b : real) : (term62 s b) = (term189 s b).
Proof. exact (@lem5155198 (term60 s b)). Qed.
Lemma lem5155200 (s : real -> Prop) (y : real) (b : real) : (term190 s b y) = ((term56 s y) = (y = b)).
Proof. exact (eq_refl (term190 s b y)). Qed.
Lemma lem5155201 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5155202 (s : real -> Prop) (y : real) (b : real) : (term191 s b y) = (term188 s y b).
Proof. exact (MK_COMB (@lem5155201) (@lem5155200 s y b)). Qed.
Lemma lem5155203 (s : real -> Prop) (y : real) (b : real) : (term191 s b y) = (term187 s y b).
Proof. exact (TRANS (@lem5155202 s y b) (@lem5155197 s y b)). Qed.
Lemma lem5155204 (s : real -> Prop) (b : real) : (term192 s b) = (term193 s b).
Proof. exact (fun_ext (fun y : real => @lem5155203 s y b)). Qed.
Lemma lem5155205 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155206 (s : real -> Prop) (b : real) : (term189 s b) = (term194 s b).
Proof. exact (MK_COMB (@lem5155205) (@lem5155204 s b)). Qed.
Lemma lem5155207 (s : real -> Prop) (b : real) : (term62 s b) = (term194 s b).
Proof. exact (TRANS (@lem5155199 s b) (@lem5155206 s b)). Qed.
Lemma lem5155209 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term195 A P Q) = (term196 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5155210 (P : real -> Prop) (Q : real -> Prop) : (term197 P Q) = (term198 P Q).
Proof. exact (@lem5155209 real P Q). Qed.
Lemma lem5155211 (s : real -> Prop) (b : real) : (term199 s b) = (term200 s b).
Proof. exact (@lem5155210 (term201 s b) (term202 s b)). Qed.
Lemma lem5155212 (s : real -> Prop) (y : real) (b : real) : (term203 s b y) = (term183 s y b).
Proof. exact (eq_refl (term203 s b y)). Qed.
Lemma lem5155213 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155214 (s : real -> Prop) (y : real) (b : real) : (term204 s b y) = (term185 s y b).
Proof. exact (MK_COMB (@lem5155213) (@lem5155212 s y b)). Qed.
Lemma lem5155215 (s : real -> Prop) (y : real) (b : real) : (term205 s b y) = (term179 s y b).
Proof. exact (eq_refl (term205 s b y)). Qed.
Lemma lem5155216 (s : real -> Prop) (y : real) (b : real) : (term206 s b y) = (term187 s y b).
Proof. exact (MK_COMB (@lem5155214 s y b) (@lem5155215 s y b)). Qed.
Lemma lem5155217 (s : real -> Prop) (b : real) : (term207 s b) = (term193 s b).
Proof. exact (fun_ext (fun y : real => @lem5155216 s y b)). Qed.
Lemma lem5155218 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155219 (s : real -> Prop) (b : real) : (term199 s b) = (term194 s b).
Proof. exact (MK_COMB (@lem5155218) (@lem5155217 s b)). Qed.
Lemma lem5155220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155221 (s : real -> Prop) (b : real) : (term208 s b) = (term209 s b).
Proof. exact (MK_COMB (@lem5155220) (@lem5155219 s b)). Qed.
Lemma lem5155222 (s : real -> Prop) (y : real) (b : real) : (term203 s b y) = (term183 s y b).
Proof. exact (eq_refl (term203 s b y)). Qed.
Lemma lem5155223 (s : real -> Prop) (b : real) : (term210 s b) = (term201 s b).
Proof. exact (fun_ext (fun y : real => @lem5155222 s y b)). Qed.
Lemma lem5155224 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155225 (s : real -> Prop) (b : real) : (term211 s b) = (term212 s b).
Proof. exact (MK_COMB (@lem5155224) (@lem5155223 s b)). Qed.
Lemma lem5155226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155227 (s : real -> Prop) (b : real) : (term213 s b) = (term214 s b).
Proof. exact (MK_COMB (@lem5155226) (@lem5155225 s b)). Qed.
Lemma lem5155228 (s : real -> Prop) (y : real) (b : real) : (term205 s b y) = (term179 s y b).
Proof. exact (eq_refl (term205 s b y)). Qed.
Lemma lem5155229 (s : real -> Prop) (b : real) : (term215 s b) = (term202 s b).
Proof. exact (fun_ext (fun y : real => @lem5155228 s y b)). Qed.
Lemma lem5155230 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155231 (s : real -> Prop) (b : real) : (term216 s b) = (term217 s b).
Proof. exact (MK_COMB (@lem5155230) (@lem5155229 s b)). Qed.
Lemma lem5155232 (s : real -> Prop) (b : real) : (term200 s b) = (term218 s b).
Proof. exact (MK_COMB (@lem5155227 s b) (@lem5155231 s b)). Qed.
Lemma lem5155233 (s : real -> Prop) (b : real) : ((term199 s b) = (term200 s b)) = ((term194 s b) = (term218 s b)).
Proof. exact (MK_COMB (@lem5155221 s b) (@lem5155232 s b)). Qed.
Lemma lem5155234 (s : real -> Prop) (b : real) : (term194 s b) = (term218 s b).
Proof. exact (EQ_MP (@lem5155233 s b) (@lem5155211 s b)). Qed.
Lemma lem5155620 {A : Type'} (P : A -> Prop) (Q : Prop) : (term219 A P Q) = (term220 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5155621 (P : real -> Prop) (Q : Prop) : (term221 P Q) = (term222 P Q).
Proof. exact (@lem5155620 real P Q). Qed.
Lemma lem5155622 (s : real -> Prop) (y : real) (b : real) : (term223 s y b) = (term224 s y b).
Proof. exact (@lem5155621 (term152 s b) (real_le y b)). Qed.
Lemma lem5155623 (s : real -> Prop) (x : real) (b : real) : (term225 s b x) = (term144 s x b).
Proof. exact (eq_refl (term225 s b x)). Qed.
Lemma lem5155624 (s : real -> Prop) (b : real) : (term226 s b) = (term152 s b).
Proof. exact (fun_ext (fun x : real => @lem5155623 s x b)). Qed.
Lemma lem5155625 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155626 (s : real -> Prop) (b : real) : (term227 s b) = (term153 s b).
Proof. exact (MK_COMB (@lem5155625) (@lem5155624 s b)). Qed.
Lemma lem5155627 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155628 (s : real -> Prop) (b : real) : (term228 s b) = (term159 s b).
Proof. exact (MK_COMB (@lem5155627) (@lem5155626 s b)). Qed.
Lemma lem5155629 (y : real) (b : real) : (real_le y b) = (real_le y b).
Proof. exact (eq_refl (real_le y b)). Qed.
Lemma lem5155630 (s : real -> Prop) (y : real) (b : real) : (term223 s y b) = (term161 s y b).
Proof. exact (MK_COMB (@lem5155628 s b) (@lem5155629 y b)). Qed.
Lemma lem5155631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155632 (s : real -> Prop) (y : real) (b : real) : (term229 s y b) = (term230 s y b).
Proof. exact (MK_COMB (@lem5155631) (@lem5155630 s y b)). Qed.
Lemma lem5155633 (s : real -> Prop) (x : real) (b : real) : (term225 s b x) = (term144 s x b).
Proof. exact (eq_refl (term225 s b x)). Qed.
Lemma lem5155634 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155635 (s : real -> Prop) (x : real) (b : real) : (term231 s b x) = (term232 s x b).
Proof. exact (MK_COMB (@lem5155634) (@lem5155633 s x b)). Qed.
Lemma lem5155636 (y : real) (b : real) : (real_le y b) = (real_le y b).
Proof. exact (eq_refl (real_le y b)). Qed.
Lemma lem5155637 (s : real -> Prop) (x : real) (y : real) (b : real) : (term233 s x y b) = (term234 s x y b).
Proof. exact (MK_COMB (@lem5155635 s x b) (@lem5155636 y b)). Qed.
Lemma lem5155638 (s : real -> Prop) (y : real) (b : real) : (term235 s y b) = (term236 s y b).
Proof. exact (fun_ext (fun x : real => @lem5155637 s x y b)). Qed.
Lemma lem5155639 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155640 (s : real -> Prop) (y : real) (b : real) : (term224 s y b) = (term237 s y b).
Proof. exact (MK_COMB (@lem5155639) (@lem5155638 s y b)). Qed.
Lemma lem5155641 (s : real -> Prop) (y : real) (b : real) : ((term223 s y b) = (term224 s y b)) = ((term161 s y b) = (term237 s y b)).
Proof. exact (MK_COMB (@lem5155632 s y b) (@lem5155640 s y b)). Qed.
Lemma lem5155642 (s : real -> Prop) (y : real) (b : real) : (term161 s y b) = (term237 s y b).
Proof. exact (EQ_MP (@lem5155641 s y b) (@lem5155622 s y b)). Qed.
Lemma lem5155643 (s : real -> Prop) (y : real) : (term169 s y) = (term238 s y).
Proof. exact (fun_ext (fun b : real => @lem5155642 s y b)). Qed.
Lemma lem5155644 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155645 (s : real -> Prop) (y : real) : (term170 s y) = (term239 s y).
Proof. exact (MK_COMB (@lem5155644) (@lem5155643 s y)). Qed.
Lemma lem5155647 {A B : Type'} (P : type1413 A B) : (term118 A B P) = (term119 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5155648 (P : type1626) : (term120 P) = (term121 P).
Proof. exact (@lem5155647 real real P). Qed.
Lemma lem5155649 (s : real -> Prop) (y : real) : (term240 s y) = (term241 s y).
Proof. exact (@lem5155648 (term242 s y)). Qed.
Lemma lem5155650 (s : real -> Prop) (y : real) (b : real) : (term243 s y b) = (term236 s y b).
Proof. exact (eq_refl (term243 s y b)). Qed.
Lemma lem5155651 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5155652 (s : real -> Prop) (y : real) (b : real) (x : real) : (term244 s y b x) = (term245 s y b x).
Proof. exact (MK_COMB (@lem5155650 s y b) (@lem5155651 x)). Qed.
Lemma lem5155653 (s : real -> Prop) (x : real) (y : real) (b : real) : (term245 s y b x) = (term234 s x y b).
Proof. exact (eq_refl (term245 s y b x)). Qed.
Lemma lem5155654 (s : real -> Prop) (x : real) (y : real) (b : real) : (term244 s y b x) = (term234 s x y b).
Proof. exact (TRANS (@lem5155652 s y b x) (@lem5155653 s x y b)). Qed.
Lemma lem5155655 (s : real -> Prop) (y : real) (b : real) : (term246 s y b) = (term236 s y b).
Proof. exact (fun_ext (fun x : real => @lem5155654 s x y b)). Qed.
Lemma lem5155656 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155657 (s : real -> Prop) (y : real) (b : real) : (term247 s y b) = (term237 s y b).
Proof. exact (MK_COMB (@lem5155656) (@lem5155655 s y b)). Qed.
Lemma lem5155658 (s : real -> Prop) (y : real) : (term248 s y) = (term238 s y).
Proof. exact (fun_ext (fun b : real => @lem5155657 s y b)). Qed.
Lemma lem5155659 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155660 (s : real -> Prop) (y : real) : (term240 s y) = (term239 s y).
Proof. exact (MK_COMB (@lem5155659) (@lem5155658 s y)). Qed.
Lemma lem5155661 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155662 (s : real -> Prop) (y : real) : (term249 s y) = (term250 s y).
Proof. exact (MK_COMB (@lem5155661) (@lem5155660 s y)). Qed.
Lemma lem5155663 (s : real -> Prop) (y : real) (b : real) : (term243 s y b) = (term236 s y b).
Proof. exact (eq_refl (term243 s y b)). Qed.
Lemma lem5155664 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5155665 (s : real -> Prop) (y : real) (x : real -> real) (b : real) : (term251 s y x b) = (term252 s y x b).
Proof. exact (MK_COMB (@lem5155663 s y b) (@lem5155664 x b)). Qed.
Lemma lem5155666 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term252 s y x b) = (term253 s x y b).
Proof. exact (eq_refl (term252 s y x b)). Qed.
Lemma lem5155667 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term251 s y x b) = (term253 s x y b).
Proof. exact (TRANS (@lem5155665 s y x b) (@lem5155666 s x y b)). Qed.
Lemma lem5155668 (s : real -> Prop) (x : real -> real) (y : real) : (term254 s y x) = (term255 s x y).
Proof. exact (fun_ext (fun b : real => @lem5155667 s x y b)). Qed.
Lemma lem5155669 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155670 (s : real -> Prop) (x : real -> real) (y : real) : (term256 s y x) = (term257 s x y).
Proof. exact (MK_COMB (@lem5155669) (@lem5155668 s x y)). Qed.
Lemma lem5155671 (s : real -> Prop) (y : real) : (term258 s y) = (term259 s y).
Proof. exact (fun_ext (fun x : real -> real => @lem5155670 s x y)). Qed.
Lemma lem5155672 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5155673 (s : real -> Prop) (y : real) : (term241 s y) = (term260 s y).
Proof. exact (MK_COMB (@lem5155672) (@lem5155671 s y)). Qed.
Lemma lem5155674 (s : real -> Prop) (y : real) : ((term240 s y) = (term241 s y)) = ((term239 s y) = (term260 s y)).
Proof. exact (MK_COMB (@lem5155662 s y) (@lem5155673 s y)). Qed.
Lemma lem5155675 (s : real -> Prop) (y : real) : (term239 s y) = (term260 s y).
Proof. exact (EQ_MP (@lem5155674 s y) (@lem5155649 s y)). Qed.
Lemma lem5155676 (s : real -> Prop) (y : real) : (term170 s y) = (term260 s y).
Proof. exact (TRANS (@lem5155645 s y) (@lem5155675 s y)). Qed.
Lemma lem5155677 (s : real -> Prop) (y : real) : (term154 s y) = (term154 s y).
Proof. exact (eq_refl (term154 s y)). Qed.
Lemma lem5155678 (s : real -> Prop) (y : real) : (term174 s y) = (term261 s y).
Proof. exact (MK_COMB (@lem5155677 s y) (@lem5155676 s y)). Qed.
Lemma lem5155680 {A : Type'} (P : Prop) (Q : A -> Prop) : (term262 A P Q) = (term263 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5155681 (P : Prop) (Q : type1028) : (term264 P Q) = (term265 P Q).
Proof. exact (@lem5155680 (real -> real) P Q). Qed.
Lemma lem5155682 (s : real -> Prop) (y : real) : (term266 s y) = (term267 s y).
Proof. exact (@lem5155681 (term94 s y) (term259 s y)). Qed.
Lemma lem5155683 (s : real -> Prop) (x : real -> real) (y : real) : (term268 s y x) = (term257 s x y).
Proof. exact (eq_refl (term268 s y x)). Qed.
Lemma lem5155684 (s : real -> Prop) (y : real) : (term269 s y) = (term259 s y).
Proof. exact (fun_ext (fun x : real -> real => @lem5155683 s x y)). Qed.
Lemma lem5155685 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5155686 (s : real -> Prop) (y : real) : (term270 s y) = (term260 s y).
Proof. exact (MK_COMB (@lem5155685) (@lem5155684 s y)). Qed.
Lemma lem5155687 (s : real -> Prop) (y : real) : (term154 s y) = (term154 s y).
Proof. exact (eq_refl (term154 s y)). Qed.
Lemma lem5155688 (s : real -> Prop) (y : real) : (term266 s y) = (term261 s y).
Proof. exact (MK_COMB (@lem5155687 s y) (@lem5155686 s y)). Qed.
Lemma lem5155689 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155690 (s : real -> Prop) (y : real) : (term271 s y) = (term272 s y).
Proof. exact (MK_COMB (@lem5155689) (@lem5155688 s y)). Qed.
Lemma lem5155691 (s : real -> Prop) (x : real -> real) (y : real) : (term268 s y x) = (term257 s x y).
Proof. exact (eq_refl (term268 s y x)). Qed.
Lemma lem5155692 (s : real -> Prop) (y : real) : (term154 s y) = (term154 s y).
Proof. exact (eq_refl (term154 s y)). Qed.
Lemma lem5155693 (s : real -> Prop) (x : real -> real) (y : real) : (term273 s y x) = (term274 s x y).
Proof. exact (MK_COMB (@lem5155692 s y) (@lem5155691 s x y)). Qed.
Lemma lem5155694 (s : real -> Prop) (y : real) : (term275 s y) = (term276 s y).
Proof. exact (fun_ext (fun x : real -> real => @lem5155693 s x y)). Qed.
Lemma lem5155695 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5155696 (s : real -> Prop) (y : real) : (term267 s y) = (term277 s y).
Proof. exact (MK_COMB (@lem5155695) (@lem5155694 s y)). Qed.
Lemma lem5155697 (s : real -> Prop) (y : real) : ((term266 s y) = (term267 s y)) = ((term261 s y) = (term277 s y)).
Proof. exact (MK_COMB (@lem5155690 s y) (@lem5155696 s y)). Qed.
Lemma lem5155698 (s : real -> Prop) (y : real) : (term261 s y) = (term277 s y).
Proof. exact (EQ_MP (@lem5155697 s y) (@lem5155682 s y)). Qed.
Lemma lem5155699 (s : real -> Prop) (y : real) : (term174 s y) = (term277 s y).
Proof. exact (TRANS (@lem5155678 s y) (@lem5155698 s y)). Qed.
Lemma lem5155700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5155701 (s : real -> Prop) (y : real) : (term181 s y) = (term278 s y).
Proof. exact (MK_COMB (@lem5155700) (@lem5155699 s y)). Qed.
Lemma lem5155702 (y : real) (b : real) : (term175 y b) = (term175 y b).
Proof. exact (eq_refl (term175 y b)). Qed.
Lemma lem5155703 (s : real -> Prop) (y : real) (b : real) : (term183 s y b) = (term279 s y b).
Proof. exact (MK_COMB (@lem5155701 s y) (@lem5155702 y b)). Qed.
Lemma lem5155705 {A : Type'} (P : A -> Prop) (Q : Prop) : (term280 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5155706 (P : type1028) (Q : Prop) : (term282 P Q) = (term283 P Q).
Proof. exact (@lem5155705 (real -> real) P Q). Qed.
Lemma lem5155707 (s : real -> Prop) (y : real) (b : real) : (term284 s y b) = (term285 s y b).
Proof. exact (@lem5155706 (term276 s y) (term175 y b)). Qed.
Lemma lem5155708 (s : real -> Prop) (x : real -> real) (y : real) : (term286 s y x) = (term274 s x y).
Proof. exact (eq_refl (term286 s y x)). Qed.
Lemma lem5155709 (s : real -> Prop) (y : real) : (term287 s y) = (term276 s y).
Proof. exact (fun_ext (fun x : real -> real => @lem5155708 s x y)). Qed.
Lemma lem5155710 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5155711 (s : real -> Prop) (y : real) : (term288 s y) = (term277 s y).
Proof. exact (MK_COMB (@lem5155710) (@lem5155709 s y)). Qed.
Lemma lem5155712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5155713 (s : real -> Prop) (y : real) : (term289 s y) = (term278 s y).
Proof. exact (MK_COMB (@lem5155712) (@lem5155711 s y)). Qed.
Lemma lem5155714 (y : real) (b : real) : (term175 y b) = (term175 y b).
Proof. exact (eq_refl (term175 y b)). Qed.
Lemma lem5155715 (s : real -> Prop) (y : real) (b : real) : (term284 s y b) = (term279 s y b).
Proof. exact (MK_COMB (@lem5155713 s y) (@lem5155714 y b)). Qed.
Lemma lem5155716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155717 (s : real -> Prop) (y : real) (b : real) : (term290 s y b) = (term291 s y b).
Proof. exact (MK_COMB (@lem5155716) (@lem5155715 s y b)). Qed.
Lemma lem5155718 (s : real -> Prop) (x : real -> real) (y : real) : (term286 s y x) = (term274 s x y).
Proof. exact (eq_refl (term286 s y x)). Qed.
Lemma lem5155719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5155720 (s : real -> Prop) (x : real -> real) (y : real) : (term292 s y x) = (term293 s x y).
Proof. exact (MK_COMB (@lem5155719) (@lem5155718 s x y)). Qed.
Lemma lem5155721 (y : real) (b : real) : (term175 y b) = (term175 y b).
Proof. exact (eq_refl (term175 y b)). Qed.
Lemma lem5155722 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term294 s x y b) = (term295 s x y b).
Proof. exact (MK_COMB (@lem5155720 s x y) (@lem5155721 y b)). Qed.
Lemma lem5155723 (s : real -> Prop) (y : real) (b : real) : (term296 s y b) = (term297 s y b).
Proof. exact (fun_ext (fun x : real -> real => @lem5155722 s x y b)). Qed.
Lemma lem5155724 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5155725 (s : real -> Prop) (y : real) (b : real) : (term285 s y b) = (term298 s y b).
Proof. exact (MK_COMB (@lem5155724) (@lem5155723 s y b)). Qed.
Lemma lem5155726 (s : real -> Prop) (y : real) (b : real) : ((term284 s y b) = (term285 s y b)) = ((term279 s y b) = (term298 s y b)).
Proof. exact (MK_COMB (@lem5155717 s y b) (@lem5155725 s y b)). Qed.
Lemma lem5155727 (s : real -> Prop) (y : real) (b : real) : (term279 s y b) = (term298 s y b).
Proof. exact (EQ_MP (@lem5155726 s y b) (@lem5155707 s y b)). Qed.
Lemma lem5155728 (s : real -> Prop) (y : real) (b : real) : (term183 s y b) = (term298 s y b).
Proof. exact (TRANS (@lem5155703 s y b) (@lem5155727 s y b)). Qed.
Lemma lem5155729 (s : real -> Prop) (b : real) : (term201 s b) = (term299 s b).
Proof. exact (fun_ext (fun y : real => @lem5155728 s y b)). Qed.
Lemma lem5155730 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155731 (s : real -> Prop) (b : real) : (term212 s b) = (term300 s b).
Proof. exact (MK_COMB (@lem5155730) (@lem5155729 s b)). Qed.
Lemma lem5155732 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155733 (s : real -> Prop) (b : real) : (term214 s b) = (term301 s b).
Proof. exact (MK_COMB (@lem5155732) (@lem5155731 s b)). Qed.
Lemma lem5155735 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term196 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5155736 (P : real -> Prop) (Q : real -> Prop) : (term198 P Q) = (term197 P Q).
Proof. exact (@lem5155735 real P Q). Qed.
Lemma lem5155737 (s : real -> Prop) (y : real) : (term302 s y) = (term303 s y).
Proof. exact (@lem5155736 (term152 s y) (term167 s y)). Qed.
Lemma lem5155738 (s : real -> Prop) (b : real) (y : real) : (term225 s y b) = (term144 s b y).
Proof. exact (eq_refl (term225 s y b)). Qed.
Lemma lem5155739 (s : real -> Prop) (y : real) : (term226 s y) = (term152 s y).
Proof. exact (fun_ext (fun b : real => @lem5155738 s b y)). Qed.
Lemma lem5155740 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155741 (s : real -> Prop) (y : real) : (term227 s y) = (term153 s y).
Proof. exact (MK_COMB (@lem5155740) (@lem5155739 s y)). Qed.
Lemma lem5155742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155743 (s : real -> Prop) (y : real) : (term228 s y) = (term159 s y).
Proof. exact (MK_COMB (@lem5155742) (@lem5155741 s y)). Qed.
Lemma lem5155744 (s : real -> Prop) (y : real) (b : real) : (term304 s y b) = (term156 s y b).
Proof. exact (eq_refl (term304 s y b)). Qed.
Lemma lem5155745 (s : real -> Prop) (y : real) : (term305 s y) = (term167 s y).
Proof. exact (fun_ext (fun b : real => @lem5155744 s y b)). Qed.
Lemma lem5155746 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155747 (s : real -> Prop) (y : real) : (term306 s y) = (term168 s y).
Proof. exact (MK_COMB (@lem5155746) (@lem5155745 s y)). Qed.
Lemma lem5155748 (s : real -> Prop) (y : real) : (term302 s y) = (term172 s y).
Proof. exact (MK_COMB (@lem5155743 s y) (@lem5155747 s y)). Qed.
Lemma lem5155749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155750 (s : real -> Prop) (y : real) : (term307 s y) = (term308 s y).
Proof. exact (MK_COMB (@lem5155749) (@lem5155748 s y)). Qed.
Lemma lem5155751 (s : real -> Prop) (b : real) (y : real) : (term225 s y b) = (term144 s b y).
Proof. exact (eq_refl (term225 s y b)). Qed.
Lemma lem5155752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155753 (s : real -> Prop) (b : real) (y : real) : (term231 s y b) = (term232 s b y).
Proof. exact (MK_COMB (@lem5155752) (@lem5155751 s b y)). Qed.
Lemma lem5155754 (s : real -> Prop) (y : real) (b : real) : (term304 s y b) = (term156 s y b).
Proof. exact (eq_refl (term304 s y b)). Qed.
Lemma lem5155755 (s : real -> Prop) (y : real) (b : real) : (term309 s y b) = (term310 s y b).
Proof. exact (MK_COMB (@lem5155753 s b y) (@lem5155754 s y b)). Qed.
Lemma lem5155756 (s : real -> Prop) (y : real) : (term311 s y) = (term312 s y).
Proof. exact (fun_ext (fun b : real => @lem5155755 s y b)). Qed.
Lemma lem5155757 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155758 (s : real -> Prop) (y : real) : (term303 s y) = (term313 s y).
Proof. exact (MK_COMB (@lem5155757) (@lem5155756 s y)). Qed.
Lemma lem5155759 (s : real -> Prop) (y : real) : ((term302 s y) = (term303 s y)) = ((term172 s y) = (term313 s y)).
Proof. exact (MK_COMB (@lem5155750 s y) (@lem5155758 s y)). Qed.
Lemma lem5155760 (s : real -> Prop) (y : real) : (term172 s y) = (term313 s y).
Proof. exact (EQ_MP (@lem5155759 s y) (@lem5155737 s y)). Qed.
Lemma lem5155763 (s : real -> Prop) (y : real) : (term314 s y) = (term314 s y).
Proof. exact (eq_refl (term314 s y)). Qed.
Lemma lem5155764 (s : real -> Prop) (y : real) : (term314 s y) = ((term172 s y) = (term313 s y)).
Proof. exact (eq_refl (term314 s y)). Qed.
Lemma lem5155765 (s : real -> Prop) (y : real) : (term315 s y) = (term315 s y).
Proof. exact (eq_refl (term315 s y)). Qed.
Lemma lem5155766 (s : real -> Prop) (y : real) : ((term314 s y) = (term314 s y)) = ((term314 s y) = ((term172 s y) = (term313 s y))).
Proof. exact (MK_COMB (@lem5155765 s y) (@lem5155764 s y)). Qed.
Lemma lem5155767 (s : real -> Prop) (y : real) : (term314 s y) = ((term172 s y) = (term313 s y)).
Proof. exact (eq_refl (term314 s y)). Qed.
Lemma lem5155768 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155769 (s : real -> Prop) (y : real) : (term315 s y) = (term316 s y).
Proof. exact (MK_COMB (@lem5155768) (@lem5155767 s y)). Qed.
Lemma lem5155770 (s : real -> Prop) (y : real) : ((term172 s y) = (term313 s y)) = ((term172 s y) = (term313 s y)).
Proof. exact (eq_refl ((term172 s y) = (term313 s y))). Qed.
Lemma lem5155771 (s : real -> Prop) (y : real) : ((term314 s y) = ((term172 s y) = (term313 s y))) = (((term172 s y) = (term313 s y)) = ((term172 s y) = (term313 s y))).
Proof. exact (MK_COMB (@lem5155769 s y) (@lem5155770 s y)). Qed.
Lemma lem5155772 (s : real -> Prop) (y : real) : ((term314 s y) = (term314 s y)) = (((term172 s y) = (term313 s y)) = ((term172 s y) = (term313 s y))).
Proof. exact (TRANS (@lem5155766 s y) (@lem5155771 s y)). Qed.
Lemma lem5155773 (s : real -> Prop) (y : real) : ((term172 s y) = (term313 s y)) = ((term172 s y) = (term313 s y)).
Proof. exact (EQ_MP (@lem5155772 s y) (@lem5155763 s y)). Qed.
Lemma lem5155774 (s : real -> Prop) (y : real) : (term172 s y) = (term313 s y).
Proof. exact (EQ_MP (@lem5155773 s y) (@lem5155760 s y)). Qed.
Lemma lem5155775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5155776 (s : real -> Prop) (y : real) : (term177 s y) = (term317 s y).
Proof. exact (MK_COMB (@lem5155775) (@lem5155774 s y)). Qed.
Lemma lem5155777 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5155778 (s : real -> Prop) (y : real) (b : real) : (term179 s y b) = (term318 s y b).
Proof. exact (MK_COMB (@lem5155776 s y) (@lem5155777 y b)). Qed.
Lemma lem5155780 {A : Type'} (P : A -> Prop) (Q : Prop) : (term280 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5155781 (P : real -> Prop) (Q : Prop) : (term319 P Q) = (term320 P Q).
Proof. exact (@lem5155780 real P Q). Qed.
Lemma lem5155782 (s : real -> Prop) (y : real) (b : real) : (term321 s y b) = (term322 s y b).
Proof. exact (@lem5155781 (term312 s y) (y = b)). Qed.
Lemma lem5155783 (s : real -> Prop) (y : real) (b : real) : (term323 s y b) = (term310 s y b).
Proof. exact (eq_refl (term323 s y b)). Qed.
Lemma lem5155784 (s : real -> Prop) (y : real) : (term324 s y) = (term312 s y).
Proof. exact (fun_ext (fun b : real => @lem5155783 s y b)). Qed.
Lemma lem5155785 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155786 (s : real -> Prop) (y : real) : (term325 s y) = (term313 s y).
Proof. exact (MK_COMB (@lem5155785) (@lem5155784 s y)). Qed.
Lemma lem5155787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5155788 (s : real -> Prop) (y : real) : (term326 s y) = (term317 s y).
Proof. exact (MK_COMB (@lem5155787) (@lem5155786 s y)). Qed.
Lemma lem5155789 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5155790 (s : real -> Prop) (y : real) (b : real) : (term321 s y b) = (term318 s y b).
Proof. exact (MK_COMB (@lem5155788 s y) (@lem5155789 y b)). Qed.
Lemma lem5155791 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155792 (s : real -> Prop) (y : real) (b : real) : (term327 s y b) = (term328 s y b).
Proof. exact (MK_COMB (@lem5155791) (@lem5155790 s y b)). Qed.
Lemma lem5155793 (s : real -> Prop) (y : real) (b' : real) : (term323 s y b') = (term310 s y b').
Proof. exact (eq_refl (term323 s y b')). Qed.
Lemma lem5155794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5155795 (s : real -> Prop) (y : real) (b' : real) : (term329 s y b') = (term330 s y b').
Proof. exact (MK_COMB (@lem5155794) (@lem5155793 s y b')). Qed.
Lemma lem5155796 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5155797 (s : real -> Prop) (b' : real) (y : real) (b : real) : (term331 s b' y b) = (term332 s b' y b).
Proof. exact (MK_COMB (@lem5155795 s y b') (@lem5155796 y b)). Qed.
Lemma lem5155798 (s : real -> Prop) (y : real) (b : real) : (term333 s y b) = (term334 s y b).
Proof. exact (fun_ext (fun b' : real => @lem5155797 s b' y b)). Qed.
Lemma lem5155799 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155800 (s : real -> Prop) (y : real) (b : real) : (term322 s y b) = (term335 s y b).
Proof. exact (MK_COMB (@lem5155799) (@lem5155798 s y b)). Qed.
Lemma lem5155801 (s : real -> Prop) (y : real) (b : real) : ((term321 s y b) = (term322 s y b)) = ((term318 s y b) = (term335 s y b)).
Proof. exact (MK_COMB (@lem5155792 s y b) (@lem5155800 s y b)). Qed.
Lemma lem5155802 (s : real -> Prop) (y : real) (b : real) : (term318 s y b) = (term335 s y b).
Proof. exact (EQ_MP (@lem5155801 s y b) (@lem5155782 s y b)). Qed.
Lemma lem5155803 (s : real -> Prop) (y : real) (b : real) : (term179 s y b) = (term335 s y b).
Proof. exact (TRANS (@lem5155778 s y b) (@lem5155802 s y b)). Qed.
Lemma lem5155804 (s : real -> Prop) (b : real) : (term202 s b) = (term336 s b).
Proof. exact (fun_ext (fun y : real => @lem5155803 s y b)). Qed.
Lemma lem5155805 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155806 (s : real -> Prop) (b : real) : (term217 s b) = (term337 s b).
Proof. exact (MK_COMB (@lem5155805) (@lem5155804 s b)). Qed.
Lemma lem5155807 (s : real -> Prop) (b : real) : (term218 s b) = (term338 s b).
Proof. exact (MK_COMB (@lem5155733 s b) (@lem5155806 s b)). Qed.
Lemma lem5155809 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term196 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5155810 (P : real -> Prop) (Q : real -> Prop) : (term198 P Q) = (term197 P Q).
Proof. exact (@lem5155809 real P Q). Qed.
Lemma lem5155811 (s : real -> Prop) (b : real) : (term339 s b) = (term340 s b).
Proof. exact (@lem5155810 (term299 s b) (term336 s b)). Qed.
Lemma lem5155812 (s : real -> Prop) (y : real) (b : real) : (term341 s b y) = (term298 s y b).
Proof. exact (eq_refl (term341 s b y)). Qed.
Lemma lem5155813 (s : real -> Prop) (b : real) : (term342 s b) = (term299 s b).
Proof. exact (fun_ext (fun y : real => @lem5155812 s y b)). Qed.
Lemma lem5155814 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155815 (s : real -> Prop) (b : real) : (term343 s b) = (term300 s b).
Proof. exact (MK_COMB (@lem5155814) (@lem5155813 s b)). Qed.
Lemma lem5155816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155817 (s : real -> Prop) (b : real) : (term344 s b) = (term301 s b).
Proof. exact (MK_COMB (@lem5155816) (@lem5155815 s b)). Qed.
Lemma lem5155818 (s : real -> Prop) (y : real) (b : real) : (term345 s b y) = (term335 s y b).
Proof. exact (eq_refl (term345 s b y)). Qed.
Lemma lem5155819 (s : real -> Prop) (b : real) : (term346 s b) = (term336 s b).
Proof. exact (fun_ext (fun y : real => @lem5155818 s y b)). Qed.
Lemma lem5155820 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155821 (s : real -> Prop) (b : real) : (term347 s b) = (term337 s b).
Proof. exact (MK_COMB (@lem5155820) (@lem5155819 s b)). Qed.
Lemma lem5155822 (s : real -> Prop) (b : real) : (term339 s b) = (term338 s b).
Proof. exact (MK_COMB (@lem5155817 s b) (@lem5155821 s b)). Qed.
Lemma lem5155823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155824 (s : real -> Prop) (b : real) : (term348 s b) = (term349 s b).
Proof. exact (MK_COMB (@lem5155823) (@lem5155822 s b)). Qed.
Lemma lem5155825 (s : real -> Prop) (y : real) (b : real) : (term341 s b y) = (term298 s y b).
Proof. exact (eq_refl (term341 s b y)). Qed.
Lemma lem5155826 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155827 (s : real -> Prop) (y : real) (b : real) : (term350 s b y) = (term351 s y b).
Proof. exact (MK_COMB (@lem5155826) (@lem5155825 s y b)). Qed.
Lemma lem5155828 (s : real -> Prop) (y : real) (b : real) : (term345 s b y) = (term335 s y b).
Proof. exact (eq_refl (term345 s b y)). Qed.
Lemma lem5155829 (s : real -> Prop) (y : real) (b : real) : (term352 s b y) = (term353 s y b).
Proof. exact (MK_COMB (@lem5155827 s y b) (@lem5155828 s y b)). Qed.
Lemma lem5155830 (s : real -> Prop) (b : real) : (term354 s b) = (term355 s b).
Proof. exact (fun_ext (fun y : real => @lem5155829 s y b)). Qed.
Lemma lem5155831 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155832 (s : real -> Prop) (b : real) : (term340 s b) = (term356 s b).
Proof. exact (MK_COMB (@lem5155831) (@lem5155830 s b)). Qed.
Lemma lem5155833 (s : real -> Prop) (b : real) : ((term339 s b) = (term340 s b)) = ((term338 s b) = (term356 s b)).
Proof. exact (MK_COMB (@lem5155824 s b) (@lem5155832 s b)). Qed.
Lemma lem5155834 (s : real -> Prop) (b : real) : (term338 s b) = (term356 s b).
Proof. exact (EQ_MP (@lem5155833 s b) (@lem5155811 s b)). Qed.
Lemma lem5155838 {A : Type'} (P : A -> Prop) (Q : Prop) : (term219 A P Q) = (term220 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5155839 (P : type1028) (Q : Prop) : (term357 P Q) = (term358 P Q).
Proof. exact (@lem5155838 (real -> real) P Q). Qed.
Lemma lem5155840 (s : real -> Prop) (y : real) (b : real) : (term359 s y b) = (term360 s y b).
Proof. exact (@lem5155839 (term297 s y b) (term335 s y b)). Qed.
Lemma lem5155841 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term361 s y b x) = (term295 s x y b).
Proof. exact (eq_refl (term361 s y b x)). Qed.
Lemma lem5155842 (s : real -> Prop) (y : real) (b : real) : (term362 s y b) = (term297 s y b).
Proof. exact (fun_ext (fun x : real -> real => @lem5155841 s x y b)). Qed.
Lemma lem5155843 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5155844 (s : real -> Prop) (y : real) (b : real) : (term363 s y b) = (term298 s y b).
Proof. exact (MK_COMB (@lem5155843) (@lem5155842 s y b)). Qed.
Lemma lem5155845 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155846 (s : real -> Prop) (y : real) (b : real) : (term364 s y b) = (term351 s y b).
Proof. exact (MK_COMB (@lem5155845) (@lem5155844 s y b)). Qed.
Lemma lem5155847 (s : real -> Prop) (y : real) (b : real) : (term335 s y b) = (term335 s y b).
Proof. exact (eq_refl (term335 s y b)). Qed.
Lemma lem5155848 (s : real -> Prop) (y : real) (b : real) : (term359 s y b) = (term353 s y b).
Proof. exact (MK_COMB (@lem5155846 s y b) (@lem5155847 s y b)). Qed.
Lemma lem5155849 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155850 (s : real -> Prop) (y : real) (b : real) : (term365 s y b) = (term366 s y b).
Proof. exact (MK_COMB (@lem5155849) (@lem5155848 s y b)). Qed.
Lemma lem5155851 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term361 s y b x) = (term295 s x y b).
Proof. exact (eq_refl (term361 s y b x)). Qed.
Lemma lem5155852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155853 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term367 s y b x) = (term368 s x y b).
Proof. exact (MK_COMB (@lem5155852) (@lem5155851 s x y b)). Qed.
Lemma lem5155854 (s : real -> Prop) (y : real) (b : real) : (term335 s y b) = (term335 s y b).
Proof. exact (eq_refl (term335 s y b)). Qed.
Lemma lem5155855 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term369 x s y b) = (term370 x s y b).
Proof. exact (MK_COMB (@lem5155853 s x y b) (@lem5155854 s y b)). Qed.
Lemma lem5155856 (s : real -> Prop) (y : real) (b : real) : (term371 s y b) = (term372 s y b).
Proof. exact (fun_ext (fun x : real -> real => @lem5155855 x s y b)). Qed.
Lemma lem5155857 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5155858 (s : real -> Prop) (y : real) (b : real) : (term360 s y b) = (term373 s y b).
Proof. exact (MK_COMB (@lem5155857) (@lem5155856 s y b)). Qed.
Lemma lem5155859 (s : real -> Prop) (y : real) (b : real) : ((term359 s y b) = (term360 s y b)) = ((term353 s y b) = (term373 s y b)).
Proof. exact (MK_COMB (@lem5155850 s y b) (@lem5155858 s y b)). Qed.
Lemma lem5155860 (s : real -> Prop) (y : real) (b : real) : (term353 s y b) = (term373 s y b).
Proof. exact (EQ_MP (@lem5155859 s y b) (@lem5155840 s y b)). Qed.
Lemma lem5155862 {A : Type'} (P : Prop) (Q : A -> Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5155863 (P : Prop) (Q : real -> Prop) : (term101 P Q) = (term102 P Q).
Proof. exact (@lem5155862 real P Q). Qed.
Lemma lem5155864 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term374 x s y b) = (term375 x s y b).
Proof. exact (@lem5155863 (term295 s x y b) (term334 s y b)). Qed.
Lemma lem5155865 (s : real -> Prop) (b' : real) (y : real) (b : real) : (term376 s y b b') = (term332 s b' y b).
Proof. exact (eq_refl (term376 s y b b')). Qed.
Lemma lem5155866 (s : real -> Prop) (y : real) (b : real) : (term377 s y b) = (term334 s y b).
Proof. exact (fun_ext (fun b' : real => @lem5155865 s b' y b)). Qed.
Lemma lem5155867 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155868 (s : real -> Prop) (y : real) (b : real) : (term378 s y b) = (term335 s y b).
Proof. exact (MK_COMB (@lem5155867) (@lem5155866 s y b)). Qed.
Lemma lem5155869 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term368 s x y b) = (term368 s x y b).
Proof. exact (eq_refl (term368 s x y b)). Qed.
Lemma lem5155870 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term374 x s y b) = (term370 x s y b).
Proof. exact (MK_COMB (@lem5155869 s x y b) (@lem5155868 s y b)). Qed.
Lemma lem5155871 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155872 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term379 x s y b) = (term380 x s y b).
Proof. exact (MK_COMB (@lem5155871) (@lem5155870 x s y b)). Qed.
Lemma lem5155873 (s : real -> Prop) (b' : real) (y : real) (b : real) : (term376 s y b b') = (term332 s b' y b).
Proof. exact (eq_refl (term376 s y b b')). Qed.
Lemma lem5155874 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term368 s x y b) = (term368 s x y b).
Proof. exact (eq_refl (term368 s x y b)). Qed.
Lemma lem5155875 (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) : (term381 x s y b b') = (term382 x s b' y b).
Proof. exact (MK_COMB (@lem5155874 s x y b) (@lem5155873 s b' y b)). Qed.
Lemma lem5155876 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term383 x s y b) = (term384 x s y b).
Proof. exact (fun_ext (fun b' : real => @lem5155875 x s b' y b)). Qed.
Lemma lem5155877 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155878 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term375 x s y b) = (term385 x s y b).
Proof. exact (MK_COMB (@lem5155877) (@lem5155876 x s y b)). Qed.
Lemma lem5155879 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : ((term374 x s y b) = (term375 x s y b)) = ((term370 x s y b) = (term385 x s y b)).
Proof. exact (MK_COMB (@lem5155872 x s y b) (@lem5155878 x s y b)). Qed.
Lemma lem5155880 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term370 x s y b) = (term385 x s y b).
Proof. exact (EQ_MP (@lem5155879 x s y b) (@lem5155864 x s y b)). Qed.
Lemma lem5155881 (s : real -> Prop) (y : real) (b : real) : (term372 s y b) = (term386 s y b).
Proof. exact (fun_ext (fun x : real -> real => @lem5155880 x s y b)). Qed.
Lemma lem5155882 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5155883 (s : real -> Prop) (y : real) (b : real) : (term373 s y b) = (term387 s y b).
Proof. exact (MK_COMB (@lem5155882) (@lem5155881 s y b)). Qed.
Lemma lem5155884 (s : real -> Prop) (y : real) (b : real) : (term353 s y b) = (term387 s y b).
Proof. exact (TRANS (@lem5155860 s y b) (@lem5155883 s y b)). Qed.
Lemma lem5155885 (s : real -> Prop) (b : real) : (term355 s b) = (term388 s b).
Proof. exact (fun_ext (fun y : real => @lem5155884 s y b)). Qed.
Lemma lem5155886 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5155887 (s : real -> Prop) (b : real) : (term356 s b) = (term389 s b).
Proof. exact (MK_COMB (@lem5155886) (@lem5155885 s b)). Qed.
Lemma lem5155888 (s : real -> Prop) (b : real) : (term338 s b) = (term389 s b).
Proof. exact (TRANS (@lem5155834 s b) (@lem5155887 s b)). Qed.
Lemma lem5155889 (s : real -> Prop) (b : real) : (term218 s b) = (term389 s b).
Proof. exact (TRANS (@lem5155807 s b) (@lem5155888 s b)). Qed.
Lemma lem5155890 (s : real -> Prop) (b : real) : (term194 s b) = (term389 s b).
Proof. exact (TRANS (@lem5155234 s b) (@lem5155889 s b)). Qed.
Lemma lem5155891 (s : real -> Prop) (b : real) : (term62 s b) = (term389 s b).
Proof. exact (TRANS (@lem5155207 s b) (@lem5155890 s b)). Qed.
Lemma lem5155892 (s : real -> Prop) (b : real) (h1 : term62 s b) : term389 s b.
Proof. exact (EQ_MP (@lem5155891 s b) (@lem5154861 s b h1)). Qed.
Lemma lem5155901 (y : real) (x : real) : (term390 y x) = (term391 y x).
Proof. exact (@lem17045 (real_le x y) (real_le y x)). Qed.
Lemma lem5155906 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5155907 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5155908 (y : real) (x : real) : (term392 y x) = (term393 y x).
Proof. exact (MK_COMB (@lem5155907) (@lem5155901 y x)). Qed.
Lemma lem5155909 (x : real) (y : real) : (term394 x y) = (term395 x y).
Proof. exact (MK_COMB (@lem5155908 y x) (@lem5155906 x y)). Qed.
Lemma lem5155914 (x : real) (y : real) : (term396 x y) = (term396 x y).
Proof. exact (eq_refl (term396 x y)). Qed.
Lemma lem5155915 (x : real) (y : real) : (term397 x y) = (term398 x y).
Proof. exact (MK_COMB (@lem5155914 x y) (@lem5155909 x y)). Qed.
Lemma lem5155916 (x : real) (y : real) : ((term75 y x) = (x = y)) = (term397 x y).
Proof. exact (@lem17784 (term75 y x) (x = y)). Qed.
Lemma lem5155917 (x : real) (y : real) : ((term75 y x) = (x = y)) = (term398 x y).
Proof. exact (TRANS (@lem5155916 x y) (@lem5155915 x y)). Qed.
Lemma lem5155918 (x : real) : (term76 x) = (term399 x).
Proof. exact (fun_ext (fun y : real => @lem5155917 x y)). Qed.
Lemma lem5155919 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155920 (x : real) : (term77 x) = (term400 x).
Proof. exact (MK_COMB (@lem5155919) (@lem5155918 x)). Qed.
Lemma lem5155921 : term78 = term401.
Proof. exact (fun_ext (fun x : real => @lem5155920 x)). Qed.
Lemma lem5155922 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155923 : term79 = term402.
Proof. exact (MK_COMB (@lem5155922) (@lem5155921)). Qed.
Lemma lem5155929 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term403 A P Q) = (term404 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5155930 (P : real -> Prop) (Q : real -> Prop) : (term405 P Q) = (term406 P Q).
Proof. exact (@lem5155929 real P Q). Qed.
Lemma lem5155931 (x : real) : (term407 x) = (term408 x).
Proof. exact (@lem5155930 (term409 x) (term410 x)). Qed.
Lemma lem5155932 (x : real) (y : real) : (term411 x y) = (term412 x y).
Proof. exact (eq_refl (term411 x y)). Qed.
Lemma lem5155933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5155934 (x : real) (y : real) : (term413 x y) = (term396 x y).
Proof. exact (MK_COMB (@lem5155933) (@lem5155932 x y)). Qed.
Lemma lem5155935 (x : real) (y : real) : (term414 x y) = (term395 x y).
Proof. exact (eq_refl (term414 x y)). Qed.
Lemma lem5155936 (x : real) (y : real) : (term415 x y) = (term398 x y).
Proof. exact (MK_COMB (@lem5155934 x y) (@lem5155935 x y)). Qed.
Lemma lem5155937 (x : real) : (term416 x) = (term399 x).
Proof. exact (fun_ext (fun y : real => @lem5155936 x y)). Qed.
Lemma lem5155938 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155939 (x : real) : (term407 x) = (term400 x).
Proof. exact (MK_COMB (@lem5155938) (@lem5155937 x)). Qed.
Lemma lem5155940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5155941 (x : real) : (term417 x) = (term418 x).
Proof. exact (MK_COMB (@lem5155940) (@lem5155939 x)). Qed.
Lemma lem5155942 (x : real) (y : real) : (term411 x y) = (term412 x y).
Proof. exact (eq_refl (term411 x y)). Qed.
Lemma lem5155943 (x : real) : (term419 x) = (term409 x).
Proof. exact (fun_ext (fun y : real => @lem5155942 x y)). Qed.
Lemma lem5155944 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155945 (x : real) : (term420 x) = (term421 x).
Proof. exact (MK_COMB (@lem5155944) (@lem5155943 x)). Qed.
Lemma lem5155946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5155947 (x : real) : (term422 x) = (term423 x).
Proof. exact (MK_COMB (@lem5155946) (@lem5155945 x)). Qed.
Lemma lem5155948 (x : real) (y : real) : (term414 x y) = (term395 x y).
Proof. exact (eq_refl (term414 x y)). Qed.
Lemma lem5155949 (x : real) : (term424 x) = (term410 x).
Proof. exact (fun_ext (fun y : real => @lem5155948 x y)). Qed.
Lemma lem5155950 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5155951 (x : real) : (term425 x) = (term426 x).
Proof. exact (MK_COMB (@lem5155950) (@lem5155949 x)). Qed.
Lemma lem5155952 (x : real) : (term408 x) = (term427 x).
Proof. exact (MK_COMB (@lem5155947 x) (@lem5155951 x)). Qed.
Lemma lem5155953 (x : real) : ((term407 x) = (term408 x)) = ((term400 x) = (term427 x)).
Proof. exact (MK_COMB (@lem5155941 x) (@lem5155952 x)). Qed.
Lemma lem5155954 (x : real) : (term400 x) = (term427 x).
Proof. exact (EQ_MP (@lem5155953 x) (@lem5155931 x)). Qed.
Lemma lem5156051 : term401 = term428.
Proof. exact (fun_ext (fun x : real => @lem5155954 x)). Qed.
Lemma lem5156052 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156053 : term402 = term429.
Proof. exact (MK_COMB (@lem5156052) (@lem5156051)). Qed.
Lemma lem5156055 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term403 A P Q) = (term404 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5156056 (P : real -> Prop) (Q : real -> Prop) : (term405 P Q) = (term406 P Q).
Proof. exact (@lem5156055 real P Q). Qed.
Lemma lem5156057 : term430 = term431.
Proof. exact (@lem5156056 term432 term433). Qed.
Lemma lem5156058 (x : real) : (term434 x) = (term421 x).
Proof. exact (eq_refl (term434 x)). Qed.
Lemma lem5156059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5156060 (x : real) : (term435 x) = (term423 x).
Proof. exact (MK_COMB (@lem5156059) (@lem5156058 x)). Qed.
Lemma lem5156061 (x : real) : (term436 x) = (term426 x).
Proof. exact (eq_refl (term436 x)). Qed.
Lemma lem5156062 (x : real) : (term437 x) = (term427 x).
Proof. exact (MK_COMB (@lem5156060 x) (@lem5156061 x)). Qed.
Lemma lem5156063 : term438 = term428.
Proof. exact (fun_ext (fun x : real => @lem5156062 x)). Qed.
Lemma lem5156064 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156065 : term430 = term429.
Proof. exact (MK_COMB (@lem5156064) (@lem5156063)). Qed.
Lemma lem5156066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5156067 : term439 = term440.
Proof. exact (MK_COMB (@lem5156066) (@lem5156065)). Qed.
Lemma lem5156068 (x : real) : (term434 x) = (term421 x).
Proof. exact (eq_refl (term434 x)). Qed.
Lemma lem5156069 : term441 = term432.
Proof. exact (fun_ext (fun x : real => @lem5156068 x)). Qed.
Lemma lem5156070 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156071 : term442 = term443.
Proof. exact (MK_COMB (@lem5156070) (@lem5156069)). Qed.
Lemma lem5156072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5156073 : term444 = term445.
Proof. exact (MK_COMB (@lem5156072) (@lem5156071)). Qed.
Lemma lem5156074 (x : real) : (term436 x) = (term426 x).
Proof. exact (eq_refl (term436 x)). Qed.
Lemma lem5156075 : term446 = term433.
Proof. exact (fun_ext (fun x : real => @lem5156074 x)). Qed.
Lemma lem5156076 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156077 : term447 = term448.
Proof. exact (MK_COMB (@lem5156076) (@lem5156075)). Qed.
Lemma lem5156078 : term431 = term449.
Proof. exact (MK_COMB (@lem5156073) (@lem5156077)). Qed.
Lemma lem5156079 : (term430 = term431) = (term429 = term449).
Proof. exact (MK_COMB (@lem5156067) (@lem5156078)). Qed.
Lemma lem5156080 : term429 = term449.
Proof. exact (EQ_MP (@lem5156079) (@lem5156057)). Qed.
Lemma lem5156187 : term402 = term449.
Proof. exact (TRANS (@lem5156053) (@lem5156080)). Qed.
Lemma lem5156188 : term79 = term449.
Proof. exact (TRANS (@lem5155923) (@lem5156187)). Qed.
Lemma lem5156189 (h1 : term79) : term449.
Proof. exact (EQ_MP (@lem5156188) (@lem5154862 h1)). Qed.
Lemma lem5156193 (x : real) (y : real) : (term450 x y) = (real_le x y).
Proof. exact (@lem16933 (real_le x y)). Qed.
Lemma lem5156195 (y : real) (x : real) : (real_lt y x) = (real_lt y x).
Proof. exact (eq_refl (real_lt y x)). Qed.
Lemma lem5156196 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5156197 (x : real) (y : real) : (term451 x y) = (term452 x y).
Proof. exact (MK_COMB (@lem5156196) (@lem5156193 x y)). Qed.
Lemma lem5156198 (y : real) (x : real) : (term453 y x) = (term454 y x).
Proof. exact (MK_COMB (@lem5156197 x y) (@lem5156195 y x)). Qed.
Lemma lem5156203 (y : real) (x : real) : (term455 y x) = (term455 y x).
Proof. exact (eq_refl (term455 y x)). Qed.
Lemma lem5156204 (y : real) (x : real) : (term456 y x) = (term457 y x).
Proof. exact (MK_COMB (@lem5156203 y x) (@lem5156198 y x)). Qed.
Lemma lem5156205 (y : real) (x : real) : ((term71 x y) = (real_lt y x)) = (term456 y x).
Proof. exact (@lem17784 (term71 x y) (real_lt y x)). Qed.
Lemma lem5156206 (y : real) (x : real) : ((term71 x y) = (real_lt y x)) = (term457 y x).
Proof. exact (TRANS (@lem5156205 y x) (@lem5156204 y x)). Qed.
Lemma lem5156207 (x : real) : (term72 x) = (term458 x).
Proof. exact (fun_ext (fun y : real => @lem5156206 y x)). Qed.
Lemma lem5156208 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156209 (x : real) : (term73 x) = (term459 x).
Proof. exact (MK_COMB (@lem5156208) (@lem5156207 x)). Qed.
Lemma lem5156210 : term74 = term460.
Proof. exact (fun_ext (fun x : real => @lem5156209 x)). Qed.
Lemma lem5156211 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156212 : term35 = term461.
Proof. exact (MK_COMB (@lem5156211) (@lem5156210)). Qed.
Lemma lem5156218 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term403 A P Q) = (term404 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5156219 (P : real -> Prop) (Q : real -> Prop) : (term405 P Q) = (term406 P Q).
Proof. exact (@lem5156218 real P Q). Qed.
Lemma lem5156220 (x : real) : (term462 x) = (term463 x).
Proof. exact (@lem5156219 (term464 x) (term465 x)). Qed.
Lemma lem5156221 (y : real) (x : real) : (term466 x y) = (term467 y x).
Proof. exact (eq_refl (term466 x y)). Qed.
Lemma lem5156222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5156223 (y : real) (x : real) : (term468 x y) = (term455 y x).
Proof. exact (MK_COMB (@lem5156222) (@lem5156221 y x)). Qed.
Lemma lem5156224 (y : real) (x : real) : (term469 x y) = (term454 y x).
Proof. exact (eq_refl (term469 x y)). Qed.
Lemma lem5156225 (y : real) (x : real) : (term470 x y) = (term457 y x).
Proof. exact (MK_COMB (@lem5156223 y x) (@lem5156224 y x)). Qed.
Lemma lem5156226 (x : real) : (term471 x) = (term458 x).
Proof. exact (fun_ext (fun y : real => @lem5156225 y x)). Qed.
Lemma lem5156227 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156228 (x : real) : (term462 x) = (term459 x).
Proof. exact (MK_COMB (@lem5156227) (@lem5156226 x)). Qed.
Lemma lem5156229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5156230 (x : real) : (term472 x) = (term473 x).
Proof. exact (MK_COMB (@lem5156229) (@lem5156228 x)). Qed.
Lemma lem5156231 (y : real) (x : real) : (term466 x y) = (term467 y x).
Proof. exact (eq_refl (term466 x y)). Qed.
Lemma lem5156232 (x : real) : (term474 x) = (term464 x).
Proof. exact (fun_ext (fun y : real => @lem5156231 y x)). Qed.
Lemma lem5156233 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156234 (x : real) : (term475 x) = (term476 x).
Proof. exact (MK_COMB (@lem5156233) (@lem5156232 x)). Qed.
Lemma lem5156235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5156236 (x : real) : (term477 x) = (term478 x).
Proof. exact (MK_COMB (@lem5156235) (@lem5156234 x)). Qed.
Lemma lem5156237 (y : real) (x : real) : (term469 x y) = (term454 y x).
Proof. exact (eq_refl (term469 x y)). Qed.
Lemma lem5156238 (x : real) : (term479 x) = (term465 x).
Proof. exact (fun_ext (fun y : real => @lem5156237 y x)). Qed.
Lemma lem5156239 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156240 (x : real) : (term480 x) = (term481 x).
Proof. exact (MK_COMB (@lem5156239) (@lem5156238 x)). Qed.
Lemma lem5156241 (x : real) : (term463 x) = (term482 x).
Proof. exact (MK_COMB (@lem5156236 x) (@lem5156240 x)). Qed.
Lemma lem5156242 (x : real) : ((term462 x) = (term463 x)) = ((term459 x) = (term482 x)).
Proof. exact (MK_COMB (@lem5156230 x) (@lem5156241 x)). Qed.
Lemma lem5156243 (x : real) : (term459 x) = (term482 x).
Proof. exact (EQ_MP (@lem5156242 x) (@lem5156220 x)). Qed.
Lemma lem5156340 : term460 = term483.
Proof. exact (fun_ext (fun x : real => @lem5156243 x)). Qed.
Lemma lem5156341 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156342 : term461 = term484.
Proof. exact (MK_COMB (@lem5156341) (@lem5156340)). Qed.
Lemma lem5156344 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term403 A P Q) = (term404 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5156345 (P : real -> Prop) (Q : real -> Prop) : (term405 P Q) = (term406 P Q).
Proof. exact (@lem5156344 real P Q). Qed.
Lemma lem5156346 : term485 = term486.
Proof. exact (@lem5156345 term487 term488). Qed.
Lemma lem5156347 (x : real) : (term489 x) = (term476 x).
Proof. exact (eq_refl (term489 x)). Qed.
Lemma lem5156348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5156349 (x : real) : (term490 x) = (term478 x).
Proof. exact (MK_COMB (@lem5156348) (@lem5156347 x)). Qed.
Lemma lem5156350 (x : real) : (term491 x) = (term481 x).
Proof. exact (eq_refl (term491 x)). Qed.
Lemma lem5156351 (x : real) : (term492 x) = (term482 x).
Proof. exact (MK_COMB (@lem5156349 x) (@lem5156350 x)). Qed.
Lemma lem5156352 : term493 = term483.
Proof. exact (fun_ext (fun x : real => @lem5156351 x)). Qed.
Lemma lem5156353 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156354 : term485 = term484.
Proof. exact (MK_COMB (@lem5156353) (@lem5156352)). Qed.
Lemma lem5156355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5156356 : term494 = term495.
Proof. exact (MK_COMB (@lem5156355) (@lem5156354)). Qed.
Lemma lem5156357 (x : real) : (term489 x) = (term476 x).
Proof. exact (eq_refl (term489 x)). Qed.
Lemma lem5156358 : term496 = term487.
Proof. exact (fun_ext (fun x : real => @lem5156357 x)). Qed.
Lemma lem5156359 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156360 : term497 = term498.
Proof. exact (MK_COMB (@lem5156359) (@lem5156358)). Qed.
Lemma lem5156361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5156362 : term499 = term500.
Proof. exact (MK_COMB (@lem5156361) (@lem5156360)). Qed.
Lemma lem5156363 (x : real) : (term491 x) = (term481 x).
Proof. exact (eq_refl (term491 x)). Qed.
Lemma lem5156364 : term501 = term488.
Proof. exact (fun_ext (fun x : real => @lem5156363 x)). Qed.
Lemma lem5156365 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156366 : term502 = term503.
Proof. exact (MK_COMB (@lem5156365) (@lem5156364)). Qed.
Lemma lem5156367 : term486 = term504.
Proof. exact (MK_COMB (@lem5156362) (@lem5156366)). Qed.
Lemma lem5156368 : (term485 = term486) = (term484 = term504).
Proof. exact (MK_COMB (@lem5156356) (@lem5156367)). Qed.
Lemma lem5156369 : term484 = term504.
Proof. exact (EQ_MP (@lem5156368) (@lem5156346)). Qed.
Lemma lem5156476 : term461 = term504.
Proof. exact (TRANS (@lem5156342) (@lem5156369)). Qed.
Lemma lem5156477 : term35 = term504.
Proof. exact (TRANS (@lem5156212) (@lem5156476)). Qed.
Lemma lem5156478 (h1 : term35) : term504.
Proof. exact (EQ_MP (@lem5156477) (@lem5154863 h1)). Qed.
Lemma lem5156479 (s : real -> Prop) (y : real) (b : real) (h1 : term387 s y b) : term387 s y b.
Proof. exact (h1). Qed.
Lemma lem5156480 (x : real -> real) (s : real -> Prop) (y : real) (b : real) (h1 : term385 x s y b) : term385 x s y b.
Proof. exact (h1). Qed.
Lemma lem5156481 (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term382 x s b' y b) : term382 x s b' y b.
Proof. exact (h1). Qed.
Lemma lem5156482 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term139 b s x'.
Proof. exact (h1). Qed.
Lemma lem5156497 (s : real -> Prop) (x : real) (b : real) : (term92 s x b) = (term92 s x b).
Proof. exact (eq_refl (term92 s x b)). Qed.
Lemma lem5156498 (s : real -> Prop) (b : real) : (term93 s b) = (term93 s b).
Proof. exact (fun_ext (fun x : real => @lem5156497 s x b)). Qed.
Lemma lem5156499 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156500 (s : real -> Prop) (b : real) : (term94 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5156499) (@lem5156498 s b)). Qed.
Lemma lem5156501 (s : real -> Prop) (b : real) (h1 : term19 s b) : term94 s b.
Proof. exact (EQ_MP (@lem5156500 s b) (@lem5154926 s b h1)). Qed.
Lemma lem5156526 (x : real) (y : real) : (term395 x y) = (term395 x y).
Proof. exact (eq_refl (term395 x y)). Qed.
Lemma lem5156527 (x : real) : (term410 x) = (term410 x).
Proof. exact (fun_ext (fun y : real => @lem5156526 x y)). Qed.
Lemma lem5156528 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156529 (x : real) : (term426 x) = (term426 x).
Proof. exact (MK_COMB (@lem5156528) (@lem5156527 x)). Qed.
Lemma lem5156530 : term433 = term433.
Proof. exact (fun_ext (fun x : real => @lem5156529 x)). Qed.
Lemma lem5156531 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156532 : term448 = term448.
Proof. exact (MK_COMB (@lem5156531) (@lem5156530)). Qed.
Lemma lem5156555 (x : real) (y : real) : (term412 x y) = (term412 x y).
Proof. exact (eq_refl (term412 x y)). Qed.
Lemma lem5156556 (x : real) : (term409 x) = (term409 x).
Proof. exact (fun_ext (fun y : real => @lem5156555 x y)). Qed.
Lemma lem5156557 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156558 (x : real) : (term421 x) = (term421 x).
Proof. exact (MK_COMB (@lem5156557) (@lem5156556 x)). Qed.
Lemma lem5156559 : term432 = term432.
Proof. exact (fun_ext (fun x : real => @lem5156558 x)). Qed.
Lemma lem5156560 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156561 : term443 = term443.
Proof. exact (MK_COMB (@lem5156560) (@lem5156559)). Qed.
Lemma lem5156562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5156563 : term445 = term445.
Proof. exact (MK_COMB (@lem5156562) (@lem5156561)). Qed.
Lemma lem5156564 : term449 = term449.
Proof. exact (MK_COMB (@lem5156563) (@lem5156532)). Qed.
Lemma lem5156565 (h1 : term79) : term449.
Proof. exact (EQ_MP (@lem5156564) (@lem5156189 h1)). Qed.
Lemma lem5156578 (y : real) (x : real) : (term454 y x) = (term454 y x).
Proof. exact (eq_refl (term454 y x)). Qed.
Lemma lem5156579 (x : real) : (term465 x) = (term465 x).
Proof. exact (fun_ext (fun y : real => @lem5156578 y x)). Qed.
Lemma lem5156580 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156581 (x : real) : (term481 x) = (term481 x).
Proof. exact (MK_COMB (@lem5156580) (@lem5156579 x)). Qed.
Lemma lem5156582 : term488 = term488.
Proof. exact (fun_ext (fun x : real => @lem5156581 x)). Qed.
Lemma lem5156583 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156584 : term503 = term503.
Proof. exact (MK_COMB (@lem5156583) (@lem5156582)). Qed.
Lemma lem5156601 (y : real) (x : real) : (term467 y x) = (term467 y x).
Proof. exact (eq_refl (term467 y x)). Qed.
Lemma lem5156602 (x : real) : (term464 x) = (term464 x).
Proof. exact (fun_ext (fun y : real => @lem5156601 y x)). Qed.
Lemma lem5156603 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156604 (x : real) : (term476 x) = (term476 x).
Proof. exact (MK_COMB (@lem5156603) (@lem5156602 x)). Qed.
Lemma lem5156605 : term487 = term487.
Proof. exact (fun_ext (fun x : real => @lem5156604 x)). Qed.
Lemma lem5156606 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156607 : term498 = term498.
Proof. exact (MK_COMB (@lem5156606) (@lem5156605)). Qed.
Lemma lem5156608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5156609 : term500 = term500.
Proof. exact (MK_COMB (@lem5156608) (@lem5156607)). Qed.
Lemma lem5156610 : term504 = term504.
Proof. exact (MK_COMB (@lem5156609) (@lem5156584)). Qed.
Lemma lem5156611 (h1 : term35) : term504.
Proof. exact (EQ_MP (@lem5156610) (@lem5156478 h1)). Qed.
Lemma lem5156616 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5156623 (y : real) (b' : real) : (term71 y b') = (term71 y b').
Proof. exact (eq_refl (term71 y b')). Qed.
Lemma lem5156638 (s : real -> Prop) (x : real) (b' : real) : (term92 s x b') = (term92 s x b').
Proof. exact (eq_refl (term92 s x b')). Qed.
Lemma lem5156639 (s : real -> Prop) (b' : real) : (term93 s b') = (term93 s b').
Proof. exact (fun_ext (fun x : real => @lem5156638 s x b')). Qed.
Lemma lem5156640 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156641 (s : real -> Prop) (b' : real) : (term94 s b') = (term94 s b').
Proof. exact (MK_COMB (@lem5156640) (@lem5156639 s b')). Qed.
Lemma lem5156642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5156643 (s : real -> Prop) (b' : real) : (term154 s b') = (term154 s b').
Proof. exact (MK_COMB (@lem5156642) (@lem5156641 s b')). Qed.
Lemma lem5156644 (s : real -> Prop) (y : real) (b' : real) : (term156 s y b') = (term156 s y b').
Proof. exact (MK_COMB (@lem5156643 s b') (@lem5156623 y b')). Qed.
Lemma lem5156661 (s : real -> Prop) (b' : real) (y : real) : (term232 s b' y) = (term232 s b' y).
Proof. exact (eq_refl (term232 s b' y)). Qed.
Lemma lem5156662 (s : real -> Prop) (y : real) (b' : real) : (term310 s y b') = (term310 s y b').
Proof. exact (MK_COMB (@lem5156661 s b' y) (@lem5156644 s y b')). Qed.
Lemma lem5156663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5156664 (s : real -> Prop) (y : real) (b' : real) : (term330 s y b') = (term330 s y b').
Proof. exact (MK_COMB (@lem5156663) (@lem5156662 s y b')). Qed.
Lemma lem5156665 (s : real -> Prop) (b' : real) (y : real) (b : real) : (term332 s b' y b) = (term332 s b' y b).
Proof. exact (MK_COMB (@lem5156664 s y b') (@lem5156616 y b)). Qed.
Lemma lem5156672 (y : real) (b : real) : (term175 y b) = (term175 y b).
Proof. exact (eq_refl (term175 y b)). Qed.
Lemma lem5156699 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term253 s x y b) = (term253 s x y b).
Proof. exact (eq_refl (term253 s x y b)). Qed.
Lemma lem5156700 (s : real -> Prop) (x : real -> real) (y : real) : (term255 s x y) = (term255 s x y).
Proof. exact (fun_ext (fun b : real => @lem5156699 s x y b)). Qed.
Lemma lem5156701 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156702 (s : real -> Prop) (x : real -> real) (y : real) : (term257 s x y) = (term257 s x y).
Proof. exact (MK_COMB (@lem5156701) (@lem5156700 s x y)). Qed.
Lemma lem5156717 (s : real -> Prop) (x : real) (y : real) : (term92 s x y) = (term92 s x y).
Proof. exact (eq_refl (term92 s x y)). Qed.
Lemma lem5156718 (s : real -> Prop) (y : real) : (term93 s y) = (term93 s y).
Proof. exact (fun_ext (fun x : real => @lem5156717 s x y)). Qed.
Lemma lem5156719 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156720 (s : real -> Prop) (y : real) : (term94 s y) = (term94 s y).
Proof. exact (MK_COMB (@lem5156719) (@lem5156718 s y)). Qed.
Lemma lem5156721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5156722 (s : real -> Prop) (y : real) : (term154 s y) = (term154 s y).
Proof. exact (MK_COMB (@lem5156721) (@lem5156720 s y)). Qed.
Lemma lem5156723 (s : real -> Prop) (x : real -> real) (y : real) : (term274 s x y) = (term274 s x y).
Proof. exact (MK_COMB (@lem5156722 s y) (@lem5156702 s x y)). Qed.
Lemma lem5156724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5156725 (s : real -> Prop) (x : real -> real) (y : real) : (term293 s x y) = (term293 s x y).
Proof. exact (MK_COMB (@lem5156724) (@lem5156723 s x y)). Qed.
Lemma lem5156726 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term295 s x y b) = (term295 s x y b).
Proof. exact (MK_COMB (@lem5156725 s x y) (@lem5156672 y b)). Qed.
Lemma lem5156727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5156728 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term368 s x y b) = (term368 s x y b).
Proof. exact (MK_COMB (@lem5156727) (@lem5156726 s x y b)). Qed.
Lemma lem5156729 (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) : (term382 x s b' y b) = (term382 x s b' y b).
Proof. exact (MK_COMB (@lem5156728 s x y b) (@lem5156665 s b' y b)). Qed.
Lemma lem5156730 (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term382 x s b' y b) : term382 x s b' y b.
Proof. exact (EQ_MP (@lem5156729 x s b' y b) (@lem5156481 x s b' y b h1)). Qed.
Lemma lem5156757 (b : real) (s : real -> Prop) (x' : real -> real) (b' : real) : (term135 b s x' b') = (term135 b s x' b').
Proof. exact (eq_refl (term135 b s x' b')). Qed.
Lemma lem5156758 (b : real) (s : real -> Prop) (x' : real -> real) : (term137 b s x') = (term137 b s x').
Proof. exact (fun_ext (fun b' : real => @lem5156757 b s x' b')). Qed.
Lemma lem5156759 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156760 (b : real) (s : real -> Prop) (x' : real -> real) : (term139 b s x') = (term139 b s x').
Proof. exact (MK_COMB (@lem5156759) (@lem5156758 b s x')). Qed.
Lemma lem5156761 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term139 b s x'.
Proof. exact (EQ_MP (@lem5156760 b s x') (@lem5156482 b s x' h1)). Qed.
Lemma lem5156762 (h1 : term35) : term503.
Proof. exact (proj2 (@lem5156611 h1)). Qed.
Lemma lem5156763 (h1 : term35) : term498.
Proof. exact (proj1 (@lem5156611 h1)). Qed.
Lemma lem5156764 (h1 : term79) : term448.
Proof. exact (proj2 (@lem5156565 h1)). Qed.
Lemma lem5156766 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term295 s x y b.
Proof. exact (h1). Qed.
Lemma lem5156767 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : term332 s b' y b.
Proof. exact (h1). Qed.
Lemma lem5156769 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term274 s x y.
Proof. exact (proj1 (@lem5156766 s x y b h1)). Qed.
Lemma lem5156770 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term257 s x y.
Proof. exact (proj2 (@lem5156769 s x y b h1)). Qed.
Lemma lem5156771 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term94 s y.
Proof. exact (proj1 (@lem5156769 s x y b h1)). Qed.
Lemma lem5156773 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : term310 s y b'.
Proof. exact (proj1 (@lem5156767 s b' y b h1)). Qed.
Lemma lem5156774 (s : real -> Prop) (b' : real) (y : real) (h1 : term144 s b' y) : term144 s b' y.
Proof. exact (h1). Qed.
Lemma lem5156775 (s : real -> Prop) (y : real) (b' : real) (h1 : term156 s y b') : term156 s y b'.
Proof. exact (h1). Qed.
Lemma lem5156779 (s : real -> Prop) (y : real) (b' : real) (h1 : term156 s y b') : term94 s b'.
Proof. exact (proj1 (@lem5156775 s y b' h1)). Qed.
Lemma lem5156787 (s : real -> Prop) (x : real) (b : real) : (term92 s x b) = (term92 s x b).
Proof. exact (eq_refl (term92 s x b)). Qed.
Lemma lem5156788 (s : real -> Prop) (b : real) : (term93 s b) = (term93 s b).
Proof. exact (fun_ext (fun x : real => @lem5156787 s x b)). Qed.
Lemma lem5156789 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156791 (s : real -> Prop) (b : real) : (term94 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5156789) (@lem5156788 s b)). Qed.
Lemma lem5156792 (s : real -> Prop) (b : real) (h1 : term19 s b) : term94 s b.
Proof. exact (EQ_MP (@lem5156791 s b) (@lem5156501 s b h1)). Qed.
Lemma lem5156810 (s : real -> Prop) (b : real) (x' : real -> real) (b' : real) : (term135 b s x' b') = (term505 s b x' b').
Proof. exact (@lem19490 (term506 x' b' s) (term105 b' b) (term507 x' b')). Qed.
Lemma lem5156811 (s : real -> Prop) (b : real) (x' : real -> real) : (term137 b s x') = (term508 s b x').
Proof. exact (fun_ext (fun b' : real => @lem5156810 s b x' b')). Qed.
Lemma lem5156812 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156814 (s : real -> Prop) (b : real) (x' : real -> real) : (term139 b s x') = (term509 s b x').
Proof. exact (MK_COMB (@lem5156812) (@lem5156811 s b x')). Qed.
Lemma lem5156815 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term509 s b x'.
Proof. exact (EQ_MP (@lem5156814 s b x') (@lem5156761 b s x' h1)). Qed.
Lemma lem5156823 (y : real) (x : real) : (term467 y x) = (term467 y x).
Proof. exact (eq_refl (term467 y x)). Qed.
Lemma lem5156824 (x : real) : (term464 x) = (term464 x).
Proof. exact (fun_ext (fun y : real => @lem5156823 y x)). Qed.
Lemma lem5156825 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156826 (x : real) : (term476 x) = (term476 x).
Proof. exact (MK_COMB (@lem5156825) (@lem5156824 x)). Qed.
Lemma lem5156827 : term487 = term487.
Proof. exact (fun_ext (fun x : real => @lem5156826 x)). Qed.
Lemma lem5156828 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156830 : term498 = term498.
Proof. exact (MK_COMB (@lem5156828) (@lem5156827)). Qed.
Lemma lem5156831 (h1 : term35) : term498.
Proof. exact (EQ_MP (@lem5156830) (@lem5156763 h1)). Qed.
Lemma lem5156839 (y : real) (x : real) : (term454 y x) = (term454 y x).
Proof. exact (eq_refl (term454 y x)). Qed.
Lemma lem5156840 (x : real) : (term465 x) = (term465 x).
Proof. exact (fun_ext (fun y : real => @lem5156839 y x)). Qed.
Lemma lem5156841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156842 (x : real) : (term481 x) = (term481 x).
Proof. exact (MK_COMB (@lem5156841) (@lem5156840 x)). Qed.
Lemma lem5156843 : term488 = term488.
Proof. exact (fun_ext (fun x : real => @lem5156842 x)). Qed.
Lemma lem5156844 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156846 : term503 = term503.
Proof. exact (MK_COMB (@lem5156844) (@lem5156843)). Qed.
Lemma lem5156847 (h1 : term35) : term503.
Proof. exact (EQ_MP (@lem5156846) (@lem5156762 h1)). Qed.
Lemma lem5156887 (x : real) (y : real) : (term395 x y) = (term395 x y).
Proof. exact (eq_refl (term395 x y)). Qed.
Lemma lem5156888 (x : real) : (term410 x) = (term410 x).
Proof. exact (fun_ext (fun y : real => @lem5156887 x y)). Qed.
Lemma lem5156889 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156890 (x : real) : (term426 x) = (term426 x).
Proof. exact (MK_COMB (@lem5156889) (@lem5156888 x)). Qed.
Lemma lem5156891 : term433 = term433.
Proof. exact (fun_ext (fun x : real => @lem5156890 x)). Qed.
Lemma lem5156892 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156894 : term448 = term448.
Proof. exact (MK_COMB (@lem5156892) (@lem5156891)). Qed.
Lemma lem5156895 (h1 : term79) : term448.
Proof. exact (EQ_MP (@lem5156894) (@lem5156764 h1)). Qed.
Lemma lem5156907 (s : real -> Prop) (x : real) (y : real) : (term92 s x y) = (term92 s x y).
Proof. exact (eq_refl (term92 s x y)). Qed.
Lemma lem5156908 (s : real -> Prop) (y : real) : (term93 s y) = (term93 s y).
Proof. exact (fun_ext (fun x : real => @lem5156907 s x y)). Qed.
Lemma lem5156909 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156911 (s : real -> Prop) (y : real) : (term94 s y) = (term94 s y).
Proof. exact (MK_COMB (@lem5156909) (@lem5156908 s y)). Qed.
Lemma lem5156912 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term94 s y.
Proof. exact (EQ_MP (@lem5156911 s y) (@lem5156771 s x y b h1)). Qed.
Lemma lem5156930 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term253 s x y b) = (term510 s x y b).
Proof. exact (@lem19699 (term506 x b s) (term511 x b) (real_le y b)). Qed.
Lemma lem5156931 (s : real -> Prop) (x : real -> real) (y : real) : (term255 s x y) = (term512 s x y).
Proof. exact (fun_ext (fun b : real => @lem5156930 s x y b)). Qed.
Lemma lem5156932 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156934 (s : real -> Prop) (x : real -> real) (y : real) : (term257 s x y) = (term513 s x y).
Proof. exact (MK_COMB (@lem5156932) (@lem5156931 s x y)). Qed.
Lemma lem5156935 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term513 s x y.
Proof. exact (EQ_MP (@lem5156934 s x y) (@lem5156770 s x y b h1)). Qed.
Lemma lem5156943 (s : real -> Prop) (x : real) (b : real) : (term92 s x b) = (term92 s x b).
Proof. exact (eq_refl (term92 s x b)). Qed.
Lemma lem5156944 (s : real -> Prop) (b : real) : (term93 s b) = (term93 s b).
Proof. exact (fun_ext (fun x : real => @lem5156943 s x b)). Qed.
Lemma lem5156945 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5156947 (s : real -> Prop) (b : real) : (term94 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5156945) (@lem5156944 s b)). Qed.
Lemma lem5156948 (s : real -> Prop) (b : real) (h1 : term19 s b) : term94 s b.
Proof. exact (EQ_MP (@lem5156947 s b) (@lem5156501 s b h1)). Qed.
Lemma lem5157094 (s : real -> Prop) (b : real) (x' : real -> real) (b' : real) : (term135 b s x' b') = (term505 s b x' b').
Proof. exact (@lem19490 (term506 x' b' s) (term105 b' b) (term507 x' b')). Qed.
Lemma lem5157095 (s : real -> Prop) (b : real) (x' : real -> real) : (term137 b s x') = (term508 s b x').
Proof. exact (fun_ext (fun b' : real => @lem5157094 s b x' b')). Qed.
Lemma lem5157096 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5157098 (s : real -> Prop) (b : real) (x' : real -> real) : (term139 b s x') = (term509 s b x').
Proof. exact (MK_COMB (@lem5157096) (@lem5157095 s b x')). Qed.
Lemma lem5157099 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term509 s b x'.
Proof. exact (EQ_MP (@lem5157098 s b x') (@lem5156761 b s x' h1)). Qed.
Lemma lem5157107 (y : real) (x : real) : (term467 y x) = (term467 y x).
Proof. exact (eq_refl (term467 y x)). Qed.
Lemma lem5157108 (x : real) : (term464 x) = (term464 x).
Proof. exact (fun_ext (fun y : real => @lem5157107 y x)). Qed.
Lemma lem5157109 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5157110 (x : real) : (term476 x) = (term476 x).
Proof. exact (MK_COMB (@lem5157109) (@lem5157108 x)). Qed.
Lemma lem5157111 : term487 = term487.
Proof. exact (fun_ext (fun x : real => @lem5157110 x)). Qed.
Lemma lem5157112 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5157114 : term498 = term498.
Proof. exact (MK_COMB (@lem5157112) (@lem5157111)). Qed.
Lemma lem5157115 (h1 : term35) : term498.
Proof. exact (EQ_MP (@lem5157114) (@lem5156763 h1)). Qed.
Lemma lem5157123 (y : real) (x : real) : (term454 y x) = (term454 y x).
Proof. exact (eq_refl (term454 y x)). Qed.
Lemma lem5157124 (x : real) : (term465 x) = (term465 x).
Proof. exact (fun_ext (fun y : real => @lem5157123 y x)). Qed.
Lemma lem5157125 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5157126 (x : real) : (term481 x) = (term481 x).
Proof. exact (MK_COMB (@lem5157125) (@lem5157124 x)). Qed.
Lemma lem5157127 : term488 = term488.
Proof. exact (fun_ext (fun x : real => @lem5157126 x)). Qed.
Lemma lem5157128 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5157130 : term503 = term503.
Proof. exact (MK_COMB (@lem5157128) (@lem5157127)). Qed.
Lemma lem5157131 (h1 : term35) : term503.
Proof. exact (EQ_MP (@lem5157130) (@lem5156762 h1)). Qed.
Lemma lem5157191 (s : real -> Prop) (x : real) (b' : real) : (term92 s x b') = (term92 s x b').
Proof. exact (eq_refl (term92 s x b')). Qed.
Lemma lem5157192 (s : real -> Prop) (b' : real) : (term93 s b') = (term93 s b').
Proof. exact (fun_ext (fun x : real => @lem5157191 s x b')). Qed.
Lemma lem5157193 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5157195 (s : real -> Prop) (b' : real) : (term94 s b') = (term94 s b').
Proof. exact (MK_COMB (@lem5157193) (@lem5157192 s b')). Qed.
Lemma lem5157196 (s : real -> Prop) (y : real) (b' : real) (h1 : term156 s y b') : term94 s b'.
Proof. exact (EQ_MP (@lem5157195 s b') (@lem5156779 s y b' h1)). Qed.
Lemma lem5157201 (_67334 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term514 s b _67334.
Proof. exact (@lem5156792 s b h1 _67334). Qed.
Lemma lem5157202 (s : real -> Prop) (_67334 : real) (b : real) : (term514 s b _67334) = (term92 s _67334 b).
Proof. exact (eq_refl (term514 s b _67334)). Qed.
Lemma lem5157204 (_67335 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term515 s b x' _67335.
Proof. exact (@lem5156815 b s x' h1 _67335). Qed.
Lemma lem5157205 (s : real -> Prop) (b : real) (x' : real -> real) (_67335 : real) : (term515 s b x' _67335) = (term505 s b x' _67335).
Proof. exact (eq_refl (term515 s b x' _67335)). Qed.
Lemma lem5157206 (_67335 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term505 s b x' _67335.
Proof. exact (EQ_MP (@lem5157205 s b x' _67335) (@lem5157204 _67335 b s x' h1)). Qed.
Lemma lem5157207 (_67336 : real) (h1 : term35) : term489 _67336.
Proof. exact (@lem5156831 h1 _67336). Qed.
Lemma lem5157208 (_67336 : real) : (term489 _67336) = (term476 _67336).
Proof. exact (eq_refl (term489 _67336)). Qed.
Lemma lem5157209 (_67336 : real) (h1 : term35) : term476 _67336.
Proof. exact (EQ_MP (@lem5157208 _67336) (@lem5157207 _67336 h1)). Qed.
Lemma lem5157210 (_67336 : real) (_67337 : real) (h1 : term35) : term466 _67336 _67337.
Proof. exact (@lem5157209 _67336 h1 _67337). Qed.
Lemma lem5157211 (_67337 : real) (_67336 : real) : (term466 _67336 _67337) = (term467 _67337 _67336).
Proof. exact (eq_refl (term466 _67336 _67337)). Qed.
Lemma lem5157213 (_67338 : real) (h1 : term35) : term491 _67338.
Proof. exact (@lem5156847 h1 _67338). Qed.
Lemma lem5157214 (_67338 : real) : (term491 _67338) = (term481 _67338).
Proof. exact (eq_refl (term491 _67338)). Qed.
Lemma lem5157215 (_67338 : real) (h1 : term35) : term481 _67338.
Proof. exact (EQ_MP (@lem5157214 _67338) (@lem5157213 _67338 h1)). Qed.
Lemma lem5157216 (_67338 : real) (_67339 : real) (h1 : term35) : term469 _67338 _67339.
Proof. exact (@lem5157215 _67338 h1 _67339). Qed.
Lemma lem5157217 (_67339 : real) (_67338 : real) : (term469 _67338 _67339) = (term454 _67339 _67338).
Proof. exact (eq_refl (term469 _67338 _67339)). Qed.
Lemma lem5157225 (_67342 : real) (h1 : term79) : term436 _67342.
Proof. exact (@lem5156895 h1 _67342). Qed.
Lemma lem5157226 (_67342 : real) : (term436 _67342) = (term426 _67342).
Proof. exact (eq_refl (term436 _67342)). Qed.
Lemma lem5157227 (_67342 : real) (h1 : term79) : term426 _67342.
Proof. exact (EQ_MP (@lem5157226 _67342) (@lem5157225 _67342 h1)). Qed.
Lemma lem5157228 (_67342 : real) (_67343 : real) (h1 : term79) : term414 _67342 _67343.
Proof. exact (@lem5157227 _67342 h1 _67343). Qed.
Lemma lem5157229 (_67342 : real) (_67343 : real) : (term414 _67342 _67343) = (term395 _67342 _67343).
Proof. exact (eq_refl (term414 _67342 _67343)). Qed.
Lemma lem5157230 (_67342 : real) (_67343 : real) (h1 : term79) : term395 _67342 _67343.
Proof. exact (EQ_MP (@lem5157229 _67342 _67343) (@lem5157228 _67342 _67343 h1)). Qed.
Lemma lem5157231 (_67344 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term514 s y _67344.
Proof. exact (@lem5156912 s x y b h1 _67344). Qed.
Lemma lem5157232 (s : real -> Prop) (_67344 : real) (y : real) : (term514 s y _67344) = (term92 s _67344 y).
Proof. exact (eq_refl (term514 s y _67344)). Qed.
Lemma lem5157234 (_67345 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term516 s x y _67345.
Proof. exact (@lem5156935 s x y b h1 _67345). Qed.
Lemma lem5157235 (s : real -> Prop) (x : real -> real) (y : real) (_67345 : real) : (term516 s x y _67345) = (term510 s x y _67345).
Proof. exact (eq_refl (term516 s x y _67345)). Qed.
Lemma lem5157236 (_67345 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term510 s x y _67345.
Proof. exact (EQ_MP (@lem5157235 s x y _67345) (@lem5157234 _67345 s x y b h1)). Qed.
Lemma lem5157237 (_67346 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term514 s b _67346.
Proof. exact (@lem5156948 s b h1 _67346). Qed.
Lemma lem5157238 (s : real -> Prop) (_67346 : real) (b : real) : (term514 s b _67346) = (term92 s _67346 b).
Proof. exact (eq_refl (term514 s b _67346)). Qed.
Lemma lem5157270 (_67357 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term515 s b x' _67357.
Proof. exact (@lem5157099 b s x' h1 _67357). Qed.
Lemma lem5157271 (s : real -> Prop) (b : real) (x' : real -> real) (_67357 : real) : (term515 s b x' _67357) = (term505 s b x' _67357).
Proof. exact (eq_refl (term515 s b x' _67357)). Qed.
Lemma lem5157272 (_67357 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term505 s b x' _67357.
Proof. exact (EQ_MP (@lem5157271 s b x' _67357) (@lem5157270 _67357 b s x' h1)). Qed.
Lemma lem5157273 (_67358 : real) (h1 : term35) : term489 _67358.
Proof. exact (@lem5157115 h1 _67358). Qed.
Lemma lem5157274 (_67358 : real) : (term489 _67358) = (term476 _67358).
Proof. exact (eq_refl (term489 _67358)). Qed.
Lemma lem5157275 (_67358 : real) (h1 : term35) : term476 _67358.
Proof. exact (EQ_MP (@lem5157274 _67358) (@lem5157273 _67358 h1)). Qed.
Lemma lem5157276 (_67358 : real) (_67359 : real) (h1 : term35) : term466 _67358 _67359.
Proof. exact (@lem5157275 _67358 h1 _67359). Qed.
Lemma lem5157277 (_67359 : real) (_67358 : real) : (term466 _67358 _67359) = (term467 _67359 _67358).
Proof. exact (eq_refl (term466 _67358 _67359)). Qed.
Lemma lem5157279 (_67360 : real) (h1 : term35) : term491 _67360.
Proof. exact (@lem5157131 h1 _67360). Qed.
Lemma lem5157280 (_67360 : real) : (term491 _67360) = (term481 _67360).
Proof. exact (eq_refl (term491 _67360)). Qed.
Lemma lem5157281 (_67360 : real) (h1 : term35) : term481 _67360.
Proof. exact (EQ_MP (@lem5157280 _67360) (@lem5157279 _67360 h1)). Qed.
Lemma lem5157282 (_67360 : real) (_67361 : real) (h1 : term35) : term469 _67360 _67361.
Proof. exact (@lem5157281 _67360 h1 _67361). Qed.
Lemma lem5157283 (_67361 : real) (_67360 : real) : (term469 _67360 _67361) = (term454 _67361 _67360).
Proof. exact (eq_refl (term469 _67360 _67361)). Qed.
Lemma lem5157297 (_67366 : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term156 s y b') : term514 s b' _67366.
Proof. exact (@lem5157196 s y b' h1 _67366). Qed.
Lemma lem5157298 (s : real -> Prop) (_67366 : real) (b' : real) : (term514 s b' _67366) = (term92 s _67366 b').
Proof. exact (eq_refl (term514 s b' _67366)). Qed.
Lemma lem5157319 (_67334 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term92 s _67334 b.
Proof. exact (EQ_MP (@lem5157202 s _67334 b) (@lem5157201 _67334 s b h1)). Qed.
Lemma lem5157325 (_67337 : real) (_67336 : real) (h1 : term35) : term467 _67337 _67336.
Proof. exact (EQ_MP (@lem5157211 _67337 _67336) (@lem5157210 _67336 _67337 h1)). Qed.
Lemma lem5157331 (_67339 : real) (_67338 : real) (h1 : term35) : term454 _67339 _67338.
Proof. exact (EQ_MP (@lem5157217 _67339 _67338) (@lem5157216 _67338 _67339 h1)). Qed.
Lemma lem5157342 (_67342 : real) (_67343 : real) : (term395 _67342 _67343) = (term517 _67342 _67343).
Proof. exact (@lem5154382 (term71 _67342 _67343) (term71 _67343 _67342) (_67342 = _67343)). Qed.
Lemma lem5157343 (_67342 : real) (_67343 : real) (h1 : term79) : term517 _67342 _67343.
Proof. exact (EQ_MP (@lem5157342 _67342 _67343) (@lem5157230 _67342 _67343 h1)). Qed.
Lemma lem5157345 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term175 y b.
Proof. exact (proj2 (@lem5156766 s x y b h1)). Qed.
Lemma lem5157351 (_67344 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term92 s _67344 y.
Proof. exact (EQ_MP (@lem5157232 s _67344 y) (@lem5157231 _67344 s x y b h1)). Qed.
Lemma lem5157357 (_67345 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term518 x s y _67345.
Proof. exact (proj1 (@lem5157236 _67345 s x y b h1)). Qed.
Lemma lem5157363 (_67345 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term519 x y _67345.
Proof. exact (proj2 (@lem5157236 _67345 s x y b h1)). Qed.
Lemma lem5157381 (_67335 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term520 b x' _67335 s.
Proof. exact (proj1 (@lem5157206 _67335 b s x' h1)). Qed.
Lemma lem5157387 (_67335 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term521 b x' _67335.
Proof. exact (proj2 (@lem5157206 _67335 b s x' h1)). Qed.
Lemma lem5157419 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : y = b.
Proof. exact (proj2 (@lem5156767 s b' y b h1)). Qed.
Lemma lem5157423 (s : real -> Prop) (b' : real) (y : real) (h1 : term144 s b' y) : term71 b' y.
Proof. exact (proj2 (@lem5156774 s b' y h1)). Qed.
Lemma lem5157479 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : y = b.
Proof. exact (proj2 (@lem5156767 s b' y b h1)). Qed.
Lemma lem5157487 (s : real -> Prop) (y : real) (b' : real) (h1 : term156 s y b') : term71 y b'.
Proof. exact (proj2 (@lem5156775 s y b' h1)). Qed.
Lemma lem5157539 (_67346 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term92 s _67346 b.
Proof. exact (EQ_MP (@lem5157238 s _67346 b) (@lem5157237 _67346 s b h1)). Qed.
Lemma lem5157596 (b' : real) : (term522 b') = (term522 b').
Proof. exact (eq_refl (term522 b')). Qed.
Lemma lem5157597 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : (term523 b' y) = (term523 b' b).
Proof. exact (MK_COMB (@lem5157596 b') (@lem5157419 s b' y b h1)). Qed.
Lemma lem5157598 (b' : real) (b : real) : (term523 b' b) = (term71 b' b).
Proof. exact (eq_refl (term523 b' b)). Qed.
Lemma lem5157599 (b' : real) (y : real) : (term524 b' y) = (term524 b' y).
Proof. exact (eq_refl (term524 b' y)). Qed.
Lemma lem5157600 (y : real) (b' : real) (b : real) : ((term523 b' y) = (term523 b' b)) = ((term523 b' y) = (term71 b' b)).
Proof. exact (MK_COMB (@lem5157599 b' y) (@lem5157598 b' b)). Qed.
Lemma lem5157601 (b' : real) (y : real) : (term523 b' y) = (term71 b' y).
Proof. exact (eq_refl (term523 b' y)). Qed.
Lemma lem5157602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5157603 (b' : real) (y : real) : (term524 b' y) = (term525 b' y).
Proof. exact (MK_COMB (@lem5157602) (@lem5157601 b' y)). Qed.
Lemma lem5157604 (b' : real) (b : real) : (term71 b' b) = (term71 b' b).
Proof. exact (eq_refl (term71 b' b)). Qed.
Lemma lem5157605 (y : real) (b' : real) (b : real) : ((term523 b' y) = (term71 b' b)) = ((term71 b' y) = (term71 b' b)).
Proof. exact (MK_COMB (@lem5157603 b' y) (@lem5157604 b' b)). Qed.
Lemma lem5157606 (y : real) (b' : real) (b : real) : ((term523 b' y) = (term523 b' b)) = ((term71 b' y) = (term71 b' b)).
Proof. exact (TRANS (@lem5157600 y b' b) (@lem5157605 y b' b)). Qed.
Lemma lem5157607 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : (term71 b' y) = (term71 b' b).
Proof. exact (EQ_MP (@lem5157606 y b' b) (@lem5157597 s b' y b h1)). Qed.
Lemma lem5157608 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term144 s b' y) (h2 : term332 s b' y b) : term71 b' b.
Proof. exact (EQ_MP (@lem5157607 s b' y b h2) (@lem5157423 s b' y h1)). Qed.
Lemma lem5157706 (_67359 : real) (_67358 : real) (h1 : term35) : term467 _67359 _67358.
Proof. exact (EQ_MP (@lem5157277 _67359 _67358) (@lem5157276 _67358 _67359 h1)). Qed.
Lemma lem5157720 (_67361 : real) (_67360 : real) (h1 : term35) : term454 _67361 _67360.
Proof. exact (EQ_MP (@lem5157283 _67361 _67360) (@lem5157282 _67360 _67361 h1)). Qed.
Lemma lem5157748 (_67366 : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term156 s y b') : term92 s _67366 b'.
Proof. exact (EQ_MP (@lem5157298 s _67366 b') (@lem5157297 _67366 s y b' h1)). Qed.
Lemma lem5157749 (b' : real) : (term526 b') = (term526 b').
Proof. exact (eq_refl (term526 b')). Qed.
Lemma lem5157750 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : (term527 b' y) = (term527 b' b).
Proof. exact (MK_COMB (@lem5157749 b') (@lem5157479 s b' y b h1)). Qed.
Lemma lem5157751 (b : real) (b' : real) : (term527 b' b) = (term71 b b').
Proof. exact (eq_refl (term527 b' b)). Qed.
Lemma lem5157752 (b' : real) (y : real) : (term528 b' y) = (term528 b' y).
Proof. exact (eq_refl (term528 b' y)). Qed.
Lemma lem5157753 (y : real) (b : real) (b' : real) : ((term527 b' y) = (term527 b' b)) = ((term527 b' y) = (term71 b b')).
Proof. exact (MK_COMB (@lem5157752 b' y) (@lem5157751 b b')). Qed.
Lemma lem5157754 (y : real) (b' : real) : (term527 b' y) = (term71 y b').
Proof. exact (eq_refl (term527 b' y)). Qed.
Lemma lem5157755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5157756 (y : real) (b' : real) : (term528 b' y) = (term525 y b').
Proof. exact (MK_COMB (@lem5157755) (@lem5157754 y b')). Qed.
Lemma lem5157757 (b : real) (b' : real) : (term71 b b') = (term71 b b').
Proof. exact (eq_refl (term71 b b')). Qed.
Lemma lem5157758 (y : real) (b : real) (b' : real) : ((term527 b' y) = (term71 b b')) = ((term71 y b') = (term71 b b')).
Proof. exact (MK_COMB (@lem5157756 y b') (@lem5157757 b b')). Qed.
Lemma lem5157759 (y : real) (b : real) (b' : real) : ((term527 b' y) = (term527 b' b)) = ((term71 y b') = (term71 b b')).
Proof. exact (TRANS (@lem5157753 y b b') (@lem5157758 y b b')). Qed.
Lemma lem5157760 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : (term71 y b') = (term71 b b').
Proof. exact (EQ_MP (@lem5157759 y b b') (@lem5157750 s b' y b h1)). Qed.
Lemma lem5157761 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term156 s y b') (h2 : term332 s b' y b) : term71 b b'.
Proof. exact (EQ_MP (@lem5157760 s b' y b h2) (@lem5157487 s y b' h1)). Qed.
Lemma lem5157803 (_67357 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term520 b x' _67357 s.
Proof. exact (proj1 (@lem5157272 _67357 b s x' h1)). Qed.
Lemma lem5157817 (_67357 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term521 b x' _67357.
Proof. exact (proj2 (@lem5157272 _67357 b s x' h1)). Qed.
Lemma lem5157897 (y : real) (b : real) (h1 : term71 y b) : term71 y b.
Proof. exact (h1). Qed.
Lemma lem5157898 (y : real) (b : real) (h1 : term71 y b) : term529 y b.
Proof. exact (fun h0 : real_le y b => @lem5157897 y b h1). Qed.
Lemma lem5157900 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5157901 (y : real) (b : real) : (term529 y b) = (term71 y b).
Proof. exact (@lem5157900 (real_le y b)). Qed.
Lemma lem5157902 (y : real) (b : real) (h1 : term71 y b) : term71 y b.
Proof. exact (EQ_MP (@lem5157901 y b) (@lem5157898 y b h1)). Qed.
Lemma lem5157904 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5157907 (y : real) (x : real -> real) (_67345 : real) (s : real -> Prop) : (term518 x s y _67345) = (term532 y x _67345 s).
Proof. exact (@lem5157904 (real_le y _67345) (term506 x _67345 s)). Qed.
Lemma lem5157910 (_67345 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term532 y x _67345 s.
Proof. exact (EQ_MP (@lem5157907 y x _67345 s) (@lem5157357 _67345 s x y b h1)). Qed.
Lemma lem5157911 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term532 y x b s.
Proof. exact (@lem5157910 b s x y b h1). Qed.
Lemma lem5157914 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term71 y b) (h2 : term295 s x y b) : term506 x b s.
Proof. exact (@lem5157911 s x y b h2 (@lem5157902 y b h1)). Qed.
Lemma lem5157915 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term71 y b) (h2 : term295 s x y b) : term533 x b s.
Proof. exact (fun h0 : term534 x b s => @lem5157914 s x y b h1 h2). Qed.
Lemma lem5157917 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5157918 (x : real -> real) (b : real) (s : real -> Prop) : (term533 x b s) = (term506 x b s).
Proof. exact (@lem5157917 (term506 x b s)). Qed.
Lemma lem5157919 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term71 y b) (h2 : term295 s x y b) : term506 x b s.
Proof. exact (EQ_MP (@lem5157918 x b s) (@lem5157915 s x y b h1 h2)). Qed.
Lemma lem5157925 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5157926 (b : real) (_67334 : real) (s : real -> Prop) : (term92 s _67334 b) = (term536 b _67334 s).
Proof. exact (@lem5157925 (real_le _67334 b) (term537 _67334 s)). Qed.
Lemma lem5157932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5157933 (b : real) (_67334 : real) (s : real -> Prop) : (term538 s _67334 b) = (term539 b _67334 s).
Proof. exact (MK_COMB (@lem5157932) (@lem5157926 b _67334 s)). Qed.
Lemma lem5157939 (b : real) (_67334 : real) (s : real -> Prop) : (term536 b _67334 s) = (term536 b _67334 s).
Proof. exact (eq_refl (term536 b _67334 s)). Qed.
Lemma lem5157940 (b : real) (_67334 : real) (s : real -> Prop) : ((term92 s _67334 b) = (term536 b _67334 s)) = ((term536 b _67334 s) = (term536 b _67334 s)).
Proof. exact (MK_COMB (@lem5157933 b _67334 s) (@lem5157939 b _67334 s)). Qed.
Lemma lem5157942 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5157943 (x : Prop) : (x = x) = True.
Proof. exact (@lem5157942 Prop x). Qed.
Lemma lem5157944 (b : real) (_67334 : real) (s : real -> Prop) : ((term536 b _67334 s) = (term536 b _67334 s)) = True.
Proof. exact (@lem5157943 (term536 b _67334 s)). Qed.
Lemma lem5157945 (b : real) (_67334 : real) (s : real -> Prop) : ((term92 s _67334 b) = (term536 b _67334 s)) = True.
Proof. exact (TRANS (@lem5157940 b _67334 s) (@lem5157944 b _67334 s)). Qed.
Lemma lem5157946 (b : real) (_67334 : real) (s : real -> Prop) : True = ((term92 s _67334 b) = (term536 b _67334 s)).
Proof. exact (SYM (@lem5157945 b _67334 s)). Qed.
Lemma lem5157947 (b : real) (_67334 : real) (s : real -> Prop) : (term92 s _67334 b) = (term536 b _67334 s).
Proof. exact (EQ_MP (@lem5157946 b _67334 s) (@lem0)). Qed.
Lemma lem5157948 (_67334 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term536 b _67334 s.
Proof. exact (EQ_MP (@lem5157947 b _67334 s) (@lem5157319 _67334 s b h1)). Qed.
Lemma lem5157950 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5157951 (s : real -> Prop) (_67334 : real) (b : real) : (term536 b _67334 s) = (term540 s _67334 b).
Proof. exact (@lem5157950 (term537 _67334 s) (real_le _67334 b)). Qed.
Lemma lem5157953 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5157954 (_67334 : real) (s : real -> Prop) : (term542 _67334 s) = (@IN real _67334 s).
Proof. exact (@lem5157953 (@IN real _67334 s)). Qed.
Lemma lem5157955 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5157956 (_67334 : real) (s : real -> Prop) : (term543 _67334 s) = (term544 _67334 s).
Proof. exact (MK_COMB (@lem5157955) (@lem5157954 _67334 s)). Qed.
Lemma lem5157957 (_67334 : real) (b : real) : (real_le _67334 b) = (real_le _67334 b).
Proof. exact (eq_refl (real_le _67334 b)). Qed.
Lemma lem5157958 (s : real -> Prop) (_67334 : real) (b : real) : (term540 s _67334 b) = (term80 s _67334 b).
Proof. exact (MK_COMB (@lem5157956 _67334 s) (@lem5157957 _67334 b)). Qed.
Lemma lem5157959 (s : real -> Prop) (_67334 : real) (b : real) : (term536 b _67334 s) = (term80 s _67334 b).
Proof. exact (TRANS (@lem5157951 s _67334 b) (@lem5157958 s _67334 b)). Qed.
Lemma lem5157962 (_67334 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term80 s _67334 b.
Proof. exact (EQ_MP (@lem5157959 s _67334 b) (@lem5157948 _67334 s b h1)). Qed.
Lemma lem5157963 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term545 s x b.
Proof. exact (@lem5157962 (x b) s b h1). Qed.
Lemma lem5157966 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term19 s b) (h2 : term71 y b) (h3 : term295 s x y b) : term546 x b.
Proof. exact (@lem5157963 x s b h1 (@lem5157919 s x y b h2 h3)). Qed.
Lemma lem5157967 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term19 s b) (h2 : term71 y b) (h3 : term295 s x y b) : term547 x b.
Proof. exact (fun h0 : term511 x b => @lem5157966 s x y b h1 h2 h3). Qed.
Lemma lem5157969 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5157970 (x : real -> real) (b : real) : (term547 x b) = (term546 x b).
Proof. exact (@lem5157969 (term546 x b)). Qed.
Lemma lem5157971 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term19 s b) (h2 : term71 y b) (h3 : term295 s x y b) : term546 x b.
Proof. exact (EQ_MP (@lem5157970 x b) (@lem5157967 s x y b h1 h2 h3)). Qed.
Lemma lem5157977 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5157978 (y : real) (x : real -> real) (_67345 : real) : (term519 x y _67345) = (term548 y x _67345).
Proof. exact (@lem5157977 (real_le y _67345) (term511 x _67345)). Qed.
Lemma lem5157984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5157985 (y : real) (x : real -> real) (_67345 : real) : (term549 x y _67345) = (term550 y x _67345).
Proof. exact (MK_COMB (@lem5157984) (@lem5157978 y x _67345)). Qed.
Lemma lem5157991 (y : real) (x : real -> real) (_67345 : real) : (term548 y x _67345) = (term548 y x _67345).
Proof. exact (eq_refl (term548 y x _67345)). Qed.
Lemma lem5157992 (y : real) (x : real -> real) (_67345 : real) : ((term519 x y _67345) = (term548 y x _67345)) = ((term548 y x _67345) = (term548 y x _67345)).
Proof. exact (MK_COMB (@lem5157985 y x _67345) (@lem5157991 y x _67345)). Qed.
Lemma lem5157994 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5157995 (x : Prop) : (x = x) = True.
Proof. exact (@lem5157994 Prop x). Qed.
Lemma lem5157996 (y : real) (x : real -> real) (_67345 : real) : ((term548 y x _67345) = (term548 y x _67345)) = True.
Proof. exact (@lem5157995 (term548 y x _67345)). Qed.
Lemma lem5157997 (y : real) (x : real -> real) (_67345 : real) : ((term519 x y _67345) = (term548 y x _67345)) = True.
Proof. exact (TRANS (@lem5157992 y x _67345) (@lem5157996 y x _67345)). Qed.
Lemma lem5157998 (y : real) (x : real -> real) (_67345 : real) : True = ((term519 x y _67345) = (term548 y x _67345)).
Proof. exact (SYM (@lem5157997 y x _67345)). Qed.
Lemma lem5157999 (y : real) (x : real -> real) (_67345 : real) : (term519 x y _67345) = (term548 y x _67345).
Proof. exact (EQ_MP (@lem5157998 y x _67345) (@lem0)). Qed.
Lemma lem5158000 (_67345 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term548 y x _67345.
Proof. exact (EQ_MP (@lem5157999 y x _67345) (@lem5157363 _67345 s x y b h1)). Qed.
Lemma lem5158002 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158003 (x : real -> real) (y : real) (_67345 : real) : (term548 y x _67345) = (term551 x y _67345).
Proof. exact (@lem5158002 (term511 x _67345) (real_le y _67345)). Qed.
Lemma lem5158005 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5158006 (x : real -> real) (_67345 : real) : (term552 x _67345) = (term546 x _67345).
Proof. exact (@lem5158005 (term546 x _67345)). Qed.
Lemma lem5158007 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5158008 (x : real -> real) (_67345 : real) : (term553 x _67345) = (term554 x _67345).
Proof. exact (MK_COMB (@lem5158007) (@lem5158006 x _67345)). Qed.
Lemma lem5158009 (y : real) (_67345 : real) : (real_le y _67345) = (real_le y _67345).
Proof. exact (eq_refl (real_le y _67345)). Qed.
Lemma lem5158010 (x : real -> real) (y : real) (_67345 : real) : (term551 x y _67345) = (term555 x y _67345).
Proof. exact (MK_COMB (@lem5158008 x _67345) (@lem5158009 y _67345)). Qed.
Lemma lem5158011 (x : real -> real) (y : real) (_67345 : real) : (term548 y x _67345) = (term555 x y _67345).
Proof. exact (TRANS (@lem5158003 x y _67345) (@lem5158010 x y _67345)). Qed.
Lemma lem5158014 (_67345 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term555 x y _67345.
Proof. exact (EQ_MP (@lem5158011 x y _67345) (@lem5158000 _67345 s x y b h1)). Qed.
Lemma lem5158015 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term555 x y b.
Proof. exact (@lem5158014 b s x y b h1). Qed.
Lemma lem5158018 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term19 s b) (h2 : term71 y b) (h3 : term295 s x y b) : real_le y b.
Proof. exact (@lem5158015 s x y b h3 (@lem5157971 s x y b h1 h2 h3)). Qed.
Lemma lem5158019 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term19 s b) (h2 : term295 s x y b) : term556 y b.
Proof. exact (fun h0 : term71 y b => @lem5158018 s x y b h1 h0 h2). Qed.
Lemma lem5158021 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158022 (y : real) (b : real) : (term556 y b) = (real_le y b).
Proof. exact (@lem5158021 (real_le y b)). Qed.
Lemma lem5158023 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term19 s b) (h2 : term295 s x y b) : real_le y b.
Proof. exact (EQ_MP (@lem5158022 y b) (@lem5158019 s x y b h1 h2)). Qed.
Lemma lem5158026 (b : real) (y : real) (h1 : term71 b y) : term71 b y.
Proof. exact (h1). Qed.
Lemma lem5158027 (b : real) (y : real) (h1 : term71 b y) : term529 b y.
Proof. exact (fun h0 : real_le b y => @lem5158026 b y h1). Qed.
Lemma lem5158029 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5158030 (b : real) (y : real) : (term529 b y) = (term71 b y).
Proof. exact (@lem5158029 (real_le b y)). Qed.
Lemma lem5158031 (b : real) (y : real) (h1 : term71 b y) : term71 b y.
Proof. exact (EQ_MP (@lem5158030 b y) (@lem5158027 b y h1)). Qed.
Lemma lem5158042 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5158043 (_67339 : real) (_67338 : real) : (term557 _67338 _67339) = (term454 _67339 _67338).
Proof. exact (@lem5158042 (real_le _67338 _67339) (real_lt _67339 _67338)). Qed.
Lemma lem5158049 (_67339 : real) (_67338 : real) : (term558 _67339 _67338) = (term558 _67339 _67338).
Proof. exact (eq_refl (term558 _67339 _67338)). Qed.
Lemma lem5158050 (_67339 : real) (_67338 : real) : ((term454 _67339 _67338) = (term557 _67338 _67339)) = ((term454 _67339 _67338) = (term454 _67339 _67338)).
Proof. exact (MK_COMB (@lem5158049 _67339 _67338) (@lem5158043 _67339 _67338)). Qed.
Lemma lem5158052 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5158053 (x : Prop) : (x = x) = True.
Proof. exact (@lem5158052 Prop x). Qed.
Lemma lem5158054 (_67339 : real) (_67338 : real) : ((term454 _67339 _67338) = (term454 _67339 _67338)) = True.
Proof. exact (@lem5158053 (term454 _67339 _67338)). Qed.
Lemma lem5158055 (_67338 : real) (_67339 : real) : ((term454 _67339 _67338) = (term557 _67338 _67339)) = True.
Proof. exact (TRANS (@lem5158050 _67339 _67338) (@lem5158054 _67339 _67338)). Qed.
Lemma lem5158056 (_67338 : real) (_67339 : real) : True = ((term454 _67339 _67338) = (term557 _67338 _67339)).
Proof. exact (SYM (@lem5158055 _67338 _67339)). Qed.
Lemma lem5158057 (_67338 : real) (_67339 : real) : (term454 _67339 _67338) = (term557 _67338 _67339).
Proof. exact (EQ_MP (@lem5158056 _67338 _67339) (@lem0)). Qed.
Lemma lem5158058 (_67338 : real) (_67339 : real) (h1 : term35) : term557 _67338 _67339.
Proof. exact (EQ_MP (@lem5158057 _67338 _67339) (@lem5157331 _67339 _67338 h1)). Qed.
Lemma lem5158060 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158063 (_67339 : real) (_67338 : real) : (term557 _67338 _67339) = (term559 _67339 _67338).
Proof. exact (@lem5158060 (real_le _67338 _67339) (real_lt _67339 _67338)). Qed.
Lemma lem5158066 (_67339 : real) (_67338 : real) (h1 : term35) : term559 _67339 _67338.
Proof. exact (EQ_MP (@lem5158063 _67339 _67338) (@lem5158058 _67338 _67339 h1)). Qed.
Lemma lem5158067 (y : real) (b : real) (h1 : term35) : term559 y b.
Proof. exact (@lem5158066 y b h1). Qed.
Lemma lem5158070 (b : real) (y : real) (h1 : term35) (h2 : term71 b y) : real_lt y b.
Proof. exact (@lem5158067 y b h1 (@lem5158031 b y h2)). Qed.
Lemma lem5158071 (b : real) (y : real) (h1 : term35) (h2 : term71 b y) : term560 y b.
Proof. exact (fun h0 : term105 y b => @lem5158070 b y h1 h2). Qed.
Lemma lem5158073 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158074 (y : real) (b : real) : (term560 y b) = (real_lt y b).
Proof. exact (@lem5158073 (real_lt y b)). Qed.
Lemma lem5158075 (b : real) (y : real) (h1 : term35) (h2 : term71 b y) : real_lt y b.
Proof. exact (EQ_MP (@lem5158074 y b) (@lem5158071 b y h1 h2)). Qed.
Lemma lem5158081 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5158082 (x' : real -> real) (s : real -> Prop) (_67335 : real) (b : real) : (term520 b x' _67335 s) = (term561 x' s _67335 b).
Proof. exact (@lem5158081 (term506 x' _67335 s) (term105 _67335 b)). Qed.
Lemma lem5158088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5158089 (x' : real -> real) (s : real -> Prop) (_67335 : real) (b : real) : (term562 b x' _67335 s) = (term563 x' s _67335 b).
Proof. exact (MK_COMB (@lem5158088) (@lem5158082 x' s _67335 b)). Qed.
Lemma lem5158095 (x' : real -> real) (s : real -> Prop) (_67335 : real) (b : real) : (term561 x' s _67335 b) = (term561 x' s _67335 b).
Proof. exact (eq_refl (term561 x' s _67335 b)). Qed.
Lemma lem5158096 (x' : real -> real) (s : real -> Prop) (_67335 : real) (b : real) : ((term520 b x' _67335 s) = (term561 x' s _67335 b)) = ((term561 x' s _67335 b) = (term561 x' s _67335 b)).
Proof. exact (MK_COMB (@lem5158089 x' s _67335 b) (@lem5158095 x' s _67335 b)). Qed.
Lemma lem5158098 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5158099 (x : Prop) : (x = x) = True.
Proof. exact (@lem5158098 Prop x). Qed.
Lemma lem5158100 (x' : real -> real) (s : real -> Prop) (_67335 : real) (b : real) : ((term561 x' s _67335 b) = (term561 x' s _67335 b)) = True.
Proof. exact (@lem5158099 (term561 x' s _67335 b)). Qed.
Lemma lem5158101 (x' : real -> real) (s : real -> Prop) (_67335 : real) (b : real) : ((term520 b x' _67335 s) = (term561 x' s _67335 b)) = True.
Proof. exact (TRANS (@lem5158096 x' s _67335 b) (@lem5158100 x' s _67335 b)). Qed.
Lemma lem5158102 (x' : real -> real) (s : real -> Prop) (_67335 : real) (b : real) : True = ((term520 b x' _67335 s) = (term561 x' s _67335 b)).
Proof. exact (SYM (@lem5158101 x' s _67335 b)). Qed.
Lemma lem5158103 (x' : real -> real) (s : real -> Prop) (_67335 : real) (b : real) : (term520 b x' _67335 s) = (term561 x' s _67335 b).
Proof. exact (EQ_MP (@lem5158102 x' s _67335 b) (@lem0)). Qed.
Lemma lem5158104 (_67335 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term561 x' s _67335 b.
Proof. exact (EQ_MP (@lem5158103 x' s _67335 b) (@lem5157381 _67335 b s x' h1)). Qed.
Lemma lem5158106 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158107 (b : real) (x' : real -> real) (_67335 : real) (s : real -> Prop) : (term561 x' s _67335 b) = (term564 b x' _67335 s).
Proof. exact (@lem5158106 (term105 _67335 b) (term506 x' _67335 s)). Qed.
Lemma lem5158109 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5158110 (_67335 : real) (b : real) : (term565 _67335 b) = (real_lt _67335 b).
Proof. exact (@lem5158109 (real_lt _67335 b)). Qed.
Lemma lem5158111 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5158112 (_67335 : real) (b : real) : (term566 _67335 b) = (term89 _67335 b).
Proof. exact (MK_COMB (@lem5158111) (@lem5158110 _67335 b)). Qed.
Lemma lem5158113 (x' : real -> real) (_67335 : real) (s : real -> Prop) : (term506 x' _67335 s) = (term506 x' _67335 s).
Proof. exact (eq_refl (term506 x' _67335 s)). Qed.
Lemma lem5158114 (b : real) (x' : real -> real) (_67335 : real) (s : real -> Prop) : (term564 b x' _67335 s) = (term567 b x' _67335 s).
Proof. exact (MK_COMB (@lem5158112 _67335 b) (@lem5158113 x' _67335 s)). Qed.
Lemma lem5158115 (b : real) (x' : real -> real) (_67335 : real) (s : real -> Prop) : (term561 x' s _67335 b) = (term567 b x' _67335 s).
Proof. exact (TRANS (@lem5158107 b x' _67335 s) (@lem5158114 b x' _67335 s)). Qed.
Lemma lem5158118 (_67335 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term567 b x' _67335 s.
Proof. exact (EQ_MP (@lem5158115 b x' _67335 s) (@lem5158104 _67335 b s x' h1)). Qed.
Lemma lem5158119 (y : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term567 b x' y s.
Proof. exact (@lem5158118 y b s x' h1). Qed.
Lemma lem5158122 (s : real -> Prop) (x' : real -> real) (b : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) : term506 x' y s.
Proof. exact (@lem5158119 y b s x' h2 (@lem5158075 b y h1 h3)). Qed.
Lemma lem5158123 (s : real -> Prop) (x' : real -> real) (b : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) : term533 x' y s.
Proof. exact (fun h0 : term534 x' y s => @lem5158122 s x' b y h1 h2 h3). Qed.
Lemma lem5158125 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158126 (x' : real -> real) (y : real) (s : real -> Prop) : (term533 x' y s) = (term506 x' y s).
Proof. exact (@lem5158125 (term506 x' y s)). Qed.
Lemma lem5158127 (s : real -> Prop) (x' : real -> real) (b : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) : term506 x' y s.
Proof. exact (EQ_MP (@lem5158126 x' y s) (@lem5158123 s x' b y h1 h2 h3)). Qed.
Lemma lem5158133 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5158134 (y : real) (_67344 : real) (s : real -> Prop) : (term92 s _67344 y) = (term536 y _67344 s).
Proof. exact (@lem5158133 (real_le _67344 y) (term537 _67344 s)). Qed.
Lemma lem5158140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5158141 (y : real) (_67344 : real) (s : real -> Prop) : (term538 s _67344 y) = (term539 y _67344 s).
Proof. exact (MK_COMB (@lem5158140) (@lem5158134 y _67344 s)). Qed.
Lemma lem5158147 (y : real) (_67344 : real) (s : real -> Prop) : (term536 y _67344 s) = (term536 y _67344 s).
Proof. exact (eq_refl (term536 y _67344 s)). Qed.
Lemma lem5158148 (y : real) (_67344 : real) (s : real -> Prop) : ((term92 s _67344 y) = (term536 y _67344 s)) = ((term536 y _67344 s) = (term536 y _67344 s)).
Proof. exact (MK_COMB (@lem5158141 y _67344 s) (@lem5158147 y _67344 s)). Qed.
Lemma lem5158150 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5158151 (x : Prop) : (x = x) = True.
Proof. exact (@lem5158150 Prop x). Qed.
Lemma lem5158152 (y : real) (_67344 : real) (s : real -> Prop) : ((term536 y _67344 s) = (term536 y _67344 s)) = True.
Proof. exact (@lem5158151 (term536 y _67344 s)). Qed.
Lemma lem5158153 (y : real) (_67344 : real) (s : real -> Prop) : ((term92 s _67344 y) = (term536 y _67344 s)) = True.
Proof. exact (TRANS (@lem5158148 y _67344 s) (@lem5158152 y _67344 s)). Qed.
Lemma lem5158154 (y : real) (_67344 : real) (s : real -> Prop) : True = ((term92 s _67344 y) = (term536 y _67344 s)).
Proof. exact (SYM (@lem5158153 y _67344 s)). Qed.
Lemma lem5158155 (y : real) (_67344 : real) (s : real -> Prop) : (term92 s _67344 y) = (term536 y _67344 s).
Proof. exact (EQ_MP (@lem5158154 y _67344 s) (@lem0)). Qed.
Lemma lem5158156 (_67344 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term536 y _67344 s.
Proof. exact (EQ_MP (@lem5158155 y _67344 s) (@lem5157351 _67344 s x y b h1)). Qed.
Lemma lem5158158 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158159 (s : real -> Prop) (_67344 : real) (y : real) : (term536 y _67344 s) = (term540 s _67344 y).
Proof. exact (@lem5158158 (term537 _67344 s) (real_le _67344 y)). Qed.
Lemma lem5158161 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5158162 (_67344 : real) (s : real -> Prop) : (term542 _67344 s) = (@IN real _67344 s).
Proof. exact (@lem5158161 (@IN real _67344 s)). Qed.
Lemma lem5158163 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5158164 (_67344 : real) (s : real -> Prop) : (term543 _67344 s) = (term544 _67344 s).
Proof. exact (MK_COMB (@lem5158163) (@lem5158162 _67344 s)). Qed.
Lemma lem5158165 (_67344 : real) (y : real) : (real_le _67344 y) = (real_le _67344 y).
Proof. exact (eq_refl (real_le _67344 y)). Qed.
Lemma lem5158166 (s : real -> Prop) (_67344 : real) (y : real) : (term540 s _67344 y) = (term80 s _67344 y).
Proof. exact (MK_COMB (@lem5158164 _67344 s) (@lem5158165 _67344 y)). Qed.
Lemma lem5158167 (s : real -> Prop) (_67344 : real) (y : real) : (term536 y _67344 s) = (term80 s _67344 y).
Proof. exact (TRANS (@lem5158159 s _67344 y) (@lem5158166 s _67344 y)). Qed.
Lemma lem5158170 (_67344 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term80 s _67344 y.
Proof. exact (EQ_MP (@lem5158167 s _67344 y) (@lem5158156 _67344 s x y b h1)). Qed.
Lemma lem5158171 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term545 s x' y.
Proof. exact (@lem5158170 (x' y) s x y b h1). Qed.
Lemma lem5158174 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) (h4 : term295 s x y b) : term546 x' y.
Proof. exact (@lem5158171 x' s x y b h4 (@lem5158127 s x' b y h1 h2 h3)). Qed.
Lemma lem5158175 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) (h4 : term295 s x y b) : term547 x' y.
Proof. exact (fun h0 : term511 x' y => @lem5158174 x' s x y b h1 h2 h3 h4). Qed.
Lemma lem5158177 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158178 (x' : real -> real) (y : real) : (term547 x' y) = (term546 x' y).
Proof. exact (@lem5158177 (term546 x' y)). Qed.
Lemma lem5158179 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) (h4 : term295 s x y b) : term546 x' y.
Proof. exact (EQ_MP (@lem5158178 x' y) (@lem5158175 x' s x y b h1 h2 h3 h4)). Qed.
Lemma lem5158190 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5158191 (_67337 : real) (_67336 : real) : (term568 _67336 _67337) = (term467 _67337 _67336).
Proof. exact (@lem5158190 (term71 _67336 _67337) (term105 _67337 _67336)). Qed.
Lemma lem5158197 (_67337 : real) (_67336 : real) : (term569 _67337 _67336) = (term569 _67337 _67336).
Proof. exact (eq_refl (term569 _67337 _67336)). Qed.
Lemma lem5158198 (_67337 : real) (_67336 : real) : ((term467 _67337 _67336) = (term568 _67336 _67337)) = ((term467 _67337 _67336) = (term467 _67337 _67336)).
Proof. exact (MK_COMB (@lem5158197 _67337 _67336) (@lem5158191 _67337 _67336)). Qed.
Lemma lem5158200 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5158201 (x : Prop) : (x = x) = True.
Proof. exact (@lem5158200 Prop x). Qed.
Lemma lem5158202 (_67337 : real) (_67336 : real) : ((term467 _67337 _67336) = (term467 _67337 _67336)) = True.
Proof. exact (@lem5158201 (term467 _67337 _67336)). Qed.
Lemma lem5158203 (_67336 : real) (_67337 : real) : ((term467 _67337 _67336) = (term568 _67336 _67337)) = True.
Proof. exact (TRANS (@lem5158198 _67337 _67336) (@lem5158202 _67337 _67336)). Qed.
Lemma lem5158204 (_67336 : real) (_67337 : real) : True = ((term467 _67337 _67336) = (term568 _67336 _67337)).
Proof. exact (SYM (@lem5158203 _67336 _67337)). Qed.
Lemma lem5158205 (_67336 : real) (_67337 : real) : (term467 _67337 _67336) = (term568 _67336 _67337).
Proof. exact (EQ_MP (@lem5158204 _67336 _67337) (@lem0)). Qed.
Lemma lem5158206 (_67336 : real) (_67337 : real) (h1 : term35) : term568 _67336 _67337.
Proof. exact (EQ_MP (@lem5158205 _67336 _67337) (@lem5157325 _67337 _67336 h1)). Qed.
Lemma lem5158208 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158209 (_67337 : real) (_67336 : real) : (term568 _67336 _67337) = (term570 _67337 _67336).
Proof. exact (@lem5158208 (term71 _67336 _67337) (term105 _67337 _67336)). Qed.
Lemma lem5158211 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5158212 (_67336 : real) (_67337 : real) : (term450 _67336 _67337) = (real_le _67336 _67337).
Proof. exact (@lem5158211 (real_le _67336 _67337)). Qed.
Lemma lem5158213 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5158214 (_67336 : real) (_67337 : real) : (term571 _67336 _67337) = (term572 _67336 _67337).
Proof. exact (MK_COMB (@lem5158213) (@lem5158212 _67336 _67337)). Qed.
Lemma lem5158215 (_67337 : real) (_67336 : real) : (term105 _67337 _67336) = (term105 _67337 _67336).
Proof. exact (eq_refl (term105 _67337 _67336)). Qed.
Lemma lem5158216 (_67337 : real) (_67336 : real) : (term570 _67337 _67336) = (term573 _67337 _67336).
Proof. exact (MK_COMB (@lem5158214 _67336 _67337) (@lem5158215 _67337 _67336)). Qed.
Lemma lem5158217 (_67337 : real) (_67336 : real) : (term568 _67336 _67337) = (term573 _67337 _67336).
Proof. exact (TRANS (@lem5158209 _67337 _67336) (@lem5158216 _67337 _67336)). Qed.
Lemma lem5158220 (_67337 : real) (_67336 : real) (h1 : term35) : term573 _67337 _67336.
Proof. exact (EQ_MP (@lem5158217 _67337 _67336) (@lem5158206 _67336 _67337 h1)). Qed.
Lemma lem5158221 (x' : real -> real) (y : real) (h1 : term35) : term574 x' y.
Proof. exact (@lem5158220 y (x' y) h1). Qed.
Lemma lem5158224 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) (h4 : term295 s x y b) : term575 x' y.
Proof. exact (@lem5158221 x' y h1 (@lem5158179 x' s x y b h1 h2 h3 h4)). Qed.
Lemma lem5158225 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) (h4 : term295 s x y b) : term576 x' y.
Proof. exact (fun h0 : term507 x' y => @lem5158224 x' s x y b h1 h2 h3 h4). Qed.
Lemma lem5158227 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5158228 (x' : real -> real) (y : real) : (term576 x' y) = (term575 x' y).
Proof. exact (@lem5158227 (term507 x' y)). Qed.
Lemma lem5158229 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) (h4 : term295 s x y b) : term575 x' y.
Proof. exact (EQ_MP (@lem5158228 x' y) (@lem5158225 x' s x y b h1 h2 h3 h4)). Qed.
Lemma lem5158231 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158234 (x' : real -> real) (_67335 : real) (b : real) : (term521 b x' _67335) = (term577 x' _67335 b).
Proof. exact (@lem5158231 (term507 x' _67335) (term105 _67335 b)). Qed.
Lemma lem5158237 (_67335 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term577 x' _67335 b.
Proof. exact (EQ_MP (@lem5158234 x' _67335 b) (@lem5157387 _67335 b s x' h1)). Qed.
Lemma lem5158238 (y : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term577 x' y b.
Proof. exact (@lem5158237 y b s x' h1). Qed.
Lemma lem5158241 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) (h4 : term295 s x y b) : term105 y b.
Proof. exact (@lem5158238 y b s x' h2 (@lem5158229 x' s x y b h1 h2 h3 h4)). Qed.
Lemma lem5158242 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) (h4 : term295 s x y b) : term578 y b.
Proof. exact (fun h0 : real_lt y b => @lem5158241 x' s x y b h1 h2 h3 h4). Qed.
Lemma lem5158244 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5158245 (y : real) (b : real) : (term578 y b) = (term105 y b).
Proof. exact (@lem5158244 (real_lt y b)). Qed.
Lemma lem5158246 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) (h4 : term295 s x y b) : term105 y b.
Proof. exact (EQ_MP (@lem5158245 y b) (@lem5158242 x' s x y b h1 h2 h3 h4)). Qed.
Lemma lem5158248 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158251 (_67338 : real) (_67339 : real) : (term454 _67339 _67338) = (term579 _67338 _67339).
Proof. exact (@lem5158248 (real_lt _67339 _67338) (real_le _67338 _67339)). Qed.
Lemma lem5158254 (_67338 : real) (_67339 : real) (h1 : term35) : term579 _67338 _67339.
Proof. exact (EQ_MP (@lem5158251 _67338 _67339) (@lem5157331 _67339 _67338 h1)). Qed.
Lemma lem5158255 (b : real) (y : real) (h1 : term35) : term579 b y.
Proof. exact (@lem5158254 b y h1). Qed.
Lemma lem5158258 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b y) (h4 : term295 s x y b) : real_le b y.
Proof. exact (@lem5158255 b y h1 (@lem5158246 x' s x y b h1 h2 h3 h4)). Qed.
Lemma lem5158259 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term295 s x y b) : term556 b y.
Proof. exact (fun h0 : term71 b y => @lem5158258 x' s x y b h1 h2 h0 h3). Qed.
Lemma lem5158261 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158262 (b : real) (y : real) : (term556 b y) = (real_le b y).
Proof. exact (@lem5158261 (real_le b y)). Qed.
Lemma lem5158263 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term295 s x y b) : real_le b y.
Proof. exact (EQ_MP (@lem5158262 b y) (@lem5158259 x' s x y b h1 h2 h3)). Qed.
Lemma lem5158279 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5158280 (_67343 : real) (_67342 : real) : (term580 _67342 _67343) = (term581 _67343 _67342).
Proof. exact (@lem5158279 (_67342 = _67343) (term71 _67343 _67342)). Qed.
Lemma lem5158288 (_67342 : real) (_67343 : real) : (term582 _67342 _67343) = (term582 _67342 _67343).
Proof. exact (eq_refl (term582 _67342 _67343)). Qed.
Lemma lem5158289 (_67343 : real) (_67342 : real) : (term517 _67342 _67343) = (term583 _67343 _67342).
Proof. exact (MK_COMB (@lem5158288 _67342 _67343) (@lem5158280 _67343 _67342)). Qed.
Lemma lem5158293 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5158294 (_67343 : real) (_67342 : real) : (term583 _67343 _67342) = (term584 _67343 _67342).
Proof. exact (@lem5158293 (_67342 = _67343) (term71 _67342 _67343) (term71 _67343 _67342)). Qed.
Lemma lem5158312 (_67343 : real) (_67342 : real) : (term517 _67342 _67343) = (term584 _67343 _67342).
Proof. exact (TRANS (@lem5158289 _67343 _67342) (@lem5158294 _67343 _67342)). Qed.
Lemma lem5158313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5158314 (_67343 : real) (_67342 : real) : (term585 _67342 _67343) = (term586 _67343 _67342).
Proof. exact (MK_COMB (@lem5158313) (@lem5158312 _67343 _67342)). Qed.
Lemma lem5158332 (_67343 : real) (_67342 : real) : (term584 _67343 _67342) = (term584 _67343 _67342).
Proof. exact (eq_refl (term584 _67343 _67342)). Qed.
Lemma lem5158333 (_67343 : real) (_67342 : real) : ((term517 _67342 _67343) = (term584 _67343 _67342)) = ((term584 _67343 _67342) = (term584 _67343 _67342)).
Proof. exact (MK_COMB (@lem5158314 _67343 _67342) (@lem5158332 _67343 _67342)). Qed.
Lemma lem5158335 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5158336 (x : Prop) : (x = x) = True.
Proof. exact (@lem5158335 Prop x). Qed.
Lemma lem5158337 (_67343 : real) (_67342 : real) : ((term584 _67343 _67342) = (term584 _67343 _67342)) = True.
Proof. exact (@lem5158336 (term584 _67343 _67342)). Qed.
Lemma lem5158338 (_67343 : real) (_67342 : real) : ((term517 _67342 _67343) = (term584 _67343 _67342)) = True.
Proof. exact (TRANS (@lem5158333 _67343 _67342) (@lem5158337 _67343 _67342)). Qed.
Lemma lem5158339 (_67343 : real) (_67342 : real) : True = ((term517 _67342 _67343) = (term584 _67343 _67342)).
Proof. exact (SYM (@lem5158338 _67343 _67342)). Qed.
Lemma lem5158340 (_67343 : real) (_67342 : real) : (term517 _67342 _67343) = (term584 _67343 _67342).
Proof. exact (EQ_MP (@lem5158339 _67343 _67342) (@lem0)). Qed.
Lemma lem5158341 (_67343 : real) (_67342 : real) (h1 : term79) : term584 _67343 _67342.
Proof. exact (EQ_MP (@lem5158340 _67343 _67342) (@lem5157343 _67342 _67343 h1)). Qed.
Lemma lem5158343 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158344 (_67342 : real) (_67343 : real) : (term584 _67343 _67342) = (term587 _67342 _67343).
Proof. exact (@lem5158343 (term391 _67343 _67342) (_67342 = _67343)). Qed.
Lemma lem5158346 (a : Prop) (b : Prop) : (term588 a b) = (term589 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5158347 (_67343 : real) (_67342 : real) : (term590 _67343 _67342) = (term591 _67343 _67342).
Proof. exact (@lem5158346 (term71 _67342 _67343) (term71 _67343 _67342)). Qed.
Lemma lem5158349 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5158350 (_67342 : real) (_67343 : real) : (term450 _67342 _67343) = (real_le _67342 _67343).
Proof. exact (@lem5158349 (real_le _67342 _67343)). Qed.
Lemma lem5158351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5158352 (_67342 : real) (_67343 : real) : (term592 _67342 _67343) = (term593 _67342 _67343).
Proof. exact (MK_COMB (@lem5158351) (@lem5158350 _67342 _67343)). Qed.
Lemma lem5158354 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5158355 (_67343 : real) (_67342 : real) : (term450 _67343 _67342) = (real_le _67343 _67342).
Proof. exact (@lem5158354 (real_le _67343 _67342)). Qed.
Lemma lem5158356 (_67343 : real) (_67342 : real) : (term591 _67343 _67342) = (term75 _67343 _67342).
Proof. exact (MK_COMB (@lem5158352 _67342 _67343) (@lem5158355 _67343 _67342)). Qed.
Lemma lem5158357 (_67343 : real) (_67342 : real) : (term590 _67343 _67342) = (term75 _67343 _67342).
Proof. exact (TRANS (@lem5158347 _67343 _67342) (@lem5158356 _67343 _67342)). Qed.
Lemma lem5158358 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5158359 (_67343 : real) (_67342 : real) : (term594 _67343 _67342) = (term595 _67343 _67342).
Proof. exact (MK_COMB (@lem5158358) (@lem5158357 _67343 _67342)). Qed.
Lemma lem5158360 (_67342 : real) (_67343 : real) : (_67342 = _67343) = (_67342 = _67343).
Proof. exact (eq_refl (_67342 = _67343)). Qed.
Lemma lem5158361 (_67342 : real) (_67343 : real) : (term587 _67342 _67343) = (term596 _67342 _67343).
Proof. exact (MK_COMB (@lem5158359 _67343 _67342) (@lem5158360 _67342 _67343)). Qed.
Lemma lem5158362 (_67342 : real) (_67343 : real) : (term584 _67343 _67342) = (term596 _67342 _67343).
Proof. exact (TRANS (@lem5158344 _67342 _67343) (@lem5158361 _67342 _67343)). Qed.
Lemma lem5158364 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term19 s b) (h3 : term139 b s x') (h4 : term295 s x y b) : term75 b y.
Proof. exact (conj (@lem5158023 s x y b h2 h4) (@lem5158263 x' s x y b h1 h3 h4)). Qed.
Lemma lem5158366 (_67342 : real) (_67343 : real) (h1 : term79) : term596 _67342 _67343.
Proof. exact (EQ_MP (@lem5158362 _67342 _67343) (@lem5158341 _67343 _67342 h1)). Qed.
Lemma lem5158367 (y : real) (b : real) (h1 : term79) : term596 y b.
Proof. exact (@lem5158366 y b h1). Qed.
Lemma lem5158370 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term295 s x y b) : y = b.
Proof. exact (@lem5158367 y b h2 (@lem5158364 x' s x y b h1 h3 h4 h5)). Qed.
Lemma lem5158371 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term295 s x y b) : term597 y b.
Proof. exact (fun h0 : term175 y b => @lem5158370 x' s x y b h1 h2 h3 h4 h5). Qed.
Lemma lem5158373 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158374 (y : real) (b : real) : (term597 y b) = (y = b).
Proof. exact (@lem5158373 (y = b)). Qed.
Lemma lem5158375 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term295 s x y b) : y = b.
Proof. exact (EQ_MP (@lem5158374 y b) (@lem5158371 x' s x y b h1 h2 h3 h4 h5)). Qed.
Lemma lem5158378 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5158380 (y : real) (b : real) : (term175 y b) = (term598 y b).
Proof. exact (@lem5158378 (y = b)). Qed.
Lemma lem5158383 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term598 y b.
Proof. exact (EQ_MP (@lem5158380 y b) (@lem5157345 s x y b h1)). Qed.
Lemma lem5158386 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term295 s x y b) : False.
Proof. exact (@lem5158383 s x y b h5 (@lem5158375 x' s x y b h1 h2 h3 h4 h5)). Qed.
Lemma lem5158387 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term295 s x y b) : term599.
Proof. exact (fun h0 : ~ False => @lem5158386 x' s x y b h1 h2 h3 h4 h5). Qed.
Lemma lem5158389 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158390 : term599 = False.
Proof. exact (@lem5158389 False). Qed.
Lemma lem5158391 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term295 s x y b) : False.
Proof. exact (EQ_MP (@lem5158390) (@lem5158387 x' s x y b h1 h2 h3 h4 h5)). Qed.
Lemma lem5158462 (s : real -> Prop) (b' : real) (y : real) (h1 : term144 s b' y) : @IN real b' s.
Proof. exact (proj1 (@lem5156774 s b' y h1)). Qed.
Lemma lem5158463 (s : real -> Prop) (b' : real) (y : real) (h1 : term144 s b' y) : term600 b' s.
Proof. exact (fun h0 : term537 b' s => @lem5158462 s b' y h1). Qed.
Lemma lem5158465 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158466 (b' : real) (s : real -> Prop) : (term600 b' s) = (@IN real b' s).
Proof. exact (@lem5158465 (@IN real b' s)). Qed.
Lemma lem5158467 (s : real -> Prop) (b' : real) (y : real) (h1 : term144 s b' y) : @IN real b' s.
Proof. exact (EQ_MP (@lem5158466 b' s) (@lem5158463 s b' y h1)). Qed.
Lemma lem5158473 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5158474 (b : real) (_67346 : real) (s : real -> Prop) : (term92 s _67346 b) = (term536 b _67346 s).
Proof. exact (@lem5158473 (real_le _67346 b) (term537 _67346 s)). Qed.
Lemma lem5158480 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5158481 (b : real) (_67346 : real) (s : real -> Prop) : (term538 s _67346 b) = (term539 b _67346 s).
Proof. exact (MK_COMB (@lem5158480) (@lem5158474 b _67346 s)). Qed.
Lemma lem5158487 (b : real) (_67346 : real) (s : real -> Prop) : (term536 b _67346 s) = (term536 b _67346 s).
Proof. exact (eq_refl (term536 b _67346 s)). Qed.
Lemma lem5158488 (b : real) (_67346 : real) (s : real -> Prop) : ((term92 s _67346 b) = (term536 b _67346 s)) = ((term536 b _67346 s) = (term536 b _67346 s)).
Proof. exact (MK_COMB (@lem5158481 b _67346 s) (@lem5158487 b _67346 s)). Qed.
Lemma lem5158490 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5158491 (x : Prop) : (x = x) = True.
Proof. exact (@lem5158490 Prop x). Qed.
Lemma lem5158492 (b : real) (_67346 : real) (s : real -> Prop) : ((term536 b _67346 s) = (term536 b _67346 s)) = True.
Proof. exact (@lem5158491 (term536 b _67346 s)). Qed.
Lemma lem5158493 (b : real) (_67346 : real) (s : real -> Prop) : ((term92 s _67346 b) = (term536 b _67346 s)) = True.
Proof. exact (TRANS (@lem5158488 b _67346 s) (@lem5158492 b _67346 s)). Qed.
Lemma lem5158494 (b : real) (_67346 : real) (s : real -> Prop) : True = ((term92 s _67346 b) = (term536 b _67346 s)).
Proof. exact (SYM (@lem5158493 b _67346 s)). Qed.
Lemma lem5158495 (b : real) (_67346 : real) (s : real -> Prop) : (term92 s _67346 b) = (term536 b _67346 s).
Proof. exact (EQ_MP (@lem5158494 b _67346 s) (@lem0)). Qed.
Lemma lem5158496 (_67346 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term536 b _67346 s.
Proof. exact (EQ_MP (@lem5158495 b _67346 s) (@lem5157539 _67346 s b h1)). Qed.
Lemma lem5158498 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158499 (s : real -> Prop) (_67346 : real) (b : real) : (term536 b _67346 s) = (term540 s _67346 b).
Proof. exact (@lem5158498 (term537 _67346 s) (real_le _67346 b)). Qed.
Lemma lem5158501 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5158502 (_67346 : real) (s : real -> Prop) : (term542 _67346 s) = (@IN real _67346 s).
Proof. exact (@lem5158501 (@IN real _67346 s)). Qed.
Lemma lem5158503 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5158504 (_67346 : real) (s : real -> Prop) : (term543 _67346 s) = (term544 _67346 s).
Proof. exact (MK_COMB (@lem5158503) (@lem5158502 _67346 s)). Qed.
Lemma lem5158505 (_67346 : real) (b : real) : (real_le _67346 b) = (real_le _67346 b).
Proof. exact (eq_refl (real_le _67346 b)). Qed.
Lemma lem5158506 (s : real -> Prop) (_67346 : real) (b : real) : (term540 s _67346 b) = (term80 s _67346 b).
Proof. exact (MK_COMB (@lem5158504 _67346 s) (@lem5158505 _67346 b)). Qed.
Lemma lem5158507 (s : real -> Prop) (_67346 : real) (b : real) : (term536 b _67346 s) = (term80 s _67346 b).
Proof. exact (TRANS (@lem5158499 s _67346 b) (@lem5158506 s _67346 b)). Qed.
Lemma lem5158510 (_67346 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term80 s _67346 b.
Proof. exact (EQ_MP (@lem5158507 s _67346 b) (@lem5158496 _67346 s b h1)). Qed.
Lemma lem5158511 (b' : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term80 s b' b.
Proof. exact (@lem5158510 b' s b h1). Qed.
Lemma lem5158514 (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term19 s b) (h2 : term144 s b' y) : real_le b' b.
Proof. exact (@lem5158511 b' s b h1 (@lem5158467 s b' y h2)). Qed.
Lemma lem5158515 (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term19 s b) (h2 : term144 s b' y) : term556 b' b.
Proof. exact (fun h0 : term71 b' b => @lem5158514 b s b' y h1 h2). Qed.
Lemma lem5158517 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158518 (b' : real) (b : real) : (term556 b' b) = (real_le b' b).
Proof. exact (@lem5158517 (real_le b' b)). Qed.
Lemma lem5158519 (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term19 s b) (h2 : term144 s b' y) : real_le b' b.
Proof. exact (EQ_MP (@lem5158518 b' b) (@lem5158515 b s b' y h1 h2)). Qed.
Lemma lem5158522 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5158524 (b' : real) (b : real) : (term71 b' b) = (term601 b' b).
Proof. exact (@lem5158522 (real_le b' b)). Qed.
Lemma lem5158527 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term144 s b' y) (h2 : term332 s b' y b) : term601 b' b.
Proof. exact (EQ_MP (@lem5158524 b' b) (@lem5157608 s b' y b h1 h2)). Qed.
Lemma lem5158530 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term19 s b) (h2 : term144 s b' y) (h3 : term332 s b' y b) : False.
Proof. exact (@lem5158527 s b' y b h2 h3 (@lem5158519 b s b' y h1 h2)). Qed.
Lemma lem5158531 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term19 s b) (h2 : term144 s b' y) (h3 : term332 s b' y b) : term599.
Proof. exact (fun h0 : ~ False => @lem5158530 s b' y b h1 h2 h3). Qed.
Lemma lem5158533 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158534 : term599 = False.
Proof. exact (@lem5158533 False). Qed.
Lemma lem5158607 (b : real) (b' : real) (h1 : term71 b b') : term71 b b'.
Proof. exact (h1). Qed.
Lemma lem5158608 (b : real) (b' : real) (h1 : term71 b b') : term529 b b'.
Proof. exact (fun h0 : real_le b b' => @lem5158607 b b' h1). Qed.
Lemma lem5158610 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5158611 (b : real) (b' : real) : (term529 b b') = (term71 b b').
Proof. exact (@lem5158610 (real_le b b')). Qed.
Lemma lem5158612 (b : real) (b' : real) (h1 : term71 b b') : term71 b b'.
Proof. exact (EQ_MP (@lem5158611 b b') (@lem5158608 b b' h1)). Qed.
Lemma lem5158623 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5158624 (_67361 : real) (_67360 : real) : (term557 _67360 _67361) = (term454 _67361 _67360).
Proof. exact (@lem5158623 (real_le _67360 _67361) (real_lt _67361 _67360)). Qed.
Lemma lem5158630 (_67361 : real) (_67360 : real) : (term558 _67361 _67360) = (term558 _67361 _67360).
Proof. exact (eq_refl (term558 _67361 _67360)). Qed.
Lemma lem5158631 (_67361 : real) (_67360 : real) : ((term454 _67361 _67360) = (term557 _67360 _67361)) = ((term454 _67361 _67360) = (term454 _67361 _67360)).
Proof. exact (MK_COMB (@lem5158630 _67361 _67360) (@lem5158624 _67361 _67360)). Qed.
Lemma lem5158633 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5158634 (x : Prop) : (x = x) = True.
Proof. exact (@lem5158633 Prop x). Qed.
Lemma lem5158635 (_67361 : real) (_67360 : real) : ((term454 _67361 _67360) = (term454 _67361 _67360)) = True.
Proof. exact (@lem5158634 (term454 _67361 _67360)). Qed.
Lemma lem5158636 (_67360 : real) (_67361 : real) : ((term454 _67361 _67360) = (term557 _67360 _67361)) = True.
Proof. exact (TRANS (@lem5158631 _67361 _67360) (@lem5158635 _67361 _67360)). Qed.
Lemma lem5158637 (_67360 : real) (_67361 : real) : True = ((term454 _67361 _67360) = (term557 _67360 _67361)).
Proof. exact (SYM (@lem5158636 _67360 _67361)). Qed.
Lemma lem5158638 (_67360 : real) (_67361 : real) : (term454 _67361 _67360) = (term557 _67360 _67361).
Proof. exact (EQ_MP (@lem5158637 _67360 _67361) (@lem0)). Qed.
Lemma lem5158639 (_67360 : real) (_67361 : real) (h1 : term35) : term557 _67360 _67361.
Proof. exact (EQ_MP (@lem5158638 _67360 _67361) (@lem5157720 _67361 _67360 h1)). Qed.
Lemma lem5158641 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158644 (_67361 : real) (_67360 : real) : (term557 _67360 _67361) = (term559 _67361 _67360).
Proof. exact (@lem5158641 (real_le _67360 _67361) (real_lt _67361 _67360)). Qed.
Lemma lem5158647 (_67361 : real) (_67360 : real) (h1 : term35) : term559 _67361 _67360.
Proof. exact (EQ_MP (@lem5158644 _67361 _67360) (@lem5158639 _67360 _67361 h1)). Qed.
Lemma lem5158648 (b' : real) (b : real) (h1 : term35) : term559 b' b.
Proof. exact (@lem5158647 b' b h1). Qed.
Lemma lem5158651 (b : real) (b' : real) (h1 : term35) (h2 : term71 b b') : real_lt b' b.
Proof. exact (@lem5158648 b' b h1 (@lem5158612 b b' h2)). Qed.
Lemma lem5158652 (b : real) (b' : real) (h1 : term35) (h2 : term71 b b') : term560 b' b.
Proof. exact (fun h0 : term105 b' b => @lem5158651 b b' h1 h2). Qed.
Lemma lem5158654 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158655 (b' : real) (b : real) : (term560 b' b) = (real_lt b' b).
Proof. exact (@lem5158654 (real_lt b' b)). Qed.
Lemma lem5158656 (b : real) (b' : real) (h1 : term35) (h2 : term71 b b') : real_lt b' b.
Proof. exact (EQ_MP (@lem5158655 b' b) (@lem5158652 b b' h1 h2)). Qed.
Lemma lem5158662 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5158663 (x' : real -> real) (s : real -> Prop) (_67357 : real) (b : real) : (term520 b x' _67357 s) = (term561 x' s _67357 b).
Proof. exact (@lem5158662 (term506 x' _67357 s) (term105 _67357 b)). Qed.
Lemma lem5158669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5158670 (x' : real -> real) (s : real -> Prop) (_67357 : real) (b : real) : (term562 b x' _67357 s) = (term563 x' s _67357 b).
Proof. exact (MK_COMB (@lem5158669) (@lem5158663 x' s _67357 b)). Qed.
Lemma lem5158676 (x' : real -> real) (s : real -> Prop) (_67357 : real) (b : real) : (term561 x' s _67357 b) = (term561 x' s _67357 b).
Proof. exact (eq_refl (term561 x' s _67357 b)). Qed.
Lemma lem5158677 (x' : real -> real) (s : real -> Prop) (_67357 : real) (b : real) : ((term520 b x' _67357 s) = (term561 x' s _67357 b)) = ((term561 x' s _67357 b) = (term561 x' s _67357 b)).
Proof. exact (MK_COMB (@lem5158670 x' s _67357 b) (@lem5158676 x' s _67357 b)). Qed.
Lemma lem5158679 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5158680 (x : Prop) : (x = x) = True.
Proof. exact (@lem5158679 Prop x). Qed.
Lemma lem5158681 (x' : real -> real) (s : real -> Prop) (_67357 : real) (b : real) : ((term561 x' s _67357 b) = (term561 x' s _67357 b)) = True.
Proof. exact (@lem5158680 (term561 x' s _67357 b)). Qed.
Lemma lem5158682 (x' : real -> real) (s : real -> Prop) (_67357 : real) (b : real) : ((term520 b x' _67357 s) = (term561 x' s _67357 b)) = True.
Proof. exact (TRANS (@lem5158677 x' s _67357 b) (@lem5158681 x' s _67357 b)). Qed.
Lemma lem5158683 (x' : real -> real) (s : real -> Prop) (_67357 : real) (b : real) : True = ((term520 b x' _67357 s) = (term561 x' s _67357 b)).
Proof. exact (SYM (@lem5158682 x' s _67357 b)). Qed.
Lemma lem5158684 (x' : real -> real) (s : real -> Prop) (_67357 : real) (b : real) : (term520 b x' _67357 s) = (term561 x' s _67357 b).
Proof. exact (EQ_MP (@lem5158683 x' s _67357 b) (@lem0)). Qed.
Lemma lem5158685 (_67357 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term561 x' s _67357 b.
Proof. exact (EQ_MP (@lem5158684 x' s _67357 b) (@lem5157803 _67357 b s x' h1)). Qed.
Lemma lem5158687 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158688 (b : real) (x' : real -> real) (_67357 : real) (s : real -> Prop) : (term561 x' s _67357 b) = (term564 b x' _67357 s).
Proof. exact (@lem5158687 (term105 _67357 b) (term506 x' _67357 s)). Qed.
Lemma lem5158690 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5158691 (_67357 : real) (b : real) : (term565 _67357 b) = (real_lt _67357 b).
Proof. exact (@lem5158690 (real_lt _67357 b)). Qed.
Lemma lem5158692 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5158693 (_67357 : real) (b : real) : (term566 _67357 b) = (term89 _67357 b).
Proof. exact (MK_COMB (@lem5158692) (@lem5158691 _67357 b)). Qed.
Lemma lem5158694 (x' : real -> real) (_67357 : real) (s : real -> Prop) : (term506 x' _67357 s) = (term506 x' _67357 s).
Proof. exact (eq_refl (term506 x' _67357 s)). Qed.
Lemma lem5158695 (b : real) (x' : real -> real) (_67357 : real) (s : real -> Prop) : (term564 b x' _67357 s) = (term567 b x' _67357 s).
Proof. exact (MK_COMB (@lem5158693 _67357 b) (@lem5158694 x' _67357 s)). Qed.
Lemma lem5158696 (b : real) (x' : real -> real) (_67357 : real) (s : real -> Prop) : (term561 x' s _67357 b) = (term567 b x' _67357 s).
Proof. exact (TRANS (@lem5158688 b x' _67357 s) (@lem5158695 b x' _67357 s)). Qed.
Lemma lem5158699 (_67357 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term567 b x' _67357 s.
Proof. exact (EQ_MP (@lem5158696 b x' _67357 s) (@lem5158685 _67357 b s x' h1)). Qed.
Lemma lem5158700 (b' : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term567 b x' b' s.
Proof. exact (@lem5158699 b' b s x' h1). Qed.
Lemma lem5158703 (s : real -> Prop) (x' : real -> real) (b : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') : term506 x' b' s.
Proof. exact (@lem5158700 b' b s x' h2 (@lem5158656 b b' h1 h3)). Qed.
Lemma lem5158704 (s : real -> Prop) (x' : real -> real) (b : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') : term533 x' b' s.
Proof. exact (fun h0 : term534 x' b' s => @lem5158703 s x' b b' h1 h2 h3). Qed.
Lemma lem5158706 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158707 (x' : real -> real) (b' : real) (s : real -> Prop) : (term533 x' b' s) = (term506 x' b' s).
Proof. exact (@lem5158706 (term506 x' b' s)). Qed.
Lemma lem5158708 (s : real -> Prop) (x' : real -> real) (b : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') : term506 x' b' s.
Proof. exact (EQ_MP (@lem5158707 x' b' s) (@lem5158704 s x' b b' h1 h2 h3)). Qed.
Lemma lem5158714 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5158715 (b' : real) (_67366 : real) (s : real -> Prop) : (term92 s _67366 b') = (term536 b' _67366 s).
Proof. exact (@lem5158714 (real_le _67366 b') (term537 _67366 s)). Qed.
Lemma lem5158721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5158722 (b' : real) (_67366 : real) (s : real -> Prop) : (term538 s _67366 b') = (term539 b' _67366 s).
Proof. exact (MK_COMB (@lem5158721) (@lem5158715 b' _67366 s)). Qed.
Lemma lem5158728 (b' : real) (_67366 : real) (s : real -> Prop) : (term536 b' _67366 s) = (term536 b' _67366 s).
Proof. exact (eq_refl (term536 b' _67366 s)). Qed.
Lemma lem5158729 (b' : real) (_67366 : real) (s : real -> Prop) : ((term92 s _67366 b') = (term536 b' _67366 s)) = ((term536 b' _67366 s) = (term536 b' _67366 s)).
Proof. exact (MK_COMB (@lem5158722 b' _67366 s) (@lem5158728 b' _67366 s)). Qed.
Lemma lem5158731 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5158732 (x : Prop) : (x = x) = True.
Proof. exact (@lem5158731 Prop x). Qed.
Lemma lem5158733 (b' : real) (_67366 : real) (s : real -> Prop) : ((term536 b' _67366 s) = (term536 b' _67366 s)) = True.
Proof. exact (@lem5158732 (term536 b' _67366 s)). Qed.
Lemma lem5158734 (b' : real) (_67366 : real) (s : real -> Prop) : ((term92 s _67366 b') = (term536 b' _67366 s)) = True.
Proof. exact (TRANS (@lem5158729 b' _67366 s) (@lem5158733 b' _67366 s)). Qed.
Lemma lem5158735 (b' : real) (_67366 : real) (s : real -> Prop) : True = ((term92 s _67366 b') = (term536 b' _67366 s)).
Proof. exact (SYM (@lem5158734 b' _67366 s)). Qed.
Lemma lem5158736 (b' : real) (_67366 : real) (s : real -> Prop) : (term92 s _67366 b') = (term536 b' _67366 s).
Proof. exact (EQ_MP (@lem5158735 b' _67366 s) (@lem0)). Qed.
Lemma lem5158737 (_67366 : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term156 s y b') : term536 b' _67366 s.
Proof. exact (EQ_MP (@lem5158736 b' _67366 s) (@lem5157748 _67366 s y b' h1)). Qed.
Lemma lem5158739 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158740 (s : real -> Prop) (_67366 : real) (b' : real) : (term536 b' _67366 s) = (term540 s _67366 b').
Proof. exact (@lem5158739 (term537 _67366 s) (real_le _67366 b')). Qed.
Lemma lem5158742 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5158743 (_67366 : real) (s : real -> Prop) : (term542 _67366 s) = (@IN real _67366 s).
Proof. exact (@lem5158742 (@IN real _67366 s)). Qed.
Lemma lem5158744 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5158745 (_67366 : real) (s : real -> Prop) : (term543 _67366 s) = (term544 _67366 s).
Proof. exact (MK_COMB (@lem5158744) (@lem5158743 _67366 s)). Qed.
Lemma lem5158746 (_67366 : real) (b' : real) : (real_le _67366 b') = (real_le _67366 b').
Proof. exact (eq_refl (real_le _67366 b')). Qed.
Lemma lem5158747 (s : real -> Prop) (_67366 : real) (b' : real) : (term540 s _67366 b') = (term80 s _67366 b').
Proof. exact (MK_COMB (@lem5158745 _67366 s) (@lem5158746 _67366 b')). Qed.
Lemma lem5158748 (s : real -> Prop) (_67366 : real) (b' : real) : (term536 b' _67366 s) = (term80 s _67366 b').
Proof. exact (TRANS (@lem5158740 s _67366 b') (@lem5158747 s _67366 b')). Qed.
Lemma lem5158751 (_67366 : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term156 s y b') : term80 s _67366 b'.
Proof. exact (EQ_MP (@lem5158748 s _67366 b') (@lem5158737 _67366 s y b' h1)). Qed.
Lemma lem5158752 (x' : real -> real) (s : real -> Prop) (y : real) (b' : real) (h1 : term156 s y b') : term545 s x' b'.
Proof. exact (@lem5158751 (x' b') s y b' h1). Qed.
Lemma lem5158755 (x' : real -> real) (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') (h4 : term156 s y b') : term546 x' b'.
Proof. exact (@lem5158752 x' s y b' h4 (@lem5158708 s x' b b' h1 h2 h3)). Qed.
Lemma lem5158756 (x' : real -> real) (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') (h4 : term156 s y b') : term547 x' b'.
Proof. exact (fun h0 : term511 x' b' => @lem5158755 x' b s y b' h1 h2 h3 h4). Qed.
Lemma lem5158758 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158759 (x' : real -> real) (b' : real) : (term547 x' b') = (term546 x' b').
Proof. exact (@lem5158758 (term546 x' b')). Qed.
Lemma lem5158760 (x' : real -> real) (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') (h4 : term156 s y b') : term546 x' b'.
Proof. exact (EQ_MP (@lem5158759 x' b') (@lem5158756 x' b s y b' h1 h2 h3 h4)). Qed.
Lemma lem5158771 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5158772 (_67359 : real) (_67358 : real) : (term568 _67358 _67359) = (term467 _67359 _67358).
Proof. exact (@lem5158771 (term71 _67358 _67359) (term105 _67359 _67358)). Qed.
Lemma lem5158778 (_67359 : real) (_67358 : real) : (term569 _67359 _67358) = (term569 _67359 _67358).
Proof. exact (eq_refl (term569 _67359 _67358)). Qed.
Lemma lem5158779 (_67359 : real) (_67358 : real) : ((term467 _67359 _67358) = (term568 _67358 _67359)) = ((term467 _67359 _67358) = (term467 _67359 _67358)).
Proof. exact (MK_COMB (@lem5158778 _67359 _67358) (@lem5158772 _67359 _67358)). Qed.
Lemma lem5158781 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5158782 (x : Prop) : (x = x) = True.
Proof. exact (@lem5158781 Prop x). Qed.
Lemma lem5158783 (_67359 : real) (_67358 : real) : ((term467 _67359 _67358) = (term467 _67359 _67358)) = True.
Proof. exact (@lem5158782 (term467 _67359 _67358)). Qed.
Lemma lem5158784 (_67358 : real) (_67359 : real) : ((term467 _67359 _67358) = (term568 _67358 _67359)) = True.
Proof. exact (TRANS (@lem5158779 _67359 _67358) (@lem5158783 _67359 _67358)). Qed.
Lemma lem5158785 (_67358 : real) (_67359 : real) : True = ((term467 _67359 _67358) = (term568 _67358 _67359)).
Proof. exact (SYM (@lem5158784 _67358 _67359)). Qed.
Lemma lem5158786 (_67358 : real) (_67359 : real) : (term467 _67359 _67358) = (term568 _67358 _67359).
Proof. exact (EQ_MP (@lem5158785 _67358 _67359) (@lem0)). Qed.
Lemma lem5158787 (_67358 : real) (_67359 : real) (h1 : term35) : term568 _67358 _67359.
Proof. exact (EQ_MP (@lem5158786 _67358 _67359) (@lem5157706 _67359 _67358 h1)). Qed.
Lemma lem5158789 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158790 (_67359 : real) (_67358 : real) : (term568 _67358 _67359) = (term570 _67359 _67358).
Proof. exact (@lem5158789 (term71 _67358 _67359) (term105 _67359 _67358)). Qed.
Lemma lem5158792 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5158793 (_67358 : real) (_67359 : real) : (term450 _67358 _67359) = (real_le _67358 _67359).
Proof. exact (@lem5158792 (real_le _67358 _67359)). Qed.
Lemma lem5158794 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5158795 (_67358 : real) (_67359 : real) : (term571 _67358 _67359) = (term572 _67358 _67359).
Proof. exact (MK_COMB (@lem5158794) (@lem5158793 _67358 _67359)). Qed.
Lemma lem5158796 (_67359 : real) (_67358 : real) : (term105 _67359 _67358) = (term105 _67359 _67358).
Proof. exact (eq_refl (term105 _67359 _67358)). Qed.
Lemma lem5158797 (_67359 : real) (_67358 : real) : (term570 _67359 _67358) = (term573 _67359 _67358).
Proof. exact (MK_COMB (@lem5158795 _67358 _67359) (@lem5158796 _67359 _67358)). Qed.
Lemma lem5158798 (_67359 : real) (_67358 : real) : (term568 _67358 _67359) = (term573 _67359 _67358).
Proof. exact (TRANS (@lem5158790 _67359 _67358) (@lem5158797 _67359 _67358)). Qed.
Lemma lem5158801 (_67359 : real) (_67358 : real) (h1 : term35) : term573 _67359 _67358.
Proof. exact (EQ_MP (@lem5158798 _67359 _67358) (@lem5158787 _67358 _67359 h1)). Qed.
Lemma lem5158802 (x' : real -> real) (b' : real) (h1 : term35) : term574 x' b'.
Proof. exact (@lem5158801 b' (x' b') h1). Qed.
Lemma lem5158805 (x' : real -> real) (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') (h4 : term156 s y b') : term575 x' b'.
Proof. exact (@lem5158802 x' b' h1 (@lem5158760 x' b s y b' h1 h2 h3 h4)). Qed.
Lemma lem5158806 (x' : real -> real) (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') (h4 : term156 s y b') : term576 x' b'.
Proof. exact (fun h0 : term507 x' b' => @lem5158805 x' b s y b' h1 h2 h3 h4). Qed.
Lemma lem5158808 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5158809 (x' : real -> real) (b' : real) : (term576 x' b') = (term575 x' b').
Proof. exact (@lem5158808 (term507 x' b')). Qed.
Lemma lem5158810 (x' : real -> real) (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') (h4 : term156 s y b') : term575 x' b'.
Proof. exact (EQ_MP (@lem5158809 x' b') (@lem5158806 x' b s y b' h1 h2 h3 h4)). Qed.
Lemma lem5158812 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158815 (x' : real -> real) (_67357 : real) (b : real) : (term521 b x' _67357) = (term577 x' _67357 b).
Proof. exact (@lem5158812 (term507 x' _67357) (term105 _67357 b)). Qed.
Lemma lem5158818 (_67357 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term577 x' _67357 b.
Proof. exact (EQ_MP (@lem5158815 x' _67357 b) (@lem5157817 _67357 b s x' h1)). Qed.
Lemma lem5158819 (b' : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term577 x' b' b.
Proof. exact (@lem5158818 b' b s x' h1). Qed.
Lemma lem5158822 (x' : real -> real) (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') (h4 : term156 s y b') : term105 b' b.
Proof. exact (@lem5158819 b' b s x' h2 (@lem5158810 x' b s y b' h1 h2 h3 h4)). Qed.
Lemma lem5158823 (x' : real -> real) (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') (h4 : term156 s y b') : term578 b' b.
Proof. exact (fun h0 : real_lt b' b => @lem5158822 x' b s y b' h1 h2 h3 h4). Qed.
Lemma lem5158825 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5158826 (b' : real) (b : real) : (term578 b' b) = (term105 b' b).
Proof. exact (@lem5158825 (real_lt b' b)). Qed.
Lemma lem5158827 (x' : real -> real) (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') (h4 : term156 s y b') : term105 b' b.
Proof. exact (EQ_MP (@lem5158826 b' b) (@lem5158823 x' b s y b' h1 h2 h3 h4)). Qed.
Lemma lem5158829 (b : Prop) (a : Prop) : (a \/ b) = (term531 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5158832 (_67360 : real) (_67361 : real) : (term454 _67361 _67360) = (term579 _67360 _67361).
Proof. exact (@lem5158829 (real_lt _67361 _67360) (real_le _67360 _67361)). Qed.
Lemma lem5158835 (_67360 : real) (_67361 : real) (h1 : term35) : term579 _67360 _67361.
Proof. exact (EQ_MP (@lem5158832 _67360 _67361) (@lem5157720 _67361 _67360 h1)). Qed.
Lemma lem5158836 (b : real) (b' : real) (h1 : term35) : term579 b b'.
Proof. exact (@lem5158835 b b' h1). Qed.
Lemma lem5158839 (x' : real -> real) (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b b') (h4 : term156 s y b') : real_le b b'.
Proof. exact (@lem5158836 b b' h1 (@lem5158827 x' b s y b' h1 h2 h3 h4)). Qed.
Lemma lem5158840 (b : real) (x' : real -> real) (s : real -> Prop) (y : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term156 s y b') : term556 b b'.
Proof. exact (fun h0 : term71 b b' => @lem5158839 x' b s y b' h1 h2 h0 h3). Qed.
Lemma lem5158842 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158843 (b : real) (b' : real) : (term556 b b') = (real_le b b').
Proof. exact (@lem5158842 (real_le b b')). Qed.
Lemma lem5158844 (b : real) (x' : real -> real) (s : real -> Prop) (y : real) (b' : real) (h1 : term35) (h2 : term139 b s x') (h3 : term156 s y b') : real_le b b'.
Proof. exact (EQ_MP (@lem5158843 b b') (@lem5158840 b x' s y b' h1 h2 h3)). Qed.
Lemma lem5158847 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5158849 (b : real) (b' : real) : (term71 b b') = (term601 b b').
Proof. exact (@lem5158847 (real_le b b')). Qed.
Lemma lem5158852 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term156 s y b') (h2 : term332 s b' y b) : term601 b b'.
Proof. exact (EQ_MP (@lem5158849 b b') (@lem5157761 s b' y b h1 h2)). Qed.
Lemma lem5158855 (x' : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term156 s y b') (h4 : term332 s b' y b) : False.
Proof. exact (@lem5158852 s b' y b h3 h4 (@lem5158844 b x' s y b' h1 h2 h3)). Qed.
Lemma lem5158856 (x' : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term156 s y b') (h4 : term332 s b' y b) : term599.
Proof. exact (fun h0 : ~ False => @lem5158855 x' s b' y b h1 h2 h3 h4). Qed.
Lemma lem5158858 (p : Prop) : (term535 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5158859 : term599 = False.
Proof. exact (@lem5158858 False). Qed.
Lemma lem5158861 (x' : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term156 s y b') (h4 : term332 s b' y b) : False.
Proof. exact (EQ_MP (@lem5158859) (@lem5158856 x' s b' y b h1 h2 h3 h4)). Qed.
Lemma lem5158862 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term19 s b) (h2 : term144 s b' y) (h3 : term332 s b' y b) : False.
Proof. exact (EQ_MP (@lem5158534) (@lem5158531 s b' y b h1 h2 h3)). Qed.
Lemma lem5158863 (x' : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term19 s b) (h3 : term139 b s x') (h4 : term332 s b' y b) : False.
Proof. exact (or_elim (@lem5156773 s b' y b h4) (fun h0 : term144 s b' y => @lem5158862 s b' y b h2 h0 h4) (fun h0 : term156 s y b' => @lem5158861 x' s b' y b h1 h3 h0 h4)). Qed.
Lemma lem5158864 (x' : real -> real) (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term382 x s b' y b) : False.
Proof. exact (or_elim (@lem5156730 x s b' y b h5) (fun h0 : term295 s x y b => @lem5158391 x' s x y b h1 h2 h3 h4 h0) (fun h0 : term332 s b' y b => @lem5158863 x' s b' y b h1 h3 h4 h0)). Qed.
Lemma lem5158865 (x' : real -> real) (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term382 x s b' y b) : (term139 b s x') = False.
Proof. exact (prop_ext (fun h6 : term139 b s x' => @lem5158864 x' x s b' y b h1 h2 h3 h4 h5) (fun h6 : False => @lem5156761 b s x' h4)). Qed.
Lemma lem5158866 (x' : real -> real) (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term382 x s b' y b) : False.
Proof. exact (EQ_MP (@lem5158865 x' x s b' y b h1 h2 h3 h4 h5) (@lem5156761 b s x' h4)). Qed.
Lemma lem5158867 (x' : real -> real) (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term382 x s b' y b) : (term382 x s b' y b) = False.
Proof. exact (prop_ext (fun h6 : term382 x s b' y b => @lem5158866 x' x s b' y b h1 h2 h3 h4 h5) (fun h6 : False => @lem5156730 x s b' y b h5)). Qed.
Lemma lem5158868 (x' : real -> real) (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term382 x s b' y b) : False.
Proof. exact (EQ_MP (@lem5158867 x' x s b' y b h1 h2 h3 h4 h5) (@lem5156730 x s b' y b h5)). Qed.
Lemma lem5158869 (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term18 b s) (h5 : term382 x s b' y b) : False.
Proof. exact (ex_elim (@lem5155097 b s h4) (fun x' : real -> real => fun h0 : term141 b s x' => @lem5158868 x' x s b' y b h1 h2 h3 h0 h5)). Qed.
Lemma lem5158870 (x : real -> real) (s : real -> Prop) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term18 b s) (h5 : term385 x s y b) : False.
Proof. exact (ex_elim (@lem5156480 x s y b h5) (fun b' : real => fun h0 : term384 x s y b b' => @lem5158869 x s b' y b h1 h2 h3 h4 h0)). Qed.
Lemma lem5158871 (s : real -> Prop) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term18 b s) (h5 : term387 s y b) : False.
Proof. exact (ex_elim (@lem5156479 s y b h5) (fun x : real -> real => fun h0 : term386 s y b x => @lem5158870 x s y b h1 h2 h3 h4 h0)). Qed.
Lemma lem5158872 (s : real -> Prop) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term18 b s) (h5 : term62 s b) : False.
Proof. exact (ex_elim (@lem5155892 s b h5) (fun y : real => fun h0 : term388 s b y => @lem5158871 s y b h1 h2 h3 h4 h0)). Qed.
Lemma lem5158873 (s : real -> Prop) (b : real) (h1 : term79) (h2 : term19 s b) (h3 : term18 b s) (h4 : term62 s b) : term33.
Proof. exact (fun h0 : term35 => @lem5158872 s b h0 h1 h2 h3 h4). Qed.
Lemma lem5158874 : term33 = term34.
Proof. exact (@lem69 term35). Qed.
Lemma lem5158875 (s : real -> Prop) (b : real) (h1 : term79) (h2 : term19 s b) (h3 : term18 b s) (h4 : term62 s b) : term34.
Proof. exact (EQ_MP (@lem5158874) (@lem5158873 s b h1 h2 h3 h4)). Qed.
Lemma lem5158876 (s : real -> Prop) (b : real) (h1 : term19 s b) (h2 : term18 b s) (h3 : term62 s b) : term38.
Proof. exact (fun h0 : term79 => @lem5158875 s b h0 h1 h2 h3). Qed.
Lemma lem5158877 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : term64 s b.
Proof. exact (fun h0 : term62 s b => @lem5158876 s b h1 h2 h0). Qed.
Lemma lem5158878 (s : real -> Prop) (b : real) (h1 : term19 s b) : term65 s b.
Proof. exact (fun h0 : term18 b s => @lem5158877 b s h1 h0). Qed.
Lemma lem5158879 (s : real -> Prop) (b : real) : term66 s b.
Proof. exact (fun h0 : term19 s b => @lem5158878 s b h0). Qed.
Lemma lem5158884 (b : real) : term68 b.
Proof. exact (fun s : real -> Prop => @lem5158879 s b). Qed.
Lemma lem5158889 : term70.
Proof. exact (fun b : real => @lem5158884 b). Qed.
Lemma lem5158890 : term53.
Proof. exact (EQ_MP (@lem5154858) (@lem5158889)). Qed.
Lemma lem5158891 (b : real) : term602 b.
Proof. exact (@lem5158890 b). Qed.
Lemma lem5158892 (b : real) : (term602 b) = (term49 b).
Proof. exact (eq_refl (term602 b)). Qed.
Lemma lem5158893 (b : real) : term49 b.
Proof. exact (EQ_MP (@lem5158892 b) (@lem5158891 b)). Qed.
Lemma lem5158894 (b : real) (s : real -> Prop) : term603 b s.
Proof. exact (@lem5158893 b s). Qed.
Lemma lem5158895 (s : real -> Prop) (b : real) : (term603 b s) = (term29 s b).
Proof. exact (eq_refl (term603 b s)). Qed.
Lemma lem5158896 (s : real -> Prop) (b : real) : term29 s b.
Proof. exact (EQ_MP (@lem5158895 s b) (@lem5158894 b s)). Qed.
Lemma lem5158898 (s : real -> Prop) (b : real) : term29 s b.
Proof. exact (@lem5154466 s b (@lem5158896 s b)). Qed.
Lemma lem5158899 (s : real -> Prop) (b : real) (h1 : term19 s b) : term43 s b.
Proof. exact (@lem5158898 s b (@lem5154411 s b h1)). Qed.
Lemma lem5158900 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : term40 s b.
Proof. exact (@lem5158899 s b h1 (@lem5154410 b s h2)). Qed.
Lemma lem5158901 (s : real -> Prop) (b : real) (h1 : term19 s b) (h2 : term18 b s) (h3 : term28 s b) : term37.
Proof. exact (@lem5158900 b s h1 h2 (@lem5154451 s b h3)). Qed.
Lemma lem5158902 (s : real -> Prop) (b : real) (h1 : term19 s b) (h2 : term18 b s) (h3 : term28 s b) : term33.
Proof. exact (@lem5158901 s b h1 h2 h3 (@lem1339379)). Qed.
Lemma lem5158903 (s : real -> Prop) (b : real) (h1 : term19 s b) (h2 : term18 b s) (h3 : term28 s b) : False.
Proof. exact (@lem5158902 s b h1 h2 h3 (@lem1495933)). Qed.
Lemma lem5158904 (s : real -> Prop) (b : real) (h1 : term19 s b) (h2 : term18 b s) (h3 : term28 s b) : (term28 s b) = False.
Proof. exact (prop_ext (fun h4 : term28 s b => @lem5158903 s b h1 h2 h3) (fun h4 : False => @lem5154451 s b h3)). Qed.
Lemma lem5158905 (s : real -> Prop) (b : real) (h1 : term19 s b) (h2 : term18 b s) (h3 : term28 s b) : False.
Proof. exact (EQ_MP (@lem5158904 s b h1 h2 h3) (@lem5154451 s b h3)). Qed.
Lemma lem5158906 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : term27 s b.
Proof. exact (fun h0 : term28 s b => @lem5158905 s b h1 h2 h0). Qed.
Lemma lem5158907 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : term26 s b.
Proof. exact (EQ_MP (@lem5154450 s b) (@lem5158906 b s h1 h2)). Qed.
Lemma lem5158908 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : (term16 s) = b.
Proof. exact (@lem5154446 s b (@lem5158907 b s h1 h2)). Qed.
Lemma lem5158909 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : (sup s) = b.
Proof. exact (EQ_MP (@lem5154442 s b) (@lem5158908 b s h1 h2)). Qed.
Lemma lem5158910 (b : real) (s : real -> Prop) (h1 : term17 b s) : term18 b s.
Proof. exact (proj2 (@lem5154409 b s h1)). Qed.
Lemma lem5158911 (b : real) (s : real -> Prop) (h1 : term17 b s) : term19 s b.
Proof. exact (proj1 (@lem5154409 b s h1)). Qed.
Lemma lem5158912 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : (term18 b s) = ((sup s) = b).
Proof. exact (prop_ext (fun h3 : term18 b s => @lem5158909 b s h1 h2) (fun h3 : (sup s) = b => @lem5154410 b s h2)). Qed.
Lemma lem5158913 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : (sup s) = b.
Proof. exact (EQ_MP (@lem5158912 b s h1 h2) (@lem5154410 b s h2)). Qed.
Lemma lem5158914 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : (term19 s b) = ((sup s) = b).
Proof. exact (prop_ext (fun h3 : term19 s b => @lem5158913 b s h1 h2) (fun h3 : (sup s) = b => @lem5154411 s b h1)). Qed.
Lemma lem5158915 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : (sup s) = b.
Proof. exact (EQ_MP (@lem5158914 b s h1 h2) (@lem5154411 s b h1)). Qed.
Lemma lem5158916 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term17 b s) : (term18 b s) = ((sup s) = b).
Proof. exact (prop_ext (fun h3 : term18 b s => @lem5158915 b s h1 h3) (fun h3 : (sup s) = b => @lem5158910 b s h2)). Qed.
Lemma lem5158917 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term17 b s) : (sup s) = b.
Proof. exact (EQ_MP (@lem5158916 b s h1 h2) (@lem5158910 b s h2)). Qed.
Lemma lem5158918 (b : real) (s : real -> Prop) (h1 : term17 b s) : (term19 s b) = ((sup s) = b).
Proof. exact (prop_ext (fun h2 : term19 s b => @lem5158917 b s h2 h1) (fun h2 : (sup s) = b => @lem5158911 b s h1)). Qed.
Lemma lem5158919 (b : real) (s : real -> Prop) (h1 : term17 b s) : (sup s) = b.
Proof. exact (EQ_MP (@lem5158918 b s h1) (@lem5158911 b s h1)). Qed.
Lemma lem5158920 (s : real -> Prop) (b : real) : term604 s b.
Proof. exact (fun h0 : term17 b s => @lem5158919 b s h0). Qed.
Lemma lem5158925 (s : real -> Prop) : term605 s.
Proof. exact (fun b : real => @lem5158920 s b). Qed.
Lemma lem5158930 : term606.
Proof. exact (fun s : real -> Prop => @lem5158925 s). Qed.
