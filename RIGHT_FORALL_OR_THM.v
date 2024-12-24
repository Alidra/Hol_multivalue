Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_FORALL_OR_THM_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import DE_MORGAN_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_FORALL_THM_spec.
Require Import RIGHT_EXISTS_AND_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem11455 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem5751 A P). Qed.
Lemma lem11456 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem11457 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem11456 A P) (@lem11455 A P)). Qed.
Lemma lem11458 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem11457 A P Q). Qed.
Lemma lem11459 {A : Type'} (P : Prop) (Q : A -> Prop) : (term2 A P Q) = ((term3 A P Q) = (term4 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem11461 (t1 : Prop) : term5 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem11462 (t1 : Prop) : (term5 t1) = (term6 t1).
Proof. exact (eq_refl (term5 t1)). Qed.
Lemma lem11463 (t1 : Prop) : term6 t1.
Proof. exact (EQ_MP (@lem11462 t1) (@lem11461 t1)). Qed.
Lemma lem11464 (t1 : Prop) (t2 : Prop) : term7 t1 t2.
Proof. exact (@lem11463 t1 t2). Qed.
Lemma lem11465 (t1 : Prop) (t2 : Prop) : (term7 t1 t2) = (term8 t1 t2).
Proof. exact (eq_refl (term7 t1 t2)). Qed.
Lemma lem11466 (t1 : Prop) (t2 : Prop) : term8 t1 t2.
Proof. exact (EQ_MP (@lem11465 t1 t2) (@lem11464 t1 t2)). Qed.
Lemma lem11469 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem11470 {A : Type'} (P : A -> Prop) : (term9 A P) = ((term10 A P) = (term11 A P)).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem11480 (a : Prop) : term12 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem11481 (a : Prop) : (term12 a) = (term13 a).
Proof. exact (eq_refl (term12 a)). Qed.
Lemma lem11482 (a : Prop) : term13 a.
Proof. exact (EQ_MP (@lem11481 a) (@lem11480 a)). Qed.
Lemma lem11483 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem11484 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem11493 (b : Prop) : (term14 b) = (term14 b).
Proof. exact (eq_refl (term14 b)). Qed.
Lemma lem11494 (b : Prop) (a : Prop) (h1 : a = True) : (term15 b a) = (term16 b).
Proof. exact (MK_COMB (@lem11493 b) (@lem11483 a h1)). Qed.
Lemma lem11495 (b : Prop) : (term16 b) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (eq_refl (term16 b)). Qed.
Lemma lem11496 (b : Prop) (a : Prop) : (term17 b a) = (term17 b a).
Proof. exact (eq_refl (term17 b a)). Qed.
Lemma lem11497 (a : Prop) (b : Prop) : ((term15 b a) = (term16 b)) = ((term15 b a) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (MK_COMB (@lem11496 b a) (@lem11495 b)). Qed.
Lemma lem11498 (a : Prop) (b : Prop) : (term15 b a) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (eq_refl (term15 b a)). Qed.
Lemma lem11499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11500 (a : Prop) (b : Prop) : (term17 b a) = (term18 a b).
Proof. exact (MK_COMB (@lem11499) (@lem11498 a b)). Qed.
Lemma lem11501 (b : Prop) : ((True = b) = ((~ True) = (~ b))) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (eq_refl ((True = b) = ((~ True) = (~ b)))). Qed.
Lemma lem11502 (a : Prop) (b : Prop) : ((term15 b a) = ((True = b) = ((~ True) = (~ b)))) = (((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (MK_COMB (@lem11500 a b) (@lem11501 b)). Qed.
Lemma lem11503 (a : Prop) (b : Prop) : ((term15 b a) = (term16 b)) = (((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (TRANS (@lem11497 a b) (@lem11502 a b)). Qed.
Lemma lem11504 (b : Prop) (a : Prop) (h1 : a = True) : ((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (EQ_MP (@lem11503 a b) (@lem11494 b a h1)). Qed.
Lemma lem11505 (b : Prop) (a : Prop) (h1 : a = True) : ((True = b) = ((~ True) = (~ b))) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (SYM (@lem11504 b a h1)). Qed.
Lemma lem11506 (b : Prop) : (term14 b) = (term14 b).
Proof. exact (eq_refl (term14 b)). Qed.
Lemma lem11507 (b : Prop) (a : Prop) (h1 : a = False) : (term15 b a) = (term19 b).
Proof. exact (MK_COMB (@lem11506 b) (@lem11484 a h1)). Qed.
Lemma lem11508 (b : Prop) : (term19 b) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (eq_refl (term19 b)). Qed.
Lemma lem11509 (b : Prop) (a : Prop) : (term17 b a) = (term17 b a).
Proof. exact (eq_refl (term17 b a)). Qed.
Lemma lem11510 (a : Prop) (b : Prop) : ((term15 b a) = (term19 b)) = ((term15 b a) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (MK_COMB (@lem11509 b a) (@lem11508 b)). Qed.
Lemma lem11511 (a : Prop) (b : Prop) : (term15 b a) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (eq_refl (term15 b a)). Qed.
Lemma lem11512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11513 (a : Prop) (b : Prop) : (term17 b a) = (term18 a b).
Proof. exact (MK_COMB (@lem11512) (@lem11511 a b)). Qed.
Lemma lem11514 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (eq_refl ((False = b) = ((~ False) = (~ b)))). Qed.
Lemma lem11515 (a : Prop) (b : Prop) : ((term15 b a) = ((False = b) = ((~ False) = (~ b)))) = (((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (MK_COMB (@lem11513 a b) (@lem11514 b)). Qed.
Lemma lem11516 (a : Prop) (b : Prop) : ((term15 b a) = (term19 b)) = (((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (TRANS (@lem11510 a b) (@lem11515 a b)). Qed.
Lemma lem11517 (b : Prop) (a : Prop) (h1 : a = False) : ((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (EQ_MP (@lem11516 a b) (@lem11507 b a h1)). Qed.
Lemma lem11518 (b : Prop) (a : Prop) (h1 : a = False) : ((False = b) = ((~ False) = (~ b))) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (SYM (@lem11517 b a h1)). Qed.
Lemma lem11522 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem11523 (b : Prop) : (True = b) = b.
Proof. exact (@lem11522 b). Qed.
Lemma lem11524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11525 (b : Prop) : (term20 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem11524) (@lem11523 b)). Qed.
Lemma lem11529 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem11530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11531 : term21 = (@eq Prop False).
Proof. exact (MK_COMB (@lem11530) (@lem11529)). Qed.
Lemma lem11532 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem11533 (b : Prop) : ((~ True) = (~ b)) = (False = (~ b)).
Proof. exact (MK_COMB (@lem11531) (@lem11532 b)). Qed.
Lemma lem11535 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem11536 (b : Prop) : (False = (~ b)) = (term22 b).
Proof. exact (@lem11535 (~ b)). Qed.
Lemma lem11537 (b : Prop) : ((~ True) = (~ b)) = (term22 b).
Proof. exact (TRANS (@lem11533 b) (@lem11536 b)). Qed.
Lemma lem11538 (b : Prop) : ((True = b) = ((~ True) = (~ b))) = (b = (term22 b)).
Proof. exact (MK_COMB (@lem11525 b) (@lem11537 b)). Qed.
Lemma lem11541 (b : Prop) : (b = (term22 b)) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (SYM (@lem11538 b)). Qed.
Lemma lem11550 (t : Prop) : (term22 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem11551 (b : Prop) : (term22 b) = b.
Proof. exact (@lem11550 b). Qed.
Lemma lem11552 (b : Prop) : (@eq Prop b) = (@eq Prop b).
Proof. exact (eq_refl (@eq Prop b)). Qed.
Lemma lem11553 (b : Prop) : (b = (term22 b)) = (b = b).
Proof. exact (MK_COMB (@lem11552 b) (@lem11551 b)). Qed.
Lemma lem11555 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem11556 (x : Prop) : (x = x) = True.
Proof. exact (@lem11555 Prop x). Qed.
Lemma lem11557 (b : Prop) : (b = b) = True.
Proof. exact (@lem11556 b). Qed.
Lemma lem11558 (b : Prop) : (b = (term22 b)) = True.
Proof. exact (TRANS (@lem11553 b) (@lem11557 b)). Qed.
Lemma lem11559 (b : Prop) : True = (b = (term22 b)).
Proof. exact (SYM (@lem11558 b)). Qed.
Lemma lem11560 (b : Prop) : b = (term22 b).
Proof. exact (EQ_MP (@lem11559 b) (@lem0)). Qed.
Lemma lem11561 (b : Prop) : (True = b) = ((~ True) = (~ b)).
Proof. exact (EQ_MP (@lem11541 b) (@lem11560 b)). Qed.
Lemma lem11565 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem11566 (b : Prop) : (False = b) = (~ b).
Proof. exact (@lem11565 b). Qed.
Lemma lem11567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11568 (b : Prop) : (term23 b) = (term24 b).
Proof. exact (MK_COMB (@lem11567) (@lem11566 b)). Qed.
Lemma lem11572 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem11573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11574 : term25 = (@eq Prop True).
Proof. exact (MK_COMB (@lem11573) (@lem11572)). Qed.
Lemma lem11575 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem11576 (b : Prop) : ((~ False) = (~ b)) = (True = (~ b)).
Proof. exact (MK_COMB (@lem11574) (@lem11575 b)). Qed.
Lemma lem11578 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem11579 (b : Prop) : (True = (~ b)) = (~ b).
Proof. exact (@lem11578 (~ b)). Qed.
Lemma lem11580 (b : Prop) : ((~ False) = (~ b)) = (~ b).
Proof. exact (TRANS (@lem11576 b) (@lem11579 b)). Qed.
Lemma lem11581 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = ((~ b) = (~ b)).
Proof. exact (MK_COMB (@lem11568 b) (@lem11580 b)). Qed.
Lemma lem11583 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem11584 (x : Prop) : (x = x) = True.
Proof. exact (@lem11583 Prop x). Qed.
Lemma lem11585 (b : Prop) : ((~ b) = (~ b)) = True.
Proof. exact (@lem11584 (~ b)). Qed.
Lemma lem11586 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = True.
Proof. exact (TRANS (@lem11581 b) (@lem11585 b)). Qed.
Lemma lem11587 (b : Prop) : True = ((False = b) = ((~ False) = (~ b))).
Proof. exact (SYM (@lem11586 b)). Qed.
Lemma lem11588 (b : Prop) : (False = b) = ((~ False) = (~ b)).
Proof. exact (EQ_MP (@lem11587 b) (@lem0)). Qed.
Lemma lem11589 (b : Prop) (a : Prop) (h1 : a = False) : (a = b) = ((~ a) = (~ b)).
Proof. exact (EQ_MP (@lem11518 b a h1) (@lem11588 b)). Qed.
Lemma lem11590 (b : Prop) (a : Prop) (h1 : a = True) : (a = b) = ((~ a) = (~ b)).
Proof. exact (EQ_MP (@lem11505 b a h1) (@lem11561 b)). Qed.
Lemma lem11597 (a : Prop) (b : Prop) : (a = b) = ((~ a) = (~ b)).
Proof. exact (or_elim (@lem11482 a) (fun h0 : a = True => @lem11590 b a h0) (fun h0 : a = False => @lem11589 b a h0)). Qed.
Lemma lem11598 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term26 A P Q) = (term27 A P Q)) = ((term28 A P Q) = (term29 A P Q)).
Proof. exact (@lem11597 (term26 A P Q) (term27 A P Q)). Qed.
Lemma lem11599 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term28 A P Q) = (term29 A P Q)) = ((term26 A P Q) = (term27 A P Q)).
Proof. exact (SYM (@lem11598 A P Q)). Qed.
Lemma lem11603 {A : Type'} (P : A -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (EQ_MP (@lem11470 A P) (@lem11469 A P)). Qed.
Lemma lem11604 {A : Type'} (P : A -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (@lem11603 A P). Qed.
Lemma lem11605 {A : Type'} (P : Prop) (Q : A -> Prop) : (term30 A P Q) = (term31 A P Q).
Proof. exact (@lem11604 A (term32 A P Q)). Qed.
Lemma lem11606 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) : (term33 A P Q x) = (term34 A P Q x).
Proof. exact (eq_refl (term33 A P Q x)). Qed.
Lemma lem11607 {A : Type'} (P : Prop) (Q : A -> Prop) : (term35 A P Q) = (term32 A P Q).
Proof. exact (fun_ext (fun x : A => @lem11606 A P Q x)). Qed.
Lemma lem11608 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem11609 {A : Type'} (P : Prop) (Q : A -> Prop) : (term36 A P Q) = (term26 A P Q).
Proof. exact (MK_COMB (@lem11608 A) (@lem11607 A P Q)). Qed.
Lemma lem11610 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem11611 {A : Type'} (P : Prop) (Q : A -> Prop) : (term30 A P Q) = (term28 A P Q).
Proof. exact (MK_COMB (@lem11610) (@lem11609 A P Q)). Qed.
Lemma lem11612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11613 {A : Type'} (P : Prop) (Q : A -> Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (MK_COMB (@lem11612) (@lem11611 A P Q)). Qed.
Lemma lem11614 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) : (term33 A P Q x) = (term34 A P Q x).
Proof. exact (eq_refl (term33 A P Q x)). Qed.
Lemma lem11615 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem11616 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) : (term39 A P Q x) = (term40 A P Q x).
Proof. exact (MK_COMB (@lem11615) (@lem11614 A P Q x)). Qed.
Lemma lem11617 {A : Type'} (P : Prop) (Q : A -> Prop) : (term41 A P Q) = (term42 A P Q).
Proof. exact (fun_ext (fun x : A => @lem11616 A P Q x)). Qed.
Lemma lem11618 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem11619 {A : Type'} (P : Prop) (Q : A -> Prop) : (term31 A P Q) = (term43 A P Q).
Proof. exact (MK_COMB (@lem11618 A) (@lem11617 A P Q)). Qed.
Lemma lem11620 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term30 A P Q) = (term31 A P Q)) = ((term28 A P Q) = (term43 A P Q)).
Proof. exact (MK_COMB (@lem11613 A P Q) (@lem11619 A P Q)). Qed.
Lemma lem11621 {A : Type'} (P : Prop) (Q : A -> Prop) : (term28 A P Q) = (term43 A P Q).
Proof. exact (EQ_MP (@lem11620 A P Q) (@lem11605 A P Q)). Qed.
Lemma lem11627 (t1 : Prop) (t2 : Prop) : (term44 t1 t2) = (term45 t1 t2).
Proof. exact (proj2 (@lem11466 t1 t2)). Qed.
Lemma lem11628 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) : (term40 A P Q x) = (term46 A P Q x).
Proof. exact (@lem11627 P (Q x)). Qed.
Lemma lem11631 {A : Type'} (P : Prop) (Q : A -> Prop) : (term42 A P Q) = (term47 A P Q).
Proof. exact (fun_ext (fun x : A => @lem11628 A P Q x)). Qed.
Lemma lem11632 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem11633 {A : Type'} (P : Prop) (Q : A -> Prop) : (term43 A P Q) = (term48 A P Q).
Proof. exact (MK_COMB (@lem11632 A) (@lem11631 A P Q)). Qed.
Lemma lem11635 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem11459 A P Q) (@lem11458 A P Q)). Qed.
Lemma lem11636 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (@lem11635 A P Q). Qed.
Lemma lem11637 {A : Type'} (P : Prop) (Q : A -> Prop) : (term49 A P Q) = (term50 A P Q).
Proof. exact (@lem11636 A (~ P) (term51 A Q)). Qed.
Lemma lem11638 {A : Type'} (Q : A -> Prop) (x : A) : (term52 A Q x) = (term53 A Q x).
Proof. exact (eq_refl (term52 A Q x)). Qed.
Lemma lem11639 (P : Prop) : (term54 P) = (term54 P).
Proof. exact (eq_refl (term54 P)). Qed.
Lemma lem11640 {A : Type'} (P : Prop) (Q : A -> Prop) (x : A) : (term55 A P Q x) = (term46 A P Q x).
Proof. exact (MK_COMB (@lem11639 P) (@lem11638 A Q x)). Qed.
Lemma lem11641 {A : Type'} (P : Prop) (Q : A -> Prop) : (term56 A P Q) = (term47 A P Q).
Proof. exact (fun_ext (fun x : A => @lem11640 A P Q x)). Qed.
Lemma lem11642 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem11643 {A : Type'} (P : Prop) (Q : A -> Prop) : (term49 A P Q) = (term48 A P Q).
Proof. exact (MK_COMB (@lem11642 A) (@lem11641 A P Q)). Qed.
Lemma lem11644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11645 {A : Type'} (P : Prop) (Q : A -> Prop) : (term57 A P Q) = (term58 A P Q).
Proof. exact (MK_COMB (@lem11644) (@lem11643 A P Q)). Qed.
Lemma lem11646 {A : Type'} (Q : A -> Prop) (x : A) : (term52 A Q x) = (term53 A Q x).
Proof. exact (eq_refl (term52 A Q x)). Qed.
Lemma lem11647 {A : Type'} (Q : A -> Prop) : (term59 A Q) = (term51 A Q).
Proof. exact (fun_ext (fun x : A => @lem11646 A Q x)). Qed.
Lemma lem11648 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem11649 {A : Type'} (Q : A -> Prop) : (term60 A Q) = (term11 A Q).
Proof. exact (MK_COMB (@lem11648 A) (@lem11647 A Q)). Qed.
Lemma lem11650 (P : Prop) : (term54 P) = (term54 P).
Proof. exact (eq_refl (term54 P)). Qed.
Lemma lem11651 {A : Type'} (P : Prop) (Q : A -> Prop) : (term50 A P Q) = (term61 A P Q).
Proof. exact (MK_COMB (@lem11650 P) (@lem11649 A Q)). Qed.
Lemma lem11652 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term49 A P Q) = (term50 A P Q)) = ((term48 A P Q) = (term61 A P Q)).
Proof. exact (MK_COMB (@lem11645 A P Q) (@lem11651 A P Q)). Qed.
Lemma lem11653 {A : Type'} (P : Prop) (Q : A -> Prop) : (term48 A P Q) = (term61 A P Q).
Proof. exact (EQ_MP (@lem11652 A P Q) (@lem11637 A P Q)). Qed.
Lemma lem11660 {A : Type'} (P : Prop) (Q : A -> Prop) : (term43 A P Q) = (term61 A P Q).
Proof. exact (TRANS (@lem11633 A P Q) (@lem11653 A P Q)). Qed.
Lemma lem11661 {A : Type'} (P : Prop) (Q : A -> Prop) : (term28 A P Q) = (term61 A P Q).
Proof. exact (TRANS (@lem11621 A P Q) (@lem11660 A P Q)). Qed.
Lemma lem11662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11663 {A : Type'} (P : Prop) (Q : A -> Prop) : (term38 A P Q) = (term62 A P Q).
Proof. exact (MK_COMB (@lem11662) (@lem11661 A P Q)). Qed.
Lemma lem11665 (t1 : Prop) (t2 : Prop) : (term44 t1 t2) = (term45 t1 t2).
Proof. exact (proj2 (@lem11466 t1 t2)). Qed.
Lemma lem11666 {A : Type'} (P : Prop) (Q : A -> Prop) : (term29 A P Q) = (term63 A P Q).
Proof. exact (@lem11665 P (term64 A Q)). Qed.
Lemma lem11670 {A : Type'} (P : A -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (EQ_MP (@lem11470 A P) (@lem11469 A P)). Qed.
Lemma lem11671 {A : Type'} (P : A -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (@lem11670 A P). Qed.
Lemma lem11672 {A : Type'} (Q : A -> Prop) : (term10 A Q) = (term11 A Q).
Proof. exact (@lem11671 A Q). Qed.
Lemma lem11677 (P : Prop) : (term54 P) = (term54 P).
Proof. exact (eq_refl (term54 P)). Qed.
Lemma lem11678 {A : Type'} (P : Prop) (Q : A -> Prop) : (term63 A P Q) = (term61 A P Q).
Proof. exact (MK_COMB (@lem11677 P) (@lem11672 A Q)). Qed.
Lemma lem11681 {A : Type'} (P : Prop) (Q : A -> Prop) : (term29 A P Q) = (term61 A P Q).
Proof. exact (TRANS (@lem11666 A P Q) (@lem11678 A P Q)). Qed.
Lemma lem11682 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term28 A P Q) = (term29 A P Q)) = ((term61 A P Q) = (term61 A P Q)).
Proof. exact (MK_COMB (@lem11663 A P Q) (@lem11681 A P Q)). Qed.
Lemma lem11684 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem11685 (x : Prop) : (x = x) = True.
Proof. exact (@lem11684 Prop x). Qed.
Lemma lem11686 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term61 A P Q) = (term61 A P Q)) = True.
Proof. exact (@lem11685 (term61 A P Q)). Qed.
Lemma lem11687 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term28 A P Q) = (term29 A P Q)) = True.
Proof. exact (TRANS (@lem11682 A P Q) (@lem11686 A P Q)). Qed.
Lemma lem11688 {A : Type'} (P : Prop) (Q : A -> Prop) : True = ((term28 A P Q) = (term29 A P Q)).
Proof. exact (SYM (@lem11687 A P Q)). Qed.
Lemma lem11689 {A : Type'} (P : Prop) (Q : A -> Prop) : (term28 A P Q) = (term29 A P Q).
Proof. exact (EQ_MP (@lem11688 A P Q) (@lem0)). Qed.
Lemma lem11690 {A : Type'} (P : Prop) (Q : A -> Prop) : (term26 A P Q) = (term27 A P Q).
Proof. exact (EQ_MP (@lem11599 A P Q) (@lem11689 A P Q)). Qed.
Lemma lem11695 {A : Type'} (P : Prop) : term65 A P.
Proof. exact (fun Q : A -> Prop => @lem11690 A P Q). Qed.
Lemma lem11700 {A : Type'} : term66 A.
Proof. exact (fun P : Prop => @lem11695 A P). Qed.
