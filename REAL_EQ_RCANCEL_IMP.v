Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_RCANCEL_IMP_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_ENTIRE_spec.
Require Import REAL_SUB_0_spec.
Require Import REAL_SUB_RDISTRIB_spec.
Require Import REAL_SUB_RZERO_spec.
Require Import thm0_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Lemma lem1640496 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem1640497 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem1640496 x y z h1)). Qed.
Lemma lem1640498 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1640499 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem1640498 x y z h1)). Qed.
Lemma lem1640500 (x : real) (y : real) (z : real) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem1640497 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem1640499 x y z h1)). Qed.
Lemma lem1640501 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : real => @lem1640500 x y z)). Qed.
Lemma lem1640502 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1640503 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1640502) (@lem1640501 x y)). Qed.
Lemma lem1640504 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1640503 x y)). Qed.
Lemma lem1640505 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1640506 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1640505) (@lem1640504 x)). Qed.
Lemma lem1640507 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1640506 x)). Qed.
Lemma lem1640508 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1640509 : term12 = term13.
Proof. exact (MK_COMB (@lem1640508) (@lem1640507)). Qed.
Lemma lem1640510 : term13.
Proof. exact (EQ_MP (@lem1640509) (@lem1526749)). Qed.
Lemma lem1640511 (x : real) : term14 x.
Proof. exact (@lem1382769 x). Qed.
Lemma lem1640512 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1640513 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem1640512 x) (@lem1640511 x)). Qed.
Lemma lem1640514 (x : real) (y : real) : term16 x y.
Proof. exact (@lem1640513 x y). Qed.
Lemma lem1640515 (x : real) (y : real) : (term16 x y) = (((real_mul x y) = term17) = (term18 x y)).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1640517 (x : real) : term19 x.
Proof. exact (@lem1640510 x). Qed.
Lemma lem1640518 (x : real) : (term19 x) = (term9 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1640519 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1640518 x) (@lem1640517 x)). Qed.
Lemma lem1640520 (x : real) (y : real) : term20 x y.
Proof. exact (@lem1640519 x y). Qed.
Lemma lem1640521 (x : real) (y : real) : (term20 x y) = (term5 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1640522 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem1640521 x y) (@lem1640520 x y)). Qed.
Lemma lem1640523 (x : real) (y : real) (z : real) : term21 x y z.
Proof. exact (@lem1640522 x y z). Qed.
Lemma lem1640524 (x : real) (y : real) (z : real) : (term21 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term21 x y z)). Qed.
Lemma lem1640526 (x : real) : term22 x.
Proof. exact (@lem1518006 x). Qed.
Lemma lem1640527 (x : real) : (term22 x) = ((term23 x) = x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1640531 (x : real) (y : real) (h1 : ((real_sub x y) = term17) = (x = y)) : ((real_sub x y) = term17) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1640532 (x : real) (y : real) (h1 : ((real_sub x y) = term17) = (x = y)) : (x = y) = ((real_sub x y) = term17).
Proof. exact (SYM (@lem1640531 x y h1)). Qed.
Lemma lem1640533 (x : real) (y : real) (h1 : (x = y) = ((real_sub x y) = term17)) : (x = y) = ((real_sub x y) = term17).
Proof. exact (h1). Qed.
Lemma lem1640534 (x : real) (y : real) (h1 : (x = y) = ((real_sub x y) = term17)) : ((real_sub x y) = term17) = (x = y).
Proof. exact (SYM (@lem1640533 x y h1)). Qed.
Lemma lem1640535 (x : real) (y : real) : (((real_sub x y) = term17) = (x = y)) = ((x = y) = ((real_sub x y) = term17)).
Proof. exact (prop_ext (fun h1 : ((real_sub x y) = term17) = (x = y) => @lem1640532 x y h1) (fun h1 : (x = y) = ((real_sub x y) = term17) => @lem1640534 x y h1)). Qed.
Lemma lem1640536 (x : real) : (term24 x) = (term25 x).
Proof. exact (fun_ext (fun y : real => @lem1640535 x y)). Qed.
Lemma lem1640537 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1640538 (x : real) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem1640537) (@lem1640536 x)). Qed.
Lemma lem1640539 : term28 = term29.
Proof. exact (fun_ext (fun x : real => @lem1640538 x)). Qed.
Lemma lem1640540 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1640541 : term30 = term31.
Proof. exact (MK_COMB (@lem1640540) (@lem1640539)). Qed.
Lemma lem1640542 : term31.
Proof. exact (EQ_MP (@lem1640541) (@lem1376695)). Qed.
Lemma lem1640543 (x : real) : term32 x.
Proof. exact (@lem1640542 x). Qed.
Lemma lem1640544 (x : real) : (term32 x) = (term27 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1640545 (x : real) : term27 x.
Proof. exact (EQ_MP (@lem1640544 x) (@lem1640543 x)). Qed.
Lemma lem1640546 (x : real) (y : real) : term33 x y.
Proof. exact (@lem1640545 x y). Qed.
Lemma lem1640547 (x : real) (y : real) : (term33 x y) = ((x = y) = ((real_sub x y) = term17)).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem1640556 (x : real) (y : real) : (x = y) = ((real_sub x y) = term17).
Proof. exact (EQ_MP (@lem1640547 x y) (@lem1640546 x y)). Qed.
Lemma lem1640557 (z : real) : (z = term17) = ((term23 z) = term17).
Proof. exact (@lem1640556 z term17). Qed.
Lemma lem1640558 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1640559 (z : real) : (term34 z) = (term35 z).
Proof. exact (MK_COMB (@lem1640558) (@lem1640557 z)). Qed.
Lemma lem1640560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1640561 (z : real) : (term36 z) = (term37 z).
Proof. exact (MK_COMB (@lem1640560) (@lem1640559 z)). Qed.
Lemma lem1640565 (x : real) (y : real) : (x = y) = ((real_sub x y) = term17).
Proof. exact (EQ_MP (@lem1640547 x y) (@lem1640546 x y)). Qed.
Lemma lem1640566 (x : real) (y : real) (z : real) : ((real_mul x z) = (real_mul y z)) = ((term1 x y z) = term17).
Proof. exact (@lem1640565 (real_mul x z) (real_mul y z)). Qed.
Lemma lem1640567 (x : real) (y : real) (z : real) : (term38 x y z) = (term39 x y z).
Proof. exact (MK_COMB (@lem1640561 z) (@lem1640566 x y z)). Qed.
Lemma lem1640568 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1640569 (x : real) (y : real) (z : real) : (term40 x y z) = (term41 x y z).
Proof. exact (MK_COMB (@lem1640568) (@lem1640567 x y z)). Qed.
Lemma lem1640573 (x : real) (y : real) : (x = y) = ((real_sub x y) = term17).
Proof. exact (EQ_MP (@lem1640547 x y) (@lem1640546 x y)). Qed.
Lemma lem1640574 (z : real) (x : real) (y : real) : (term42 z x y) = (term43 z x y).
Proof. exact (MK_COMB (@lem1640569 x y z) (@lem1640573 x y)). Qed.
Lemma lem1640575 (z : real) (x : real) (y : real) : (term43 z x y) = (term42 z x y).
Proof. exact (SYM (@lem1640574 z x y)). Qed.
Lemma lem1640583 (x : real) : (term23 x) = x.
Proof. exact (EQ_MP (@lem1640527 x) (@lem1640526 x)). Qed.
Lemma lem1640584 (z : real) : (term23 z) = z.
Proof. exact (@lem1640583 z). Qed.
Lemma lem1640585 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1640586 (z : real) : (term44 z) = (@eq real z).
Proof. exact (MK_COMB (@lem1640585) (@lem1640584 z)). Qed.
Lemma lem1640587 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1640588 (z : real) : ((term23 z) = term17) = (z = term17).
Proof. exact (MK_COMB (@lem1640586 z) (@lem1640587)). Qed.
Lemma lem1640591 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1640592 (z : real) : (term35 z) = (term34 z).
Proof. exact (MK_COMB (@lem1640591) (@lem1640588 z)). Qed.
Lemma lem1640593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1640594 (z : real) : (term37 z) = (term36 z).
Proof. exact (MK_COMB (@lem1640593) (@lem1640592 z)). Qed.
Lemma lem1640598 (x : real) (y : real) (z : real) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1640524 x y z) (@lem1640523 x y z)). Qed.
Lemma lem1640599 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1640600 (x : real) (y : real) (z : real) : (term45 x y z) = (term46 x y z).
Proof. exact (MK_COMB (@lem1640599) (@lem1640598 x y z)). Qed.
Lemma lem1640601 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1640602 (x : real) (y : real) (z : real) : ((term1 x y z) = term17) = ((term0 x y z) = term17).
Proof. exact (MK_COMB (@lem1640600 x y z) (@lem1640601)). Qed.
Lemma lem1640604 (x : real) (y : real) : ((real_mul x y) = term17) = (term18 x y).
Proof. exact (EQ_MP (@lem1640515 x y) (@lem1640514 x y)). Qed.
Lemma lem1640605 (x : real) (y : real) (z : real) : ((term0 x y z) = term17) = (term47 x y z).
Proof. exact (@lem1640604 (real_sub x y) z). Qed.
Lemma lem1640612 (x : real) (y : real) (z : real) : ((term1 x y z) = term17) = (term47 x y z).
Proof. exact (TRANS (@lem1640602 x y z) (@lem1640605 x y z)). Qed.
Lemma lem1640613 (x : real) (y : real) (z : real) : (term39 x y z) = (term48 x y z).
Proof. exact (MK_COMB (@lem1640594 z) (@lem1640612 x y z)). Qed.
Lemma lem1640616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1640617 (x : real) (y : real) (z : real) : (term41 x y z) = (term49 x y z).
Proof. exact (MK_COMB (@lem1640616) (@lem1640613 x y z)). Qed.
Lemma lem1640620 (x : real) (y : real) : ((real_sub x y) = term17) = ((real_sub x y) = term17).
Proof. exact (eq_refl ((real_sub x y) = term17)). Qed.
Lemma lem1640621 (z : real) (x : real) (y : real) : (term43 z x y) = (term50 z x y).
Proof. exact (MK_COMB (@lem1640617 x y z) (@lem1640620 x y)). Qed.
Lemma lem1640624 (z : real) (x : real) (y : real) : (term50 z x y) = (term43 z x y).
Proof. exact (SYM (@lem1640621 z x y)). Qed.
Lemma lem1640641 (z : real) : term51 z.
Proof. exact (@lem9851 (z = term17)). Qed.
Lemma lem1640642 (z : real) : (term51 z) = (term52 z).
Proof. exact (eq_refl (term51 z)). Qed.
Lemma lem1640643 (z : real) : term52 z.
Proof. exact (EQ_MP (@lem1640642 z) (@lem1640641 z)). Qed.
Lemma lem1640644 (z : real) (h1 : (z = term17) = True) : (z = term17) = True.
Proof. exact (h1). Qed.
Lemma lem1640645 (z : real) (h1 : (z = term17) = False) : (z = term17) = False.
Proof. exact (h1). Qed.
Lemma lem1640662 (x : real) (y : real) : (term53 x y) = (term53 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem1640663 (x : real) (y : real) (z : real) (h1 : (z = term17) = True) : (term54 x y z) = (term55 x y).
Proof. exact (MK_COMB (@lem1640662 x y) (@lem1640644 z h1)). Qed.
Lemma lem1640664 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1640665 (x : real) (y : real) (z : real) : (term57 x y z) = (term57 x y z).
Proof. exact (eq_refl (term57 x y z)). Qed.
Lemma lem1640666 (z : real) (x : real) (y : real) : ((term54 x y z) = (term55 x y)) = ((term54 x y z) = (term56 x y)).
Proof. exact (MK_COMB (@lem1640665 x y z) (@lem1640664 x y)). Qed.
Lemma lem1640667 (z : real) (x : real) (y : real) : (term54 x y z) = (term50 z x y).
Proof. exact (eq_refl (term54 x y z)). Qed.
Lemma lem1640668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1640669 (z : real) (x : real) (y : real) : (term57 x y z) = (term58 z x y).
Proof. exact (MK_COMB (@lem1640668) (@lem1640667 z x y)). Qed.
Lemma lem1640670 (x : real) (y : real) : (term56 x y) = (term56 x y).
Proof. exact (eq_refl (term56 x y)). Qed.
Lemma lem1640671 (z : real) (x : real) (y : real) : ((term54 x y z) = (term56 x y)) = ((term50 z x y) = (term56 x y)).
Proof. exact (MK_COMB (@lem1640669 z x y) (@lem1640670 x y)). Qed.
Lemma lem1640672 (z : real) (x : real) (y : real) : ((term54 x y z) = (term55 x y)) = ((term50 z x y) = (term56 x y)).
Proof. exact (TRANS (@lem1640666 z x y) (@lem1640671 z x y)). Qed.
Lemma lem1640673 (x : real) (y : real) (z : real) (h1 : (z = term17) = True) : (term50 z x y) = (term56 x y).
Proof. exact (EQ_MP (@lem1640672 z x y) (@lem1640663 x y z h1)). Qed.
Lemma lem1640674 (x : real) (y : real) (z : real) (h1 : (z = term17) = True) : (term56 x y) = (term50 z x y).
Proof. exact (SYM (@lem1640673 x y z h1)). Qed.
Lemma lem1640675 (x : real) (y : real) : (term53 x y) = (term53 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem1640676 (x : real) (y : real) (z : real) (h1 : (z = term17) = False) : (term54 x y z) = (term59 x y).
Proof. exact (MK_COMB (@lem1640675 x y) (@lem1640645 z h1)). Qed.
Lemma lem1640677 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (eq_refl (term59 x y)). Qed.
Lemma lem1640678 (x : real) (y : real) (z : real) : (term57 x y z) = (term57 x y z).
Proof. exact (eq_refl (term57 x y z)). Qed.
Lemma lem1640679 (z : real) (x : real) (y : real) : ((term54 x y z) = (term59 x y)) = ((term54 x y z) = (term60 x y)).
Proof. exact (MK_COMB (@lem1640678 x y z) (@lem1640677 x y)). Qed.
Lemma lem1640680 (z : real) (x : real) (y : real) : (term54 x y z) = (term50 z x y).
Proof. exact (eq_refl (term54 x y z)). Qed.
Lemma lem1640681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1640682 (z : real) (x : real) (y : real) : (term57 x y z) = (term58 z x y).
Proof. exact (MK_COMB (@lem1640681) (@lem1640680 z x y)). Qed.
Lemma lem1640683 (x : real) (y : real) : (term60 x y) = (term60 x y).
Proof. exact (eq_refl (term60 x y)). Qed.
Lemma lem1640684 (z : real) (x : real) (y : real) : ((term54 x y z) = (term60 x y)) = ((term50 z x y) = (term60 x y)).
Proof. exact (MK_COMB (@lem1640682 z x y) (@lem1640683 x y)). Qed.
Lemma lem1640685 (z : real) (x : real) (y : real) : ((term54 x y z) = (term59 x y)) = ((term50 z x y) = (term60 x y)).
Proof. exact (TRANS (@lem1640679 z x y) (@lem1640684 z x y)). Qed.
Lemma lem1640686 (x : real) (y : real) (z : real) (h1 : (z = term17) = False) : (term50 z x y) = (term60 x y).
Proof. exact (EQ_MP (@lem1640685 z x y) (@lem1640676 x y z h1)). Qed.
Lemma lem1640687 (x : real) (y : real) (z : real) (h1 : (z = term17) = False) : (term60 x y) = (term50 z x y).
Proof. exact (SYM (@lem1640686 x y z h1)). Qed.
Lemma lem1640693 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1640694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1640695 : term61 = (and False).
Proof. exact (MK_COMB (@lem1640694) (@lem1640693)). Qed.
Lemma lem1640697 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1640698 (x : real) (y : real) : (term62 x y) = True.
Proof. exact (@lem1640697 ((real_sub x y) = term17)). Qed.
Lemma lem1640699 (x : real) (y : real) : (term63 x y) = (False /\ True).
Proof. exact (MK_COMB (@lem1640695) (@lem1640698 x y)). Qed.
Lemma lem1640701 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1640702 : (False /\ True) = False.
Proof. exact (@lem1640701 True). Qed.
Lemma lem1640703 (x : real) (y : real) : (term63 x y) = False.
Proof. exact (TRANS (@lem1640699 x y) (@lem1640702)). Qed.
Lemma lem1640704 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1640705 (x : real) (y : real) : (term64 x y) = (imp False).
Proof. exact (MK_COMB (@lem1640704) (@lem1640703 x y)). Qed.
Lemma lem1640708 (x : real) (y : real) : ((real_sub x y) = term17) = ((real_sub x y) = term17).
Proof. exact (eq_refl ((real_sub x y) = term17)). Qed.
Lemma lem1640709 (x : real) (y : real) : (term56 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1640705 x y) (@lem1640708 x y)). Qed.
Lemma lem1640711 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1640712 (x : real) (y : real) : (term65 x y) = True.
Proof. exact (@lem1640711 ((real_sub x y) = term17)). Qed.
Lemma lem1640713 (x : real) (y : real) : (term56 x y) = True.
Proof. exact (TRANS (@lem1640709 x y) (@lem1640712 x y)). Qed.
Lemma lem1640714 (x : real) (y : real) : True = (term56 x y).
Proof. exact (SYM (@lem1640713 x y)). Qed.
Lemma lem1640715 (x : real) (y : real) : term56 x y.
Proof. exact (EQ_MP (@lem1640714 x y) (@lem0)). Qed.
Lemma lem1640721 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1640722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1640723 : term66 = (and True).
Proof. exact (MK_COMB (@lem1640722) (@lem1640721)). Qed.
Lemma lem1640725 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1640726 (x : real) (y : real) : (term67 x y) = ((real_sub x y) = term17).
Proof. exact (@lem1640725 ((real_sub x y) = term17)). Qed.
Lemma lem1640729 (x : real) (y : real) : (term68 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1640723) (@lem1640726 x y)). Qed.
Lemma lem1640731 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1640732 (x : real) (y : real) : (term69 x y) = ((real_sub x y) = term17).
Proof. exact (@lem1640731 ((real_sub x y) = term17)). Qed.
Lemma lem1640735 (x : real) (y : real) : (term68 x y) = ((real_sub x y) = term17).
Proof. exact (TRANS (@lem1640729 x y) (@lem1640732 x y)). Qed.
Lemma lem1640736 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1640737 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1640736) (@lem1640735 x y)). Qed.
Lemma lem1640740 (x : real) (y : real) : ((real_sub x y) = term17) = ((real_sub x y) = term17).
Proof. exact (eq_refl ((real_sub x y) = term17)). Qed.
Lemma lem1640741 (x : real) (y : real) : (term60 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1640737 x y) (@lem1640740 x y)). Qed.
Lemma lem1640745 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1640746 (x : real) (y : real) : (term72 x y) = True.
Proof. exact (@lem1640745 ((real_sub x y) = term17)). Qed.
Lemma lem1640747 (x : real) (y : real) : (term60 x y) = True.
Proof. exact (TRANS (@lem1640741 x y) (@lem1640746 x y)). Qed.
Lemma lem1640748 (x : real) (y : real) : True = (term60 x y).
Proof. exact (SYM (@lem1640747 x y)). Qed.
Lemma lem1640749 (x : real) (y : real) : term60 x y.
Proof. exact (EQ_MP (@lem1640748 x y) (@lem0)). Qed.
Lemma lem1640750 (x : real) (y : real) (z : real) (h1 : (z = term17) = False) : term50 z x y.
Proof. exact (EQ_MP (@lem1640687 x y z h1) (@lem1640749 x y)). Qed.
Lemma lem1640751 (x : real) (y : real) (z : real) (h1 : (z = term17) = True) : term50 z x y.
Proof. exact (EQ_MP (@lem1640674 x y z h1) (@lem1640715 x y)). Qed.
Lemma lem1640754 (z : real) (x : real) (y : real) : term50 z x y.
Proof. exact (or_elim (@lem1640643 z) (fun h0 : (z = term17) = True => @lem1640751 x y z h0) (fun h0 : (z = term17) = False => @lem1640750 x y z h0)). Qed.
Lemma lem1640755 (z : real) (x : real) (y : real) : term43 z x y.
Proof. exact (EQ_MP (@lem1640624 z x y) (@lem1640754 z x y)). Qed.
Lemma lem1640756 (z : real) (x : real) (y : real) : term42 z x y.
Proof. exact (EQ_MP (@lem1640575 z x y) (@lem1640755 z x y)). Qed.
Lemma lem1640761 (x : real) (y : real) : term73 x y.
Proof. exact (fun z : real => @lem1640756 z x y). Qed.
Lemma lem1640766 (x : real) : term74 x.
Proof. exact (fun y : real => @lem1640761 x y). Qed.
Lemma lem1640771 : term75.
Proof. exact (fun x : real => @lem1640766 x). Qed.
