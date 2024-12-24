Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_LDIV_EQ_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_LE_RMUL_EQ_spec.
Require Import REAL_LT_IMP_NZ_spec.
Require Import REAL_MUL_RID_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1338912_spec.
Require Import thm1340174_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1628578 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem1628579 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem1628578 x y z h1)). Qed.
Lemma lem1628580 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1628581 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem1628580 x y z h1)). Qed.
Lemma lem1628582 (x : real) (y : real) (z : real) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem1628579 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem1628581 x y z h1)). Qed.
Lemma lem1628583 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : real => @lem1628582 x y z)). Qed.
Lemma lem1628584 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628585 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1628584) (@lem1628583 x y)). Qed.
Lemma lem1628586 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1628585 x y)). Qed.
Lemma lem1628587 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628588 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1628587) (@lem1628586 x)). Qed.
Lemma lem1628589 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1628588 x)). Qed.
Lemma lem1628590 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628591 : term12 = term13.
Proof. exact (MK_COMB (@lem1628590) (@lem1628589)). Qed.
Lemma lem1628592 : term13.
Proof. exact (EQ_MP (@lem1628591) (@lem1338912)). Qed.
Lemma lem1628593 (z : real) (h1 : term14 z) : term14 z.
Proof. exact (h1). Qed.
Lemma lem1628594 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem1628595 (x : real) (h1 : term15) : term16 x.
Proof. exact (@lem1628594 h1 x). Qed.
Lemma lem1628596 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1628597 (x : real) (h1 : term15) : term17 x.
Proof. exact (EQ_MP (@lem1628596 x) (@lem1628595 x h1)). Qed.
Lemma lem1628598 (x : real) (y : real) (h1 : term15) : term18 x y.
Proof. exact (@lem1628597 x h1 y). Qed.
Lemma lem1628599 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1628600 (x : real) (y : real) (h1 : term15) : term19 x y.
Proof. exact (EQ_MP (@lem1628599 x y) (@lem1628598 x y h1)). Qed.
Lemma lem1628601 (x : real) (y : real) (z : real) (h1 : term15) : term20 x y z.
Proof. exact (@lem1628600 x y h1 z). Qed.
Lemma lem1628602 (z : real) (x : real) (y : real) : (term20 x y z) = (term21 z x y).
Proof. exact (eq_refl (term20 x y z)). Qed.
Lemma lem1628603 (z : real) (x : real) (y : real) (h1 : term15) : term21 z x y.
Proof. exact (EQ_MP (@lem1628602 z x y) (@lem1628601 x y z h1)). Qed.
Lemma lem1628604 (z : real) (h1 : term14 z) : term14 z.
Proof. exact (h1). Qed.
Lemma lem1628605 (x : real) (y : real) (z : real) (h1 : term15) (h2 : term14 z) : (term22 x y z) = (real_le x y).
Proof. exact (@lem1628603 z x y h1 (@lem1628604 z h2)). Qed.
Lemma lem1628606 (x : real) (z : real) (h1 : term15) (h2 : term14 z) : term23 z x.
Proof. exact (fun y : real => @lem1628605 x y z h1 h2). Qed.
Lemma lem1628607 (z : real) (h1 : term15) (h2 : term14 z) : term24 z.
Proof. exact (fun x : real => @lem1628606 x z h1 h2). Qed.
Lemma lem1628608 (z : real) (h1 : term15) : term25 z.
Proof. exact (fun h0 : term14 z => @lem1628607 z h1 h0). Qed.
Lemma lem1628609 (h1 : term15) : term26.
Proof. exact (fun z : real => @lem1628608 z h1). Qed.
Lemma lem1628610 : term27.
Proof. exact (fun h0 : term15 => @lem1628609 h0). Qed.
Lemma lem1628611 : term26.
Proof. exact (@lem1628610 (@lem1600741)). Qed.
Lemma lem1628612 (z : real) : term28 z.
Proof. exact (@lem1628611 z). Qed.
Lemma lem1628613 (z : real) : (term28 z) = (term25 z).
Proof. exact (eq_refl (term28 z)). Qed.
Lemma lem1628616 (z : real) : term25 z.
Proof. exact (EQ_MP (@lem1628613 z) (@lem1628612 z)). Qed.
Lemma lem1628617 (z : real) (h1 : term14 z) : term24 z.
Proof. exact (@lem1628616 z (@lem1628593 z h1)). Qed.
Lemma lem1628620 (z : real) (x : real) (y : real) (h1 : (term22 x y z) = (real_le x y)) : (term22 x y z) = (real_le x y).
Proof. exact (h1). Qed.
Lemma lem1628621 (z : real) (x : real) (y : real) (h1 : (term22 x y z) = (real_le x y)) : (real_le x y) = (term22 x y z).
Proof. exact (SYM (@lem1628620 z x y h1)). Qed.
Lemma lem1628622 (x : real) (y : real) (z : real) (h1 : (real_le x y) = (term22 x y z)) : (real_le x y) = (term22 x y z).
Proof. exact (h1). Qed.
Lemma lem1628623 (x : real) (y : real) (z : real) (h1 : (real_le x y) = (term22 x y z)) : (term22 x y z) = (real_le x y).
Proof. exact (SYM (@lem1628622 x y z h1)). Qed.
Lemma lem1628624 (x : real) (y : real) (z : real) : ((term22 x y z) = (real_le x y)) = ((real_le x y) = (term22 x y z)).
Proof. exact (prop_ext (fun h1 : (term22 x y z) = (real_le x y) => @lem1628621 z x y h1) (fun h1 : (real_le x y) = (term22 x y z) => @lem1628623 x y z h1)). Qed.
Lemma lem1628625 (x : real) (z : real) : (term29 z x) = (term30 x z).
Proof. exact (fun_ext (fun y : real => @lem1628624 x y z)). Qed.
Lemma lem1628626 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628627 (x : real) (z : real) : (term23 z x) = (term31 x z).
Proof. exact (MK_COMB (@lem1628626) (@lem1628625 x z)). Qed.
Lemma lem1628628 (z : real) : (term32 z) = (term33 z).
Proof. exact (fun_ext (fun x : real => @lem1628627 x z)). Qed.
Lemma lem1628629 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1628630 (z : real) : (term24 z) = (term34 z).
Proof. exact (MK_COMB (@lem1628629) (@lem1628628 z)). Qed.
Lemma lem1628631 (z : real) (h1 : term14 z) : term34 z.
Proof. exact (EQ_MP (@lem1628630 z) (@lem1628617 z h1)). Qed.
Lemma lem1628632 (x : real) (z : real) (h1 : term14 z) : term35 z x.
Proof. exact (@lem1628631 z h1 x). Qed.
Lemma lem1628633 (x : real) (z : real) : (term35 z x) = (term31 x z).
Proof. exact (eq_refl (term35 z x)). Qed.
Lemma lem1628634 (x : real) (z : real) (h1 : term14 z) : term31 x z.
Proof. exact (EQ_MP (@lem1628633 x z) (@lem1628632 x z h1)). Qed.
Lemma lem1628635 (x : real) (y : real) (z : real) (h1 : term14 z) : term36 x z y.
Proof. exact (@lem1628634 x z h1 y). Qed.
Lemma lem1628636 (x : real) (y : real) (z : real) : (term36 x z y) = ((real_le x y) = (term22 x y z)).
Proof. exact (eq_refl (term36 x z y)). Qed.
Lemma lem1628639 (x : real) (y : real) (z : real) (h1 : term14 z) : (real_le x y) = (term22 x y z).
Proof. exact (EQ_MP (@lem1628636 x y z) (@lem1628635 x y z h1)). Qed.
Lemma lem1628640 (x : real) (y : real) (z : real) (h1 : term14 z) : (term37 x z y) = (term38 x y z).
Proof. exact (@lem1628639 (real_div x z) y z h1). Qed.
Lemma lem1628641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1628642 (x : real) (y : real) (z : real) (h1 : term14 z) : (term39 x z y) = (term40 x y z).
Proof. exact (MK_COMB (@lem1628641) (@lem1628640 x y z h1)). Qed.
Lemma lem1628643 (x : real) (y : real) (z : real) : (term41 x y z) = (term41 x y z).
Proof. exact (eq_refl (term41 x y z)). Qed.
Lemma lem1628644 (x : real) (y : real) (z : real) (h1 : term14 z) : ((term37 x z y) = (term41 x y z)) = ((term38 x y z) = (term41 x y z)).
Proof. exact (MK_COMB (@lem1628642 x y z h1) (@lem1628643 x y z)). Qed.
Lemma lem1628645 (x : real) (y : real) (z : real) (h1 : term14 z) : ((term38 x y z) = (term41 x y z)) = ((term37 x z y) = (term41 x y z)).
Proof. exact (SYM (@lem1628644 x y z h1)). Qed.
Lemma lem1628646 (x : real) : term42 x.
Proof. exact (@lem1523977 x). Qed.
Lemma lem1628647 (x : real) : (term42 x) = (term43 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1628648 (x : real) : term43 x.
Proof. exact (EQ_MP (@lem1628647 x) (@lem1628646 x)). Qed.
Lemma lem1628649 (x : real) (h1 : term14 x) : term14 x.
Proof. exact (h1). Qed.
Lemma lem1628650 (x : real) (h1 : term14 x) : term44 x.
Proof. exact (@lem1628648 x (@lem1628649 x h1)). Qed.
Lemma lem1628651 (x : real) : term45 x.
Proof. exact (@lem82 (x = term46)). Qed.
Lemma lem1628652 (x : real) (h1 : term14 x) : (x = term46) = False.
Proof. exact (@lem1628651 x (@lem1628650 x h1)). Qed.
Lemma lem1628674 (x : real) : term47 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1628675 (x : real) : (term47 x) = ((term48 x) = x).
Proof. exact (eq_refl (term47 x)). Qed.
Lemma lem1628677 (x : real) : term49 x.
Proof. exact (@lem1340174 x). Qed.
Lemma lem1628678 (x : real) : (term49 x) = (term50 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1628679 (x : real) : term50 x.
Proof. exact (EQ_MP (@lem1628678 x) (@lem1628677 x)). Qed.
Lemma lem1628680 (x : real) (h1 : term44 x) : term44 x.
Proof. exact (h1). Qed.
Lemma lem1628681 (x : real) (h1 : term44 x) : (term51 x) = term52.
Proof. exact (@lem1628679 x (@lem1628680 x h1)). Qed.
Lemma lem1628687 (x : real) : term53 x.
Proof. exact (@lem1628592 x). Qed.
Lemma lem1628688 (x : real) : (term53 x) = (term9 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1628689 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1628688 x) (@lem1628687 x)). Qed.
Lemma lem1628690 (x : real) (y : real) : term54 x y.
Proof. exact (@lem1628689 x y). Qed.
Lemma lem1628691 (x : real) (y : real) : (term54 x y) = (term5 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1628692 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem1628691 x y) (@lem1628690 x y)). Qed.
Lemma lem1628693 (x : real) (y : real) (z : real) : term55 x y z.
Proof. exact (@lem1628692 x y z). Qed.
Lemma lem1628694 (x : real) (y : real) (z : real) : (term55 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term55 x y z)). Qed.
Lemma lem1628696 (x : real) : term56 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1628697 (x : real) : (term56 x) = (term57 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1628698 (x : real) : term57 x.
Proof. exact (EQ_MP (@lem1628697 x) (@lem1628696 x)). Qed.
Lemma lem1628699 (x : real) (y : real) : term58 x y.
Proof. exact (@lem1628698 x y). Qed.
Lemma lem1628700 (x : real) (y : real) : (term58 x y) = ((real_div x y) = (term59 x y)).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1628702 (z : real) : (term14 z) = ((term14 z) = True).
Proof. exact (@lem7 (term14 z)). Qed.
Lemma lem1628707 (x : real) (y : real) : (real_div x y) = (term59 x y).
Proof. exact (EQ_MP (@lem1628700 x y) (@lem1628699 x y)). Qed.
Lemma lem1628708 (x : real) (z : real) : (real_div x z) = (term59 x z).
Proof. exact (@lem1628707 x z). Qed.
Lemma lem1628709 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1628710 (x : real) (z : real) : (term60 x z) = (term61 x z).
Proof. exact (MK_COMB (@lem1628709) (@lem1628708 x z)). Qed.
Lemma lem1628711 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1628712 (x : real) (z : real) : (term62 x z) = (term63 x z).
Proof. exact (MK_COMB (@lem1628710 x z) (@lem1628711 z)). Qed.
Lemma lem1628714 (x : real) (y : real) (z : real) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1628694 x y z) (@lem1628693 x y z)). Qed.
Lemma lem1628715 (x : real) (z : real) : (term63 x z) = (term64 x z).
Proof. exact (@lem1628714 x (real_inv z) z). Qed.
Lemma lem1628717 (x : real) : term50 x.
Proof. exact (fun h0 : term44 x => @lem1628681 x h0). Qed.
Lemma lem1628718 (z : real) : term50 z.
Proof. exact (@lem1628717 z). Qed.
Lemma lem1628720 (x : real) : term65 x.
Proof. exact (fun h0 : term14 x => @lem1628652 x h0). Qed.
Lemma lem1628721 (z : real) : term65 z.
Proof. exact (@lem1628720 z). Qed.
Lemma lem1628723 (z : real) (h1 : term14 z) : (term14 z) = True.
Proof. exact (EQ_MP (@lem1628702 z) (@lem1628593 z h1)). Qed.
Lemma lem1628724 (z : real) (h1 : term14 z) : True = (term14 z).
Proof. exact (SYM (@lem1628723 z h1)). Qed.
Lemma lem1628725 (z : real) (h1 : term14 z) : term14 z.
Proof. exact (EQ_MP (@lem1628724 z h1) (@lem0)). Qed.
Lemma lem1628726 (z : real) (h1 : term14 z) : (z = term46) = False.
Proof. exact (@lem1628721 z (@lem1628725 z h1)). Qed.
Lemma lem1628727 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1628728 (z : real) (h1 : term14 z) : (term44 z) = (~ False).
Proof. exact (MK_COMB (@lem1628727) (@lem1628726 z h1)). Qed.
Lemma lem1628730 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1628731 (z : real) (h1 : term14 z) : (term44 z) = True.
Proof. exact (TRANS (@lem1628728 z h1) (@lem1628730)). Qed.
Lemma lem1628732 (z : real) (h1 : term14 z) : True = (term44 z).
Proof. exact (SYM (@lem1628731 z h1)). Qed.
Lemma lem1628733 (z : real) (h1 : term14 z) : term44 z.
Proof. exact (EQ_MP (@lem1628732 z h1) (@lem0)). Qed.
Lemma lem1628734 (z : real) (h1 : term14 z) : (term51 z) = term52.
Proof. exact (@lem1628718 z (@lem1628733 z h1)). Qed.
Lemma lem1628735 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1628736 (x : real) (z : real) (h1 : term14 z) : (term64 x z) = (term48 x).
Proof. exact (MK_COMB (@lem1628735 x) (@lem1628734 z h1)). Qed.
Lemma lem1628738 (x : real) : (term48 x) = x.
Proof. exact (EQ_MP (@lem1628675 x) (@lem1628674 x)). Qed.
Lemma lem1628739 (x : real) (z : real) (h1 : term14 z) : (term64 x z) = x.
Proof. exact (TRANS (@lem1628736 x z h1) (@lem1628738 x)). Qed.
Lemma lem1628740 (x : real) (z : real) (h1 : term14 z) : (term63 x z) = x.
Proof. exact (TRANS (@lem1628715 x z) (@lem1628739 x z h1)). Qed.
Lemma lem1628741 (x : real) (z : real) (h1 : term14 z) : (term62 x z) = x.
Proof. exact (TRANS (@lem1628712 x z) (@lem1628740 x z h1)). Qed.
Lemma lem1628742 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1628743 (x : real) (z : real) (h1 : term14 z) : (term66 x z) = (real_le x).
Proof. exact (MK_COMB (@lem1628742) (@lem1628741 x z h1)). Qed.
Lemma lem1628744 (y : real) (z : real) : (real_mul y z) = (real_mul y z).
Proof. exact (eq_refl (real_mul y z)). Qed.
Lemma lem1628745 (x : real) (y : real) (z : real) (h1 : term14 z) : (term38 x y z) = (term41 x y z).
Proof. exact (MK_COMB (@lem1628743 x z h1) (@lem1628744 y z)). Qed.
Lemma lem1628746 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1628747 (x : real) (y : real) (z : real) (h1 : term14 z) : (term40 x y z) = (term67 x y z).
Proof. exact (MK_COMB (@lem1628746) (@lem1628745 x y z h1)). Qed.
Lemma lem1628748 (x : real) (y : real) (z : real) : (term41 x y z) = (term41 x y z).
Proof. exact (eq_refl (term41 x y z)). Qed.
Lemma lem1628749 (x : real) (y : real) (z : real) (h1 : term14 z) : ((term38 x y z) = (term41 x y z)) = ((term41 x y z) = (term41 x y z)).
Proof. exact (MK_COMB (@lem1628747 x y z h1) (@lem1628748 x y z)). Qed.
Lemma lem1628751 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1628752 (x : Prop) : (x = x) = True.
Proof. exact (@lem1628751 Prop x). Qed.
Lemma lem1628753 (x : real) (y : real) (z : real) : ((term41 x y z) = (term41 x y z)) = True.
Proof. exact (@lem1628752 (term41 x y z)). Qed.
Lemma lem1628754 (x : real) (y : real) (z : real) (h1 : term14 z) : ((term38 x y z) = (term41 x y z)) = True.
Proof. exact (TRANS (@lem1628749 x y z h1) (@lem1628753 x y z)). Qed.
Lemma lem1628755 (x : real) (y : real) (z : real) (h1 : term14 z) : True = ((term38 x y z) = (term41 x y z)).
Proof. exact (SYM (@lem1628754 x y z h1)). Qed.
Lemma lem1628756 (x : real) (y : real) (z : real) (h1 : term14 z) : (term38 x y z) = (term41 x y z).
Proof. exact (EQ_MP (@lem1628755 x y z h1) (@lem0)). Qed.
Lemma lem1628757 (x : real) (y : real) (z : real) (h1 : term14 z) : (term37 x z y) = (term41 x y z).
Proof. exact (EQ_MP (@lem1628645 x y z h1) (@lem1628756 x y z h1)). Qed.
Lemma lem1628758 (x : real) (y : real) (z : real) (h1 : term14 z) : (term14 z) = ((term37 x z y) = (term41 x y z)).
Proof. exact (prop_ext (fun h2 : term14 z => @lem1628757 x y z h1) (fun h2 : (term37 x z y) = (term41 x y z) => @lem1628593 z h1)). Qed.
Lemma lem1628759 (x : real) (y : real) (z : real) (h1 : term14 z) : (term37 x z y) = (term41 x y z).
Proof. exact (EQ_MP (@lem1628758 x y z h1) (@lem1628593 z h1)). Qed.
Lemma lem1628760 (x : real) (y : real) (z : real) : term68 x y z.
Proof. exact (fun h0 : term14 z => @lem1628759 x y z h0). Qed.
Lemma lem1628765 (x : real) (y : real) : term69 x y.
Proof. exact (fun z : real => @lem1628760 x y z). Qed.
Lemma lem1628770 (x : real) : term70 x.
Proof. exact (fun y : real => @lem1628765 x y). Qed.
Lemma lem1628775 : term71.
Proof. exact (fun x : real => @lem1628770 x). Qed.
