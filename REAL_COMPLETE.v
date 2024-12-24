Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_COMPLETE_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_COMPLETE_SOMEPOS_spec.
Require Import real_sub_spec.
Require Import thm0_spec.
Require Import thm1157_spec.
Require Import thm1338238_spec.
Require Import thm1338438_spec.
Require Import thm1338512_spec.
Require Import thm1338588_spec.
Require Import thm1339240_spec.
Require Import thm1339697_spec.
Require Import thm1339889_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem1349590 (x : real) : term0 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1349591 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1349593 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1349594 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1349595 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1349594 x) (@lem1349593 x)). Qed.
Lemma lem1349596 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1349595 x y). Qed.
Lemma lem1349597 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1349602 (x : real) (y : real) (z : real) (h1 : (term5 x y z) = (term6 x y z)) : (term5 x y z) = (term6 x y z).
Proof. exact (h1). Qed.
Lemma lem1349603 (x : real) (y : real) (z : real) (h1 : (term5 x y z) = (term6 x y z)) : (term6 x y z) = (term5 x y z).
Proof. exact (SYM (@lem1349602 x y z h1)). Qed.
Lemma lem1349604 (x : real) (y : real) (z : real) (h1 : (term6 x y z) = (term5 x y z)) : (term6 x y z) = (term5 x y z).
Proof. exact (h1). Qed.
Lemma lem1349605 (x : real) (y : real) (z : real) (h1 : (term6 x y z) = (term5 x y z)) : (term5 x y z) = (term6 x y z).
Proof. exact (SYM (@lem1349604 x y z h1)). Qed.
Lemma lem1349606 (x : real) (y : real) (z : real) : ((term5 x y z) = (term6 x y z)) = ((term6 x y z) = (term5 x y z)).
Proof. exact (prop_ext (fun h1 : (term5 x y z) = (term6 x y z) => @lem1349603 x y z h1) (fun h1 : (term6 x y z) = (term5 x y z) => @lem1349605 x y z h1)). Qed.
Lemma lem1349607 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (fun_ext (fun z : real => @lem1349606 x y z)). Qed.
Lemma lem1349608 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349609 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem1349608) (@lem1349607 x y)). Qed.
Lemma lem1349610 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1349609 x y)). Qed.
Lemma lem1349611 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349612 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem1349611) (@lem1349610 x)). Qed.
Lemma lem1349613 : term15 = term16.
Proof. exact (fun_ext (fun x : real => @lem1349612 x)). Qed.
Lemma lem1349614 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349615 : term17 = term18.
Proof. exact (MK_COMB (@lem1349614) (@lem1349613)). Qed.
Lemma lem1349616 : term18.
Proof. exact (EQ_MP (@lem1349615) (@lem1338438)). Qed.
Lemma lem1349617 (x : real) : term19 x.
Proof. exact (@lem1338588 x). Qed.
Lemma lem1349618 (x : real) : (term19 x) = ((term20 x) = term21).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1349620 (x : real) : term22 x.
Proof. exact (@lem1349616 x). Qed.
Lemma lem1349621 (x : real) : (term22 x) = (term14 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1349622 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1349621 x) (@lem1349620 x)). Qed.
Lemma lem1349623 (x : real) (y : real) : term23 x y.
Proof. exact (@lem1349622 x y). Qed.
Lemma lem1349624 (x : real) (y : real) : (term23 x y) = (term10 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1349625 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem1349624 x y) (@lem1349623 x y)). Qed.
Lemma lem1349626 (x : real) (y : real) (z : real) : term24 x y z.
Proof. exact (@lem1349625 x y z). Qed.
Lemma lem1349627 (x : real) (y : real) (z : real) : (term24 x y z) = ((term6 x y z) = (term5 x y z)).
Proof. exact (eq_refl (term24 x y z)). Qed.
Lemma lem1349629 (x : real) : term25 x.
Proof. exact (@lem1340977 x). Qed.
Lemma lem1349630 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1349631 (x : real) : term26 x.
Proof. exact (EQ_MP (@lem1349630 x) (@lem1349629 x)). Qed.
Lemma lem1349632 (x : real) (y : real) : term27 x y.
Proof. exact (@lem1349631 x y). Qed.
Lemma lem1349633 (x : real) (y : real) : (term27 x y) = ((real_sub x y) = (term28 x y)).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1349638 (x : real) (y : real) : (real_sub x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1349633 x y) (@lem1349632 x y)). Qed.
Lemma lem1349639 (y : real) (x : real) : (real_sub y x) = (term28 y x).
Proof. exact (@lem1349638 y x). Qed.
Lemma lem1349640 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1349641 (y : real) (x : real) : (term29 y x) = (term30 y x).
Proof. exact (MK_COMB (@lem1349640) (@lem1349639 y x)). Qed.
Lemma lem1349642 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1349643 (y : real) (x : real) : (term31 y x) = (term32 y x).
Proof. exact (MK_COMB (@lem1349641 y x) (@lem1349642 x)). Qed.
Lemma lem1349645 (x : real) (y : real) (z : real) : (term6 x y z) = (term5 x y z).
Proof. exact (EQ_MP (@lem1349627 x y z) (@lem1349626 x y z)). Qed.
Lemma lem1349646 (y : real) (x : real) : (term32 y x) = (term33 y x).
Proof. exact (@lem1349645 y (real_neg x) x). Qed.
Lemma lem1349648 (x : real) : (term20 x) = term21.
Proof. exact (EQ_MP (@lem1349618 x) (@lem1349617 x)). Qed.
Lemma lem1349649 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1349650 (x : real) (y : real) : (term33 y x) = (term34 y).
Proof. exact (MK_COMB (@lem1349649 y) (@lem1349648 x)). Qed.
Lemma lem1349651 (x : real) (y : real) : (term32 y x) = (term34 y).
Proof. exact (TRANS (@lem1349646 y x) (@lem1349650 x y)). Qed.
Lemma lem1349652 (x : real) (y : real) : (term31 y x) = (term34 y).
Proof. exact (TRANS (@lem1349643 y x) (@lem1349651 x y)). Qed.
Lemma lem1349653 (y : real) : (@eq real y) = (@eq real y).
Proof. exact (eq_refl (@eq real y)). Qed.
Lemma lem1349654 (x : real) (y : real) : (y = (term31 y x)) = (y = (term34 y)).
Proof. exact (MK_COMB (@lem1349653 y) (@lem1349652 x y)). Qed.
Lemma lem1349657 (y : real) (x : real) : (y = (term34 y)) = (y = (term31 y x)).
Proof. exact (SYM (@lem1349654 x y)). Qed.
Lemma lem1349661 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349597 y x) (@lem1349596 x y)). Qed.
Lemma lem1349662 (y : real) : (term34 y) = (term1 y).
Proof. exact (@lem1349661 term21 y). Qed.
Lemma lem1349663 (y : real) : (@eq real y) = (@eq real y).
Proof. exact (eq_refl (@eq real y)). Qed.
Lemma lem1349664 (y : real) : (y = (term34 y)) = (y = (term1 y)).
Proof. exact (MK_COMB (@lem1349663 y) (@lem1349662 y)). Qed.
Lemma lem1349665 (y : real) : (y = (term1 y)) = (y = (term34 y)).
Proof. exact (SYM (@lem1349664 y)). Qed.
Lemma lem1349669 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1349591 x) (@lem1349590 x)). Qed.
Lemma lem1349670 (y : real) : (term1 y) = y.
Proof. exact (@lem1349669 y). Qed.
Lemma lem1349671 (y : real) : (@eq real y) = (@eq real y).
Proof. exact (eq_refl (@eq real y)). Qed.
Lemma lem1349672 (y : real) : (y = (term1 y)) = (y = y).
Proof. exact (MK_COMB (@lem1349671 y) (@lem1349670 y)). Qed.
Lemma lem1349674 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1349675 (x : real) : (x = x) = True.
Proof. exact (@lem1349674 real x). Qed.
Lemma lem1349676 (y : real) : (y = y) = True.
Proof. exact (@lem1349675 y). Qed.
Lemma lem1349677 (y : real) : (y = (term1 y)) = True.
Proof. exact (TRANS (@lem1349672 y) (@lem1349676 y)). Qed.
Lemma lem1349678 (y : real) : True = (y = (term1 y)).
Proof. exact (SYM (@lem1349677 y)). Qed.
Lemma lem1349679 (y : real) : y = (term1 y).
Proof. exact (EQ_MP (@lem1349678 y) (@lem0)). Qed.
Lemma lem1349680 (y : real) : y = (term34 y).
Proof. exact (EQ_MP (@lem1349665 y) (@lem1349679 y)). Qed.
Lemma lem1349682 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1349683 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1349684 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1349683 x) (@lem1349682 x)). Qed.
Lemma lem1349685 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1349684 x y). Qed.
Lemma lem1349686 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1349695 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349686 y x) (@lem1349685 x y)). Qed.
Lemma lem1349696 (x : real) : (term1 x) = (term34 x).
Proof. exact (@lem1349695 x term21). Qed.
Lemma lem1349697 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1349698 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1349697) (@lem1349696 x)). Qed.
Lemma lem1349699 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1349700 (x : real) : ((term1 x) = x) = ((term34 x) = x).
Proof. exact (MK_COMB (@lem1349698 x) (@lem1349699 x)). Qed.
Lemma lem1349701 : term37 = term38.
Proof. exact (fun_ext (fun x : real => @lem1349700 x)). Qed.
Lemma lem1349702 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349703 : term39 = term40.
Proof. exact (MK_COMB (@lem1349702) (@lem1349701)). Qed.
Lemma lem1349704 : term40.
Proof. exact (EQ_MP (@lem1349703) (@lem1338512)). Qed.
Lemma lem1349705 (x : real) : term41 x.
Proof. exact (@lem1349704 x). Qed.
Lemma lem1349706 (x : real) : (term41 x) = ((term34 x) = x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1349711 (x : real) (y : real) (z : real) (h1 : (term5 x y z) = (term6 x y z)) : (term5 x y z) = (term6 x y z).
Proof. exact (h1). Qed.
Lemma lem1349712 (x : real) (y : real) (z : real) (h1 : (term5 x y z) = (term6 x y z)) : (term6 x y z) = (term5 x y z).
Proof. exact (SYM (@lem1349711 x y z h1)). Qed.
Lemma lem1349713 (x : real) (y : real) (z : real) (h1 : (term6 x y z) = (term5 x y z)) : (term6 x y z) = (term5 x y z).
Proof. exact (h1). Qed.
Lemma lem1349714 (x : real) (y : real) (z : real) (h1 : (term6 x y z) = (term5 x y z)) : (term5 x y z) = (term6 x y z).
Proof. exact (SYM (@lem1349713 x y z h1)). Qed.
Lemma lem1349715 (x : real) (y : real) (z : real) : ((term5 x y z) = (term6 x y z)) = ((term6 x y z) = (term5 x y z)).
Proof. exact (prop_ext (fun h1 : (term5 x y z) = (term6 x y z) => @lem1349712 x y z h1) (fun h1 : (term6 x y z) = (term5 x y z) => @lem1349714 x y z h1)). Qed.
Lemma lem1349716 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (fun_ext (fun z : real => @lem1349715 x y z)). Qed.
Lemma lem1349717 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349718 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem1349717) (@lem1349716 x y)). Qed.
Lemma lem1349719 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1349718 x y)). Qed.
Lemma lem1349720 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349721 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem1349720) (@lem1349719 x)). Qed.
Lemma lem1349722 : term15 = term16.
Proof. exact (fun_ext (fun x : real => @lem1349721 x)). Qed.
Lemma lem1349723 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349724 : term17 = term18.
Proof. exact (MK_COMB (@lem1349723) (@lem1349722)). Qed.
Lemma lem1349725 : term18.
Proof. exact (EQ_MP (@lem1349724) (@lem1338438)). Qed.
Lemma lem1349726 (x : real) : term19 x.
Proof. exact (@lem1338588 x). Qed.
Lemma lem1349727 (x : real) : (term19 x) = ((term20 x) = term21).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1349729 (x : real) : term22 x.
Proof. exact (@lem1349725 x). Qed.
Lemma lem1349730 (x : real) : (term22 x) = (term14 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1349731 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1349730 x) (@lem1349729 x)). Qed.
Lemma lem1349732 (x : real) (y : real) : term23 x y.
Proof. exact (@lem1349731 x y). Qed.
Lemma lem1349733 (x : real) (y : real) : (term23 x y) = (term10 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1349734 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem1349733 x y) (@lem1349732 x y)). Qed.
Lemma lem1349735 (x : real) (y : real) (z : real) : term24 x y z.
Proof. exact (@lem1349734 x y z). Qed.
Lemma lem1349736 (x : real) (y : real) (z : real) : (term24 x y z) = ((term6 x y z) = (term5 x y z)).
Proof. exact (eq_refl (term24 x y z)). Qed.
Lemma lem1349738 (x : real) : term25 x.
Proof. exact (@lem1340977 x). Qed.
Lemma lem1349739 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1349740 (x : real) : term26 x.
Proof. exact (EQ_MP (@lem1349739 x) (@lem1349738 x)). Qed.
Lemma lem1349741 (x : real) (y : real) : term27 x y.
Proof. exact (@lem1349740 x y). Qed.
Lemma lem1349742 (x : real) (y : real) : (term27 x y) = ((real_sub x y) = (term28 x y)).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1349744 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1349745 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1349746 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1349745 x) (@lem1349744 x)). Qed.
Lemma lem1349747 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1349746 x y). Qed.
Lemma lem1349748 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1349750 (a : Prop) (b : Prop) (h1 : term42 a b) : term42 a b.
Proof. exact (h1). Qed.
Lemma lem1349751 (a : Prop) (b : Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem1349752 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term42 a b) : a -> b.
Proof. exact (@lem1349750 a b h2 (@lem1349751 a b h1)). Qed.
Lemma lem1349753 (a : Prop) (b : Prop) (h1 : a = b) : term43 a b.
Proof. exact (fun h0 : term42 a b => @lem1349752 a b h1 h0). Qed.
Lemma lem1349754 (a : Prop) (b : Prop) (h1 : term42 a b) : term42 a b.
Proof. exact (h1). Qed.
Lemma lem1349755 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term42 a b) : a -> b.
Proof. exact (@lem1349753 a b h1 (@lem1349754 a b h2)). Qed.
Lemma lem1349756 (a : Prop) (b : Prop) (h1 : term42 a b) : term42 a b.
Proof. exact (fun h0 : a = b => @lem1349755 a b h0 h1). Qed.
Lemma lem1349757 (a : Prop) (b : Prop) : term44 a b.
Proof. exact (fun h0 : term42 a b => @lem1349756 a b h0). Qed.
Lemma lem1349759 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1349760 (x : real) (h1 : term45) : term46 x.
Proof. exact (@lem1349759 h1 x). Qed.
Lemma lem1349761 (x : real) : (term46 x) = (term47 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1349762 (x : real) (h1 : term45) : term47 x.
Proof. exact (EQ_MP (@lem1349761 x) (@lem1349760 x h1)). Qed.
Lemma lem1349763 (x : real) (y : real) (h1 : term45) : term48 x y.
Proof. exact (@lem1349762 x h1 y). Qed.
Lemma lem1349764 (y : real) (x : real) : (term48 x y) = (term49 y x).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1349765 (y : real) (x : real) (h1 : term45) : term49 y x.
Proof. exact (EQ_MP (@lem1349764 y x) (@lem1349763 x y h1)). Qed.
Lemma lem1349766 (y : real) (x : real) (z : real) (h1 : term45) : term50 y x z.
Proof. exact (@lem1349765 y x h1 z). Qed.
Lemma lem1349767 (y : real) (x : real) (z : real) : (term50 y x z) = (term51 y x z).
Proof. exact (eq_refl (term50 y x z)). Qed.
Lemma lem1349768 (y : real) (x : real) (z : real) (h1 : term45) : term51 y x z.
Proof. exact (EQ_MP (@lem1349767 y x z) (@lem1349766 y x z h1)). Qed.
Lemma lem1349769 (y : real) (z : real) (h1 : real_le y z) : real_le y z.
Proof. exact (h1). Qed.
Lemma lem1349770 (x : real) (y : real) (z : real) (h1 : term45) (h2 : real_le y z) : term52 y x z.
Proof. exact (@lem1349768 y x z h1 (@lem1349769 y z h2)). Qed.
Lemma lem1349771 (y : real) (z : real) (h1 : term45) (h2 : real_le y z) : term53 y z.
Proof. exact (fun x : real => @lem1349770 x y z h1 h2). Qed.
Lemma lem1349772 (y : real) (z : real) (h1 : term45) : term54 y z.
Proof. exact (fun h0 : real_le y z => @lem1349771 y z h1 h0). Qed.
Lemma lem1349773 (y : real) (h1 : term45) : term55 y.
Proof. exact (fun z : real => @lem1349772 y z h1). Qed.
Lemma lem1349774 (h1 : term45) : term56.
Proof. exact (fun y : real => @lem1349773 y h1). Qed.
Lemma lem1349775 : term57.
Proof. exact (fun h0 : term45 => @lem1349774 h0). Qed.
Lemma lem1349776 : term56.
Proof. exact (@lem1349775 (@lem1339889)). Qed.
Lemma lem1349777 (y : real) : term58 y.
Proof. exact (@lem1349776 y). Qed.
Lemma lem1349778 (y : real) : (term58 y) = (term55 y).
Proof. exact (eq_refl (term58 y)). Qed.
Lemma lem1349779 (y : real) : term55 y.
Proof. exact (EQ_MP (@lem1349778 y) (@lem1349777 y)). Qed.
Lemma lem1349780 (y : real) (z : real) : term59 y z.
Proof. exact (@lem1349779 y z). Qed.
Lemma lem1349781 (y : real) (z : real) : (term59 y z) = (term54 y z).
Proof. exact (eq_refl (term59 y z)). Qed.
Lemma lem1349783 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1349784 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1349785 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1349784 x) (@lem1349783 x)). Qed.
Lemma lem1349786 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1349785 x y). Qed.
Lemma lem1349787 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1349796 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349787 y x) (@lem1349786 x y)). Qed.
Lemma lem1349797 (x : real) : (term1 x) = (term34 x).
Proof. exact (@lem1349796 x term21). Qed.
Lemma lem1349798 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1349799 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1349798) (@lem1349797 x)). Qed.
Lemma lem1349800 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1349801 (x : real) : ((term1 x) = x) = ((term34 x) = x).
Proof. exact (MK_COMB (@lem1349799 x) (@lem1349800 x)). Qed.
Lemma lem1349802 : term37 = term38.
Proof. exact (fun_ext (fun x : real => @lem1349801 x)). Qed.
Lemma lem1349803 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349804 : term39 = term40.
Proof. exact (MK_COMB (@lem1349803) (@lem1349802)). Qed.
Lemma lem1349805 : term40.
Proof. exact (EQ_MP (@lem1349804) (@lem1338512)). Qed.
Lemma lem1349806 (x : real) : term41 x.
Proof. exact (@lem1349805 x). Qed.
Lemma lem1349807 (x : real) : (term41 x) = ((term34 x) = x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1349809 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1349810 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1349811 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1349810 x) (@lem1349809 x)). Qed.
Lemma lem1349812 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1349811 x y). Qed.
Lemma lem1349813 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1349822 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349813 y x) (@lem1349812 x y)). Qed.
Lemma lem1349823 (x : real) : (term20 x) = (term60 x).
Proof. exact (@lem1349822 x (real_neg x)). Qed.
Lemma lem1349824 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1349825 (x : real) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem1349824) (@lem1349823 x)). Qed.
Lemma lem1349826 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1349827 (x : real) : ((term20 x) = term21) = ((term60 x) = term21).
Proof. exact (MK_COMB (@lem1349825 x) (@lem1349826)). Qed.
Lemma lem1349828 : term63 = term64.
Proof. exact (fun_ext (fun x : real => @lem1349827 x)). Qed.
Lemma lem1349829 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349830 : term65 = term66.
Proof. exact (MK_COMB (@lem1349829) (@lem1349828)). Qed.
Lemma lem1349831 : term66.
Proof. exact (EQ_MP (@lem1349830) (@lem1338588)). Qed.
Lemma lem1349832 (x : real) : term67 x.
Proof. exact (@lem1349831 x). Qed.
Lemma lem1349833 (x : real) : (term67 x) = ((term60 x) = term21).
Proof. exact (eq_refl (term67 x)). Qed.
Lemma lem1349838 (x : real) (y : real) (z : real) (h1 : (term5 x y z) = (term6 x y z)) : (term5 x y z) = (term6 x y z).
Proof. exact (h1). Qed.
Lemma lem1349839 (x : real) (y : real) (z : real) (h1 : (term5 x y z) = (term6 x y z)) : (term6 x y z) = (term5 x y z).
Proof. exact (SYM (@lem1349838 x y z h1)). Qed.
Lemma lem1349840 (x : real) (y : real) (z : real) (h1 : (term6 x y z) = (term5 x y z)) : (term6 x y z) = (term5 x y z).
Proof. exact (h1). Qed.
Lemma lem1349841 (x : real) (y : real) (z : real) (h1 : (term6 x y z) = (term5 x y z)) : (term5 x y z) = (term6 x y z).
Proof. exact (SYM (@lem1349840 x y z h1)). Qed.
Lemma lem1349842 (x : real) (y : real) (z : real) : ((term5 x y z) = (term6 x y z)) = ((term6 x y z) = (term5 x y z)).
Proof. exact (prop_ext (fun h1 : (term5 x y z) = (term6 x y z) => @lem1349839 x y z h1) (fun h1 : (term6 x y z) = (term5 x y z) => @lem1349841 x y z h1)). Qed.
Lemma lem1349843 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (fun_ext (fun z : real => @lem1349842 x y z)). Qed.
Lemma lem1349844 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349845 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem1349844) (@lem1349843 x y)). Qed.
Lemma lem1349846 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1349845 x y)). Qed.
Lemma lem1349847 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349848 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem1349847) (@lem1349846 x)). Qed.
Lemma lem1349849 : term15 = term16.
Proof. exact (fun_ext (fun x : real => @lem1349848 x)). Qed.
Lemma lem1349850 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349851 : term17 = term18.
Proof. exact (MK_COMB (@lem1349850) (@lem1349849)). Qed.
Lemma lem1349852 : term18.
Proof. exact (EQ_MP (@lem1349851) (@lem1338438)). Qed.
Lemma lem1349853 (x : real) : term22 x.
Proof. exact (@lem1349852 x). Qed.
Lemma lem1349854 (x : real) : (term22 x) = (term14 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1349855 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1349854 x) (@lem1349853 x)). Qed.
Lemma lem1349856 (x : real) (y : real) : term23 x y.
Proof. exact (@lem1349855 x y). Qed.
Lemma lem1349857 (x : real) (y : real) : (term23 x y) = (term10 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1349858 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem1349857 x y) (@lem1349856 x y)). Qed.
Lemma lem1349859 (x : real) (y : real) (z : real) : term24 x y z.
Proof. exact (@lem1349858 x y z). Qed.
Lemma lem1349860 (x : real) (y : real) (z : real) : (term24 x y z) = ((term6 x y z) = (term5 x y z)).
Proof. exact (eq_refl (term24 x y z)). Qed.
Lemma lem1349862 (a : Prop) (b : Prop) (h1 : term42 a b) : term42 a b.
Proof. exact (h1). Qed.
Lemma lem1349863 (a : Prop) (b : Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem1349864 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term42 a b) : a -> b.
Proof. exact (@lem1349862 a b h2 (@lem1349863 a b h1)). Qed.
Lemma lem1349865 (a : Prop) (b : Prop) (h1 : a = b) : term43 a b.
Proof. exact (fun h0 : term42 a b => @lem1349864 a b h1 h0). Qed.
Lemma lem1349866 (a : Prop) (b : Prop) (h1 : term42 a b) : term42 a b.
Proof. exact (h1). Qed.
Lemma lem1349867 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term42 a b) : a -> b.
Proof. exact (@lem1349865 a b h1 (@lem1349866 a b h2)). Qed.
Lemma lem1349868 (a : Prop) (b : Prop) (h1 : term42 a b) : term42 a b.
Proof. exact (fun h0 : a = b => @lem1349867 a b h0 h1). Qed.
Lemma lem1349869 (a : Prop) (b : Prop) : term44 a b.
Proof. exact (fun h0 : term42 a b => @lem1349868 a b h0). Qed.
Lemma lem1349871 (x : real) : term25 x.
Proof. exact (@lem1340977 x). Qed.
Lemma lem1349872 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1349873 (x : real) : term26 x.
Proof. exact (EQ_MP (@lem1349872 x) (@lem1349871 x)). Qed.
Lemma lem1349874 (x : real) (y : real) : term27 x y.
Proof. exact (@lem1349873 x y). Qed.
Lemma lem1349875 (x : real) (y : real) : (term27 x y) = ((real_sub x y) = (term28 x y)).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1349877 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1349878 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1349879 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1349878 x) (@lem1349877 x)). Qed.
Lemma lem1349880 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1349879 x y). Qed.
Lemma lem1349881 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1349883 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1349884 (x : real) (h1 : term45) : term46 x.
Proof. exact (@lem1349883 h1 x). Qed.
Lemma lem1349885 (x : real) : (term46 x) = (term47 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1349886 (x : real) (h1 : term45) : term47 x.
Proof. exact (EQ_MP (@lem1349885 x) (@lem1349884 x h1)). Qed.
Lemma lem1349887 (x : real) (y : real) (h1 : term45) : term48 x y.
Proof. exact (@lem1349886 x h1 y). Qed.
Lemma lem1349888 (y : real) (x : real) : (term48 x y) = (term49 y x).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1349889 (y : real) (x : real) (h1 : term45) : term49 y x.
Proof. exact (EQ_MP (@lem1349888 y x) (@lem1349887 x y h1)). Qed.
Lemma lem1349890 (y : real) (x : real) (z : real) (h1 : term45) : term50 y x z.
Proof. exact (@lem1349889 y x h1 z). Qed.
Lemma lem1349891 (y : real) (x : real) (z : real) : (term50 y x z) = (term51 y x z).
Proof. exact (eq_refl (term50 y x z)). Qed.
Lemma lem1349892 (y : real) (x : real) (z : real) (h1 : term45) : term51 y x z.
Proof. exact (EQ_MP (@lem1349891 y x z) (@lem1349890 y x z h1)). Qed.
Lemma lem1349893 (y : real) (z : real) (h1 : real_le y z) : real_le y z.
Proof. exact (h1). Qed.
Lemma lem1349894 (x : real) (y : real) (z : real) (h1 : term45) (h2 : real_le y z) : term52 y x z.
Proof. exact (@lem1349892 y x z h1 (@lem1349893 y z h2)). Qed.
Lemma lem1349895 (y : real) (z : real) (h1 : term45) (h2 : real_le y z) : term53 y z.
Proof. exact (fun x : real => @lem1349894 x y z h1 h2). Qed.
Lemma lem1349896 (y : real) (z : real) (h1 : term45) : term54 y z.
Proof. exact (fun h0 : real_le y z => @lem1349895 y z h1 h0). Qed.
Lemma lem1349897 (y : real) (h1 : term45) : term55 y.
Proof. exact (fun z : real => @lem1349896 y z h1). Qed.
Lemma lem1349898 (h1 : term45) : term56.
Proof. exact (fun y : real => @lem1349897 y h1). Qed.
Lemma lem1349899 : term57.
Proof. exact (fun h0 : term45 => @lem1349898 h0). Qed.
Lemma lem1349900 : term56.
Proof. exact (@lem1349899 (@lem1339889)). Qed.
Lemma lem1349901 (y : real) : term58 y.
Proof. exact (@lem1349900 y). Qed.
Lemma lem1349902 (y : real) : (term58 y) = (term55 y).
Proof. exact (eq_refl (term58 y)). Qed.
Lemma lem1349903 (y : real) : term55 y.
Proof. exact (EQ_MP (@lem1349902 y) (@lem1349901 y)). Qed.
Lemma lem1349904 (y : real) (z : real) : term59 y z.
Proof. exact (@lem1349903 y z). Qed.
Lemma lem1349905 (y : real) (z : real) : (term59 y z) = (term54 y z).
Proof. exact (eq_refl (term59 y z)). Qed.
Lemma lem1349907 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1349908 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1349909 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1349908 x) (@lem1349907 x)). Qed.
Lemma lem1349910 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1349909 x y). Qed.
Lemma lem1349911 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1349913 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1349914 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1349915 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1349914 x) (@lem1349913 x)). Qed.
Lemma lem1349916 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1349915 x y). Qed.
Lemma lem1349917 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1349926 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349917 y x) (@lem1349916 x y)). Qed.
Lemma lem1349927 (x : real) : (term1 x) = (term34 x).
Proof. exact (@lem1349926 x term21). Qed.
Lemma lem1349928 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1349929 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1349928) (@lem1349927 x)). Qed.
Lemma lem1349930 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1349931 (x : real) : ((term1 x) = x) = ((term34 x) = x).
Proof. exact (MK_COMB (@lem1349929 x) (@lem1349930 x)). Qed.
Lemma lem1349932 : term37 = term38.
Proof. exact (fun_ext (fun x : real => @lem1349931 x)). Qed.
Lemma lem1349933 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349934 : term39 = term40.
Proof. exact (MK_COMB (@lem1349933) (@lem1349932)). Qed.
Lemma lem1349935 : term40.
Proof. exact (EQ_MP (@lem1349934) (@lem1338512)). Qed.
Lemma lem1349936 (x : real) : term41 x.
Proof. exact (@lem1349935 x). Qed.
Lemma lem1349937 (x : real) : (term41 x) = ((term34 x) = x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1349942 (x : real) (y : real) (z : real) (h1 : (term5 x y z) = (term6 x y z)) : (term5 x y z) = (term6 x y z).
Proof. exact (h1). Qed.
Lemma lem1349943 (x : real) (y : real) (z : real) (h1 : (term5 x y z) = (term6 x y z)) : (term6 x y z) = (term5 x y z).
Proof. exact (SYM (@lem1349942 x y z h1)). Qed.
Lemma lem1349944 (x : real) (y : real) (z : real) (h1 : (term6 x y z) = (term5 x y z)) : (term6 x y z) = (term5 x y z).
Proof. exact (h1). Qed.
Lemma lem1349945 (x : real) (y : real) (z : real) (h1 : (term6 x y z) = (term5 x y z)) : (term5 x y z) = (term6 x y z).
Proof. exact (SYM (@lem1349944 x y z h1)). Qed.
Lemma lem1349946 (x : real) (y : real) (z : real) : ((term5 x y z) = (term6 x y z)) = ((term6 x y z) = (term5 x y z)).
Proof. exact (prop_ext (fun h1 : (term5 x y z) = (term6 x y z) => @lem1349943 x y z h1) (fun h1 : (term6 x y z) = (term5 x y z) => @lem1349945 x y z h1)). Qed.
Lemma lem1349947 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (fun_ext (fun z : real => @lem1349946 x y z)). Qed.
Lemma lem1349948 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349949 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem1349948) (@lem1349947 x y)). Qed.
Lemma lem1349950 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1349949 x y)). Qed.
Lemma lem1349951 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349952 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem1349951) (@lem1349950 x)). Qed.
Lemma lem1349953 : term15 = term16.
Proof. exact (fun_ext (fun x : real => @lem1349952 x)). Qed.
Lemma lem1349954 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1349955 : term17 = term18.
Proof. exact (MK_COMB (@lem1349954) (@lem1349953)). Qed.
Lemma lem1349956 : term18.
Proof. exact (EQ_MP (@lem1349955) (@lem1338438)). Qed.
Lemma lem1349957 (x : real) : term19 x.
Proof. exact (@lem1338588 x). Qed.
Lemma lem1349958 (x : real) : (term19 x) = ((term20 x) = term21).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1349960 (x : real) : term22 x.
Proof. exact (@lem1349956 x). Qed.
Lemma lem1349961 (x : real) : (term22 x) = (term14 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1349962 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1349961 x) (@lem1349960 x)). Qed.
Lemma lem1349963 (x : real) (y : real) : term23 x y.
Proof. exact (@lem1349962 x y). Qed.
Lemma lem1349964 (x : real) (y : real) : (term23 x y) = (term10 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1349965 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem1349964 x y) (@lem1349963 x y)). Qed.
Lemma lem1349966 (x : real) (y : real) (z : real) : term24 x y z.
Proof. exact (@lem1349965 x y z). Qed.
Lemma lem1349967 (x : real) (y : real) (z : real) : (term24 x y z) = ((term6 x y z) = (term5 x y z)).
Proof. exact (eq_refl (term24 x y z)). Qed.
Lemma lem1349969 (x : real) : term25 x.
Proof. exact (@lem1340977 x). Qed.
Lemma lem1349970 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1349971 (x : real) : term26 x.
Proof. exact (EQ_MP (@lem1349970 x) (@lem1349969 x)). Qed.
Lemma lem1349972 (x : real) (y : real) : term27 x y.
Proof. exact (@lem1349971 x y). Qed.
Lemma lem1349973 (x : real) (y : real) : (term27 x y) = ((real_sub x y) = (term28 x y)).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1349975 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1349976 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1349977 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1349976 x) (@lem1349975 x)). Qed.
Lemma lem1349978 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1349977 x y). Qed.
Lemma lem1349979 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1349981 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1349982 (x : real) (h1 : term45) : term46 x.
Proof. exact (@lem1349981 h1 x). Qed.
Lemma lem1349983 (x : real) : (term46 x) = (term47 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1349984 (x : real) (h1 : term45) : term47 x.
Proof. exact (EQ_MP (@lem1349983 x) (@lem1349982 x h1)). Qed.
Lemma lem1349985 (x : real) (y : real) (h1 : term45) : term48 x y.
Proof. exact (@lem1349984 x h1 y). Qed.
Lemma lem1349986 (y : real) (x : real) : (term48 x y) = (term49 y x).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1349987 (y : real) (x : real) (h1 : term45) : term49 y x.
Proof. exact (EQ_MP (@lem1349986 y x) (@lem1349985 x y h1)). Qed.
Lemma lem1349988 (y : real) (x : real) (z : real) (h1 : term45) : term50 y x z.
Proof. exact (@lem1349987 y x h1 z). Qed.
Lemma lem1349989 (y : real) (x : real) (z : real) : (term50 y x z) = (term51 y x z).
Proof. exact (eq_refl (term50 y x z)). Qed.
Lemma lem1349990 (y : real) (x : real) (z : real) (h1 : term45) : term51 y x z.
Proof. exact (EQ_MP (@lem1349989 y x z) (@lem1349988 y x z h1)). Qed.
Lemma lem1349991 (y : real) (z : real) (h1 : real_le y z) : real_le y z.
Proof. exact (h1). Qed.
Lemma lem1349992 (x : real) (y : real) (z : real) (h1 : term45) (h2 : real_le y z) : term52 y x z.
Proof. exact (@lem1349990 y x z h1 (@lem1349991 y z h2)). Qed.
Lemma lem1349993 (y : real) (z : real) (h1 : term45) (h2 : real_le y z) : term53 y z.
Proof. exact (fun x : real => @lem1349992 x y z h1 h2). Qed.
Lemma lem1349994 (y : real) (z : real) (h1 : term45) : term54 y z.
Proof. exact (fun h0 : real_le y z => @lem1349993 y z h1 h0). Qed.
Lemma lem1349995 (y : real) (h1 : term45) : term55 y.
Proof. exact (fun z : real => @lem1349994 y z h1). Qed.
Lemma lem1349996 (h1 : term45) : term56.
Proof. exact (fun y : real => @lem1349995 y h1). Qed.
Lemma lem1349997 : term57.
Proof. exact (fun h0 : term45 => @lem1349996 h0). Qed.
Lemma lem1349998 : term56.
Proof. exact (@lem1349997 (@lem1339889)). Qed.
Lemma lem1349999 (y : real) : term58 y.
Proof. exact (@lem1349998 y). Qed.
Lemma lem1350000 (y : real) : (term58 y) = (term55 y).
Proof. exact (eq_refl (term58 y)). Qed.
Lemma lem1350001 (y : real) : term55 y.
Proof. exact (EQ_MP (@lem1350000 y) (@lem1349999 y)). Qed.
Lemma lem1350002 (y : real) (z : real) : term59 y z.
Proof. exact (@lem1350001 y z). Qed.
Lemma lem1350003 (y : real) (z : real) : (term59 y z) = (term54 y z).
Proof. exact (eq_refl (term59 y z)). Qed.
Lemma lem1350017 (b : Prop) : term68 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem1350018 (b : Prop) : (term68 b) = (term69 b).
Proof. exact (eq_refl (term68 b)). Qed.
Lemma lem1350019 (b : Prop) : term69 b.
Proof. exact (EQ_MP (@lem1350018 b) (@lem1350017 b)). Qed.
Lemma lem1350020 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem1350021 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem1350034 (a : Prop) (c : Prop) : (term70 a c) = (term70 a c).
Proof. exact (eq_refl (term70 a c)). Qed.
Lemma lem1350035 (a : Prop) (c : Prop) (b : Prop) (h1 : b = True) : (term71 a c b) = (term72 a c).
Proof. exact (MK_COMB (@lem1350034 a c) (@lem1350020 b h1)). Qed.
Lemma lem1350036 (a : Prop) (c : Prop) : (term72 a c) = (term73 a c).
Proof. exact (eq_refl (term72 a c)). Qed.
Lemma lem1350037 (a : Prop) (c : Prop) (b : Prop) : (term74 a c b) = (term74 a c b).
Proof. exact (eq_refl (term74 a c b)). Qed.
Lemma lem1350038 (b : Prop) (a : Prop) (c : Prop) : ((term71 a c b) = (term72 a c)) = ((term71 a c b) = (term73 a c)).
Proof. exact (MK_COMB (@lem1350037 a c b) (@lem1350036 a c)). Qed.
Lemma lem1350039 (a : Prop) (b : Prop) (c : Prop) : (term71 a c b) = (term75 a b c).
Proof. exact (eq_refl (term71 a c b)). Qed.
Lemma lem1350040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1350041 (a : Prop) (b : Prop) (c : Prop) : (term74 a c b) = (term76 a b c).
Proof. exact (MK_COMB (@lem1350040) (@lem1350039 a b c)). Qed.
Lemma lem1350042 (a : Prop) (c : Prop) : (term73 a c) = (term73 a c).
Proof. exact (eq_refl (term73 a c)). Qed.
Lemma lem1350043 (b : Prop) (a : Prop) (c : Prop) : ((term71 a c b) = (term73 a c)) = ((term75 a b c) = (term73 a c)).
Proof. exact (MK_COMB (@lem1350041 a b c) (@lem1350042 a c)). Qed.
Lemma lem1350044 (b : Prop) (a : Prop) (c : Prop) : ((term71 a c b) = (term72 a c)) = ((term75 a b c) = (term73 a c)).
Proof. exact (TRANS (@lem1350038 b a c) (@lem1350043 b a c)). Qed.
Lemma lem1350045 (a : Prop) (c : Prop) (b : Prop) (h1 : b = True) : (term75 a b c) = (term73 a c).
Proof. exact (EQ_MP (@lem1350044 b a c) (@lem1350035 a c b h1)). Qed.
Lemma lem1350046 (a : Prop) (c : Prop) (b : Prop) (h1 : b = True) : (term73 a c) = (term75 a b c).
Proof. exact (SYM (@lem1350045 a c b h1)). Qed.
Lemma lem1350047 (a : Prop) (c : Prop) : (term70 a c) = (term70 a c).
Proof. exact (eq_refl (term70 a c)). Qed.
Lemma lem1350048 (a : Prop) (c : Prop) (b : Prop) (h1 : b = False) : (term71 a c b) = (term77 a c).
Proof. exact (MK_COMB (@lem1350047 a c) (@lem1350021 b h1)). Qed.
Lemma lem1350049 (a : Prop) (c : Prop) : (term77 a c) = (term78 a c).
Proof. exact (eq_refl (term77 a c)). Qed.
Lemma lem1350050 (a : Prop) (c : Prop) (b : Prop) : (term74 a c b) = (term74 a c b).
Proof. exact (eq_refl (term74 a c b)). Qed.
Lemma lem1350051 (b : Prop) (a : Prop) (c : Prop) : ((term71 a c b) = (term77 a c)) = ((term71 a c b) = (term78 a c)).
Proof. exact (MK_COMB (@lem1350050 a c b) (@lem1350049 a c)). Qed.
Lemma lem1350052 (a : Prop) (b : Prop) (c : Prop) : (term71 a c b) = (term75 a b c).
Proof. exact (eq_refl (term71 a c b)). Qed.
Lemma lem1350053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1350054 (a : Prop) (b : Prop) (c : Prop) : (term74 a c b) = (term76 a b c).
Proof. exact (MK_COMB (@lem1350053) (@lem1350052 a b c)). Qed.
Lemma lem1350055 (a : Prop) (c : Prop) : (term78 a c) = (term78 a c).
Proof. exact (eq_refl (term78 a c)). Qed.
Lemma lem1350056 (b : Prop) (a : Prop) (c : Prop) : ((term71 a c b) = (term78 a c)) = ((term75 a b c) = (term78 a c)).
Proof. exact (MK_COMB (@lem1350054 a b c) (@lem1350055 a c)). Qed.
Lemma lem1350057 (b : Prop) (a : Prop) (c : Prop) : ((term71 a c b) = (term77 a c)) = ((term75 a b c) = (term78 a c)).
Proof. exact (TRANS (@lem1350051 b a c) (@lem1350056 b a c)). Qed.
Lemma lem1350058 (a : Prop) (c : Prop) (b : Prop) (h1 : b = False) : (term75 a b c) = (term78 a c).
Proof. exact (EQ_MP (@lem1350057 b a c) (@lem1350048 a c b h1)). Qed.
Lemma lem1350059 (a : Prop) (c : Prop) (b : Prop) (h1 : b = False) : (term78 a c) = (term75 a b c).
Proof. exact (SYM (@lem1350058 a c b h1)). Qed.
Lemma lem1350063 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1350064 (c : Prop) : (True -> c) = c.
Proof. exact (@lem1350063 c). Qed.
Lemma lem1350065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350066 (c : Prop) : (term79 c) = (imp c).
Proof. exact (MK_COMB (@lem1350065) (@lem1350064 c)). Qed.
Lemma lem1350072 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1350073 (a : Prop) : (a -> True) = True.
Proof. exact (@lem1350072 a). Qed.
Lemma lem1350074 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350075 (a : Prop) : (term80 a) = (imp True).
Proof. exact (MK_COMB (@lem1350074) (@lem1350073 a)). Qed.
Lemma lem1350076 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem1350077 (a : Prop) (c : Prop) : (term81 a c) = (True -> c).
Proof. exact (MK_COMB (@lem1350075 a) (@lem1350076 c)). Qed.
Lemma lem1350079 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1350080 (c : Prop) : (True -> c) = c.
Proof. exact (@lem1350079 c). Qed.
Lemma lem1350081 (a : Prop) (c : Prop) : (term81 a c) = c.
Proof. exact (TRANS (@lem1350077 a c) (@lem1350080 c)). Qed.
Lemma lem1350082 (a : Prop) : (imp a) = (imp a).
Proof. exact (eq_refl (imp a)). Qed.
Lemma lem1350083 (a : Prop) (c : Prop) : (term82 a c) = (a -> c).
Proof. exact (MK_COMB (@lem1350082 a) (@lem1350081 a c)). Qed.
Lemma lem1350086 (a : Prop) (c : Prop) : (term73 a c) = (term83 a c).
Proof. exact (MK_COMB (@lem1350066 c) (@lem1350083 a c)). Qed.
Lemma lem1350089 (a : Prop) (c : Prop) : (term83 a c) = (term73 a c).
Proof. exact (SYM (@lem1350086 a c)). Qed.
Lemma lem1350090 (c : Prop) : term68 c.
Proof. exact (@lem9851 c). Qed.
Lemma lem1350091 (c : Prop) : (term68 c) = (term69 c).
Proof. exact (eq_refl (term68 c)). Qed.
Lemma lem1350092 (c : Prop) : term69 c.
Proof. exact (EQ_MP (@lem1350091 c) (@lem1350090 c)). Qed.
Lemma lem1350093 (c : Prop) (h1 : c = True) : c = True.
Proof. exact (h1). Qed.
Lemma lem1350094 (c : Prop) (h1 : c = False) : c = False.
Proof. exact (h1). Qed.
Lemma lem1350101 (a : Prop) : (term84 a) = (term84 a).
Proof. exact (eq_refl (term84 a)). Qed.
Lemma lem1350102 (a : Prop) (c : Prop) (h1 : c = True) : (term85 a c) = (term86 a).
Proof. exact (MK_COMB (@lem1350101 a) (@lem1350093 c h1)). Qed.
Lemma lem1350103 (a : Prop) : (term86 a) = (term87 a).
Proof. exact (eq_refl (term86 a)). Qed.
Lemma lem1350104 (a : Prop) (c : Prop) : (term88 a c) = (term88 a c).
Proof. exact (eq_refl (term88 a c)). Qed.
Lemma lem1350105 (c : Prop) (a : Prop) : ((term85 a c) = (term86 a)) = ((term85 a c) = (term87 a)).
Proof. exact (MK_COMB (@lem1350104 a c) (@lem1350103 a)). Qed.
Lemma lem1350106 (a : Prop) (c : Prop) : (term85 a c) = (term83 a c).
Proof. exact (eq_refl (term85 a c)). Qed.
Lemma lem1350107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1350108 (a : Prop) (c : Prop) : (term88 a c) = (term89 a c).
Proof. exact (MK_COMB (@lem1350107) (@lem1350106 a c)). Qed.
Lemma lem1350109 (a : Prop) : (term87 a) = (term87 a).
Proof. exact (eq_refl (term87 a)). Qed.
Lemma lem1350110 (c : Prop) (a : Prop) : ((term85 a c) = (term87 a)) = ((term83 a c) = (term87 a)).
Proof. exact (MK_COMB (@lem1350108 a c) (@lem1350109 a)). Qed.
Lemma lem1350111 (c : Prop) (a : Prop) : ((term85 a c) = (term86 a)) = ((term83 a c) = (term87 a)).
Proof. exact (TRANS (@lem1350105 c a) (@lem1350110 c a)). Qed.
Lemma lem1350112 (a : Prop) (c : Prop) (h1 : c = True) : (term83 a c) = (term87 a).
Proof. exact (EQ_MP (@lem1350111 c a) (@lem1350102 a c h1)). Qed.
Lemma lem1350113 (a : Prop) (c : Prop) (h1 : c = True) : (term87 a) = (term83 a c).
Proof. exact (SYM (@lem1350112 a c h1)). Qed.
Lemma lem1350114 (a : Prop) : (term84 a) = (term84 a).
Proof. exact (eq_refl (term84 a)). Qed.
Lemma lem1350115 (a : Prop) (c : Prop) (h1 : c = False) : (term85 a c) = (term90 a).
Proof. exact (MK_COMB (@lem1350114 a) (@lem1350094 c h1)). Qed.
Lemma lem1350116 (a : Prop) : (term90 a) = (term91 a).
Proof. exact (eq_refl (term90 a)). Qed.
Lemma lem1350117 (a : Prop) (c : Prop) : (term88 a c) = (term88 a c).
Proof. exact (eq_refl (term88 a c)). Qed.
Lemma lem1350118 (c : Prop) (a : Prop) : ((term85 a c) = (term90 a)) = ((term85 a c) = (term91 a)).
Proof. exact (MK_COMB (@lem1350117 a c) (@lem1350116 a)). Qed.
Lemma lem1350119 (a : Prop) (c : Prop) : (term85 a c) = (term83 a c).
Proof. exact (eq_refl (term85 a c)). Qed.
Lemma lem1350120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1350121 (a : Prop) (c : Prop) : (term88 a c) = (term89 a c).
Proof. exact (MK_COMB (@lem1350120) (@lem1350119 a c)). Qed.
Lemma lem1350122 (a : Prop) : (term91 a) = (term91 a).
Proof. exact (eq_refl (term91 a)). Qed.
Lemma lem1350123 (c : Prop) (a : Prop) : ((term85 a c) = (term91 a)) = ((term83 a c) = (term91 a)).
Proof. exact (MK_COMB (@lem1350121 a c) (@lem1350122 a)). Qed.
Lemma lem1350124 (c : Prop) (a : Prop) : ((term85 a c) = (term90 a)) = ((term83 a c) = (term91 a)).
Proof. exact (TRANS (@lem1350118 c a) (@lem1350123 c a)). Qed.
Lemma lem1350125 (a : Prop) (c : Prop) (h1 : c = False) : (term83 a c) = (term91 a).
Proof. exact (EQ_MP (@lem1350124 c a) (@lem1350115 a c h1)). Qed.
Lemma lem1350126 (a : Prop) (c : Prop) (h1 : c = False) : (term91 a) = (term83 a c).
Proof. exact (SYM (@lem1350125 a c h1)). Qed.
Lemma lem1350128 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1350129 (a : Prop) : (term87 a) = (a -> True).
Proof. exact (@lem1350128 (a -> True)). Qed.
Lemma lem1350131 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1350132 (a : Prop) : (a -> True) = True.
Proof. exact (@lem1350131 a). Qed.
Lemma lem1350133 (a : Prop) : (term87 a) = True.
Proof. exact (TRANS (@lem1350129 a) (@lem1350132 a)). Qed.
Lemma lem1350134 (a : Prop) : True = (term87 a).
Proof. exact (SYM (@lem1350133 a)). Qed.
Lemma lem1350135 (a : Prop) : term87 a.
Proof. exact (EQ_MP (@lem1350134 a) (@lem0)). Qed.
Lemma lem1350137 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1350138 (a : Prop) : (term91 a) = True.
Proof. exact (@lem1350137 (a -> False)). Qed.
Lemma lem1350139 (a : Prop) : True = (term91 a).
Proof. exact (SYM (@lem1350138 a)). Qed.
Lemma lem1350140 (a : Prop) : term91 a.
Proof. exact (EQ_MP (@lem1350139 a) (@lem0)). Qed.
Lemma lem1350141 (a : Prop) (c : Prop) (h1 : c = False) : term83 a c.
Proof. exact (EQ_MP (@lem1350126 a c h1) (@lem1350140 a)). Qed.
Lemma lem1350142 (a : Prop) (c : Prop) (h1 : c = True) : term83 a c.
Proof. exact (EQ_MP (@lem1350113 a c h1) (@lem1350135 a)). Qed.
Lemma lem1350144 (a : Prop) (c : Prop) : term83 a c.
Proof. exact (or_elim (@lem1350092 c) (fun h0 : c = True => @lem1350142 a c h0) (fun h0 : c = False => @lem1350141 a c h0)). Qed.
Lemma lem1350145 (a : Prop) (c : Prop) : term73 a c.
Proof. exact (EQ_MP (@lem1350089 a c) (@lem1350144 a c)). Qed.
Lemma lem1350149 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1350150 (c : Prop) : (False -> c) = True.
Proof. exact (@lem1350149 c). Qed.
Lemma lem1350151 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350152 (c : Prop) : (term92 c) = (imp True).
Proof. exact (MK_COMB (@lem1350151) (@lem1350150 c)). Qed.
Lemma lem1350158 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1350159 (a : Prop) : (a -> False) = (~ a).
Proof. exact (@lem1350158 a). Qed.
Lemma lem1350160 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350161 (a : Prop) : (term93 a) = (term94 a).
Proof. exact (MK_COMB (@lem1350160) (@lem1350159 a)). Qed.
Lemma lem1350162 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem1350163 (a : Prop) (c : Prop) : (term95 a c) = (term96 a c).
Proof. exact (MK_COMB (@lem1350161 a) (@lem1350162 c)). Qed.
Lemma lem1350166 (a : Prop) : (imp a) = (imp a).
Proof. exact (eq_refl (imp a)). Qed.
Lemma lem1350167 (a : Prop) (c : Prop) : (term97 a c) = (term98 a c).
Proof. exact (MK_COMB (@lem1350166 a) (@lem1350163 a c)). Qed.
Lemma lem1350170 (a : Prop) (c : Prop) : (term78 a c) = (term99 a c).
Proof. exact (MK_COMB (@lem1350152 c) (@lem1350167 a c)). Qed.
Lemma lem1350172 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1350173 (a : Prop) (c : Prop) : (term99 a c) = (term98 a c).
Proof. exact (@lem1350172 (term98 a c)). Qed.
Lemma lem1350178 (a : Prop) (c : Prop) : (term78 a c) = (term98 a c).
Proof. exact (TRANS (@lem1350170 a c) (@lem1350173 a c)). Qed.
Lemma lem1350179 (a : Prop) (c : Prop) : (term98 a c) = (term78 a c).
Proof. exact (SYM (@lem1350178 a c)). Qed.
Lemma lem1350180 (a : Prop) : term68 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem1350181 (a : Prop) : (term68 a) = (term69 a).
Proof. exact (eq_refl (term68 a)). Qed.
Lemma lem1350182 (a : Prop) : term69 a.
Proof. exact (EQ_MP (@lem1350181 a) (@lem1350180 a)). Qed.
Lemma lem1350183 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem1350184 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem1350191 (c : Prop) : (term100 c) = (term100 c).
Proof. exact (eq_refl (term100 c)). Qed.
Lemma lem1350192 (c : Prop) (a : Prop) (h1 : a = True) : (term101 c a) = (term102 c).
Proof. exact (MK_COMB (@lem1350191 c) (@lem1350183 a h1)). Qed.
Lemma lem1350193 (c : Prop) : (term102 c) = (term103 c).
Proof. exact (eq_refl (term102 c)). Qed.
Lemma lem1350194 (c : Prop) (a : Prop) : (term104 c a) = (term104 c a).
Proof. exact (eq_refl (term104 c a)). Qed.
Lemma lem1350195 (a : Prop) (c : Prop) : ((term101 c a) = (term102 c)) = ((term101 c a) = (term103 c)).
Proof. exact (MK_COMB (@lem1350194 c a) (@lem1350193 c)). Qed.
Lemma lem1350196 (a : Prop) (c : Prop) : (term101 c a) = (term98 a c).
Proof. exact (eq_refl (term101 c a)). Qed.
Lemma lem1350197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1350198 (a : Prop) (c : Prop) : (term104 c a) = (term105 a c).
Proof. exact (MK_COMB (@lem1350197) (@lem1350196 a c)). Qed.
Lemma lem1350199 (c : Prop) : (term103 c) = (term103 c).
Proof. exact (eq_refl (term103 c)). Qed.
Lemma lem1350200 (a : Prop) (c : Prop) : ((term101 c a) = (term103 c)) = ((term98 a c) = (term103 c)).
Proof. exact (MK_COMB (@lem1350198 a c) (@lem1350199 c)). Qed.
Lemma lem1350201 (a : Prop) (c : Prop) : ((term101 c a) = (term102 c)) = ((term98 a c) = (term103 c)).
Proof. exact (TRANS (@lem1350195 a c) (@lem1350200 a c)). Qed.
Lemma lem1350202 (c : Prop) (a : Prop) (h1 : a = True) : (term98 a c) = (term103 c).
Proof. exact (EQ_MP (@lem1350201 a c) (@lem1350192 c a h1)). Qed.
Lemma lem1350203 (c : Prop) (a : Prop) (h1 : a = True) : (term103 c) = (term98 a c).
Proof. exact (SYM (@lem1350202 c a h1)). Qed.
Lemma lem1350204 (c : Prop) : (term100 c) = (term100 c).
Proof. exact (eq_refl (term100 c)). Qed.
Lemma lem1350205 (c : Prop) (a : Prop) (h1 : a = False) : (term101 c a) = (term106 c).
Proof. exact (MK_COMB (@lem1350204 c) (@lem1350184 a h1)). Qed.
Lemma lem1350206 (c : Prop) : (term106 c) = (term107 c).
Proof. exact (eq_refl (term106 c)). Qed.
Lemma lem1350207 (c : Prop) (a : Prop) : (term104 c a) = (term104 c a).
Proof. exact (eq_refl (term104 c a)). Qed.
Lemma lem1350208 (a : Prop) (c : Prop) : ((term101 c a) = (term106 c)) = ((term101 c a) = (term107 c)).
Proof. exact (MK_COMB (@lem1350207 c a) (@lem1350206 c)). Qed.
Lemma lem1350209 (a : Prop) (c : Prop) : (term101 c a) = (term98 a c).
Proof. exact (eq_refl (term101 c a)). Qed.
Lemma lem1350210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1350211 (a : Prop) (c : Prop) : (term104 c a) = (term105 a c).
Proof. exact (MK_COMB (@lem1350210) (@lem1350209 a c)). Qed.
Lemma lem1350212 (c : Prop) : (term107 c) = (term107 c).
Proof. exact (eq_refl (term107 c)). Qed.
Lemma lem1350213 (a : Prop) (c : Prop) : ((term101 c a) = (term107 c)) = ((term98 a c) = (term107 c)).
Proof. exact (MK_COMB (@lem1350211 a c) (@lem1350212 c)). Qed.
Lemma lem1350214 (a : Prop) (c : Prop) : ((term101 c a) = (term106 c)) = ((term98 a c) = (term107 c)).
Proof. exact (TRANS (@lem1350208 a c) (@lem1350213 a c)). Qed.
Lemma lem1350215 (c : Prop) (a : Prop) (h1 : a = False) : (term98 a c) = (term107 c).
Proof. exact (EQ_MP (@lem1350214 a c) (@lem1350205 c a h1)). Qed.
Lemma lem1350216 (c : Prop) (a : Prop) (h1 : a = False) : (term107 c) = (term98 a c).
Proof. exact (SYM (@lem1350215 c a h1)). Qed.
Lemma lem1350218 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1350219 (c : Prop) : (term103 c) = (term108 c).
Proof. exact (@lem1350218 (term108 c)). Qed.
Lemma lem1350223 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1350224 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350225 : term109 = (imp False).
Proof. exact (MK_COMB (@lem1350224) (@lem1350223)). Qed.
Lemma lem1350226 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem1350227 (c : Prop) : (term108 c) = (False -> c).
Proof. exact (MK_COMB (@lem1350225) (@lem1350226 c)). Qed.
Lemma lem1350229 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1350230 (c : Prop) : (False -> c) = True.
Proof. exact (@lem1350229 c). Qed.
Lemma lem1350231 (c : Prop) : (term108 c) = True.
Proof. exact (TRANS (@lem1350227 c) (@lem1350230 c)). Qed.
Lemma lem1350232 (c : Prop) : (term103 c) = True.
Proof. exact (TRANS (@lem1350219 c) (@lem1350231 c)). Qed.
Lemma lem1350233 (c : Prop) : True = (term103 c).
Proof. exact (SYM (@lem1350232 c)). Qed.
Lemma lem1350234 (c : Prop) : term103 c.
Proof. exact (EQ_MP (@lem1350233 c) (@lem0)). Qed.
Lemma lem1350236 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1350237 (c : Prop) : (term107 c) = True.
Proof. exact (@lem1350236 (term110 c)). Qed.
Lemma lem1350238 (c : Prop) : True = (term107 c).
Proof. exact (SYM (@lem1350237 c)). Qed.
Lemma lem1350239 (c : Prop) : term107 c.
Proof. exact (EQ_MP (@lem1350238 c) (@lem0)). Qed.
Lemma lem1350240 (c : Prop) (a : Prop) (h1 : a = False) : term98 a c.
Proof. exact (EQ_MP (@lem1350216 c a h1) (@lem1350239 c)). Qed.
Lemma lem1350241 (c : Prop) (a : Prop) (h1 : a = True) : term98 a c.
Proof. exact (EQ_MP (@lem1350203 c a h1) (@lem1350234 c)). Qed.
Lemma lem1350243 (a : Prop) (c : Prop) : term98 a c.
Proof. exact (or_elim (@lem1350182 a) (fun h0 : a = True => @lem1350241 c a h0) (fun h0 : a = False => @lem1350240 c a h0)). Qed.
Lemma lem1350244 (a : Prop) (c : Prop) : term78 a c.
Proof. exact (EQ_MP (@lem1350179 a c) (@lem1350243 a c)). Qed.
Lemma lem1350245 (a : Prop) (c : Prop) (b : Prop) (h1 : b = False) : term75 a b c.
Proof. exact (EQ_MP (@lem1350059 a c b h1) (@lem1350244 a c)). Qed.
Lemma lem1350246 (a : Prop) (c : Prop) (b : Prop) (h1 : b = True) : term75 a b c.
Proof. exact (EQ_MP (@lem1350046 a c b h1) (@lem1350145 a c)). Qed.
Lemma lem1350249 (a : Prop) (b : Prop) (c : Prop) : term75 a b c.
Proof. exact (or_elim (@lem1350019 b) (fun h0 : b = True => @lem1350246 a c b h0) (fun h0 : b = False => @lem1350245 a c b h0)). Qed.
Lemma lem1350250 (a : Prop) (b : Prop) (c : Prop) (h1 : term75 a b c) : term75 a b c.
Proof. exact (h1). Qed.
Lemma lem1350251 (b : Prop) (c : Prop) (h1 : b -> c) : b -> c.
Proof. exact (h1). Qed.
Lemma lem1350252 (a : Prop) (b : Prop) (c : Prop) (h1 : b -> c) (h2 : term75 a b c) : term111 a b c.
Proof. exact (@lem1350250 a b c h2 (@lem1350251 b c h1)). Qed.
Lemma lem1350253 (a : Prop) (b : Prop) (c : Prop) (h1 : b -> c) : term112 a b c.
Proof. exact (fun h0 : term75 a b c => @lem1350252 a b c h1 h0). Qed.
Lemma lem1350254 (a : Prop) (b : Prop) (c : Prop) (h1 : term75 a b c) : term75 a b c.
Proof. exact (h1). Qed.
Lemma lem1350255 (a : Prop) (b : Prop) (c : Prop) (h1 : b -> c) (h2 : term75 a b c) : term111 a b c.
Proof. exact (@lem1350253 a b c h1 (@lem1350254 a b c h2)). Qed.
Lemma lem1350256 (a : Prop) (b : Prop) (c : Prop) (h1 : term75 a b c) : term75 a b c.
Proof. exact (fun h0 : b -> c => @lem1350255 a b c h0 h1). Qed.
Lemma lem1350257 (a : Prop) (b : Prop) (c : Prop) : term113 a b c.
Proof. exact (fun h0 : term75 a b c => @lem1350256 a b c h0). Qed.
Lemma lem1350259 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1350260 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1350261 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1350260 x) (@lem1350259 x)). Qed.
Lemma lem1350262 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1350261 x y). Qed.
Lemma lem1350263 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1350272 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1350263 y x) (@lem1350262 x y)). Qed.
Lemma lem1350273 (x : real) : (term1 x) = (term34 x).
Proof. exact (@lem1350272 x term21). Qed.
Lemma lem1350274 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1350275 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1350274) (@lem1350273 x)). Qed.
Lemma lem1350276 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1350277 (x : real) : ((term1 x) = x) = ((term34 x) = x).
Proof. exact (MK_COMB (@lem1350275 x) (@lem1350276 x)). Qed.
Lemma lem1350278 : term37 = term38.
Proof. exact (fun_ext (fun x : real => @lem1350277 x)). Qed.
Lemma lem1350279 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1350280 : term39 = term40.
Proof. exact (MK_COMB (@lem1350279) (@lem1350278)). Qed.
Lemma lem1350281 : term40.
Proof. exact (EQ_MP (@lem1350280) (@lem1338512)). Qed.
Lemma lem1350282 (x : real) : term41 x.
Proof. exact (@lem1350281 x). Qed.
Lemma lem1350283 (x : real) : (term41 x) = ((term34 x) = x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1350285 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1350286 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1350287 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1350286 x) (@lem1350285 x)). Qed.
Lemma lem1350288 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1350287 x y). Qed.
Lemma lem1350289 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1350298 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1350289 y x) (@lem1350288 x y)). Qed.
Lemma lem1350299 (x : real) : (term20 x) = (term60 x).
Proof. exact (@lem1350298 x (real_neg x)). Qed.
Lemma lem1350300 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1350301 (x : real) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem1350300) (@lem1350299 x)). Qed.
Lemma lem1350302 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1350303 (x : real) : ((term20 x) = term21) = ((term60 x) = term21).
Proof. exact (MK_COMB (@lem1350301 x) (@lem1350302)). Qed.
Lemma lem1350304 : term63 = term64.
Proof. exact (fun_ext (fun x : real => @lem1350303 x)). Qed.
Lemma lem1350305 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1350306 : term65 = term66.
Proof. exact (MK_COMB (@lem1350305) (@lem1350304)). Qed.
Lemma lem1350307 : term66.
Proof. exact (EQ_MP (@lem1350306) (@lem1338588)). Qed.
Lemma lem1350308 (x : real) : term67 x.
Proof. exact (@lem1350307 x). Qed.
Lemma lem1350309 (x : real) : (term67 x) = ((term60 x) = term21).
Proof. exact (eq_refl (term67 x)). Qed.
Lemma lem1350314 (x : real) (y : real) (z : real) (h1 : (term5 x y z) = (term6 x y z)) : (term5 x y z) = (term6 x y z).
Proof. exact (h1). Qed.
Lemma lem1350315 (x : real) (y : real) (z : real) (h1 : (term5 x y z) = (term6 x y z)) : (term6 x y z) = (term5 x y z).
Proof. exact (SYM (@lem1350314 x y z h1)). Qed.
Lemma lem1350316 (x : real) (y : real) (z : real) (h1 : (term6 x y z) = (term5 x y z)) : (term6 x y z) = (term5 x y z).
Proof. exact (h1). Qed.
Lemma lem1350317 (x : real) (y : real) (z : real) (h1 : (term6 x y z) = (term5 x y z)) : (term5 x y z) = (term6 x y z).
Proof. exact (SYM (@lem1350316 x y z h1)). Qed.
Lemma lem1350318 (x : real) (y : real) (z : real) : ((term5 x y z) = (term6 x y z)) = ((term6 x y z) = (term5 x y z)).
Proof. exact (prop_ext (fun h1 : (term5 x y z) = (term6 x y z) => @lem1350315 x y z h1) (fun h1 : (term6 x y z) = (term5 x y z) => @lem1350317 x y z h1)). Qed.
Lemma lem1350319 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (fun_ext (fun z : real => @lem1350318 x y z)). Qed.
Lemma lem1350320 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1350321 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem1350320) (@lem1350319 x y)). Qed.
Lemma lem1350322 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1350321 x y)). Qed.
Lemma lem1350323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1350324 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem1350323) (@lem1350322 x)). Qed.
Lemma lem1350325 : term15 = term16.
Proof. exact (fun_ext (fun x : real => @lem1350324 x)). Qed.
Lemma lem1350326 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1350327 : term17 = term18.
Proof. exact (MK_COMB (@lem1350326) (@lem1350325)). Qed.
Lemma lem1350328 : term18.
Proof. exact (EQ_MP (@lem1350327) (@lem1338438)). Qed.
Lemma lem1350329 (x : real) : term22 x.
Proof. exact (@lem1350328 x). Qed.
Lemma lem1350330 (x : real) : (term22 x) = (term14 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1350331 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1350330 x) (@lem1350329 x)). Qed.
Lemma lem1350332 (x : real) (y : real) : term23 x y.
Proof. exact (@lem1350331 x y). Qed.
Lemma lem1350333 (x : real) (y : real) : (term23 x y) = (term10 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1350334 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem1350333 x y) (@lem1350332 x y)). Qed.
Lemma lem1350335 (x : real) (y : real) (z : real) : term24 x y z.
Proof. exact (@lem1350334 x y z). Qed.
Lemma lem1350336 (x : real) (y : real) (z : real) : (term24 x y z) = ((term6 x y z) = (term5 x y z)).
Proof. exact (eq_refl (term24 x y z)). Qed.
Lemma lem1350338 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1350339 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1350340 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1350339 x) (@lem1350338 x)). Qed.
Lemma lem1350341 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1350340 x y). Qed.
Lemma lem1350342 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1350344 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1350345 (x : real) (h1 : term45) : term46 x.
Proof. exact (@lem1350344 h1 x). Qed.
Lemma lem1350346 (x : real) : (term46 x) = (term47 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1350347 (x : real) (h1 : term45) : term47 x.
Proof. exact (EQ_MP (@lem1350346 x) (@lem1350345 x h1)). Qed.
Lemma lem1350348 (x : real) (y : real) (h1 : term45) : term48 x y.
Proof. exact (@lem1350347 x h1 y). Qed.
Lemma lem1350349 (y : real) (x : real) : (term48 x y) = (term49 y x).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1350350 (y : real) (x : real) (h1 : term45) : term49 y x.
Proof. exact (EQ_MP (@lem1350349 y x) (@lem1350348 x y h1)). Qed.
Lemma lem1350351 (y : real) (x : real) (z : real) (h1 : term45) : term50 y x z.
Proof. exact (@lem1350350 y x h1 z). Qed.
Lemma lem1350352 (y : real) (x : real) (z : real) : (term50 y x z) = (term51 y x z).
Proof. exact (eq_refl (term50 y x z)). Qed.
Lemma lem1350353 (y : real) (x : real) (z : real) (h1 : term45) : term51 y x z.
Proof. exact (EQ_MP (@lem1350352 y x z) (@lem1350351 y x z h1)). Qed.
Lemma lem1350354 (y : real) (z : real) (h1 : real_le y z) : real_le y z.
Proof. exact (h1). Qed.
Lemma lem1350355 (x : real) (y : real) (z : real) (h1 : term45) (h2 : real_le y z) : term52 y x z.
Proof. exact (@lem1350353 y x z h1 (@lem1350354 y z h2)). Qed.
Lemma lem1350356 (y : real) (z : real) (h1 : term45) (h2 : real_le y z) : term53 y z.
Proof. exact (fun x : real => @lem1350355 x y z h1 h2). Qed.
Lemma lem1350357 (y : real) (z : real) (h1 : term45) : term54 y z.
Proof. exact (fun h0 : real_le y z => @lem1350356 y z h1 h0). Qed.
Lemma lem1350358 (y : real) (h1 : term45) : term55 y.
Proof. exact (fun z : real => @lem1350357 y z h1). Qed.
Lemma lem1350359 (h1 : term45) : term56.
Proof. exact (fun y : real => @lem1350358 y h1). Qed.
Lemma lem1350360 : term57.
Proof. exact (fun h0 : term45 => @lem1350359 h0). Qed.
Lemma lem1350361 : term56.
Proof. exact (@lem1350360 (@lem1339889)). Qed.
Lemma lem1350362 (y : real) : term58 y.
Proof. exact (@lem1350361 y). Qed.
Lemma lem1350363 (y : real) : (term58 y) = (term55 y).
Proof. exact (eq_refl (term58 y)). Qed.
Lemma lem1350364 (y : real) : term55 y.
Proof. exact (EQ_MP (@lem1350363 y) (@lem1350362 y)). Qed.
Lemma lem1350365 (y : real) (z : real) : term59 y z.
Proof. exact (@lem1350364 y z). Qed.
Lemma lem1350366 (y : real) (z : real) : (term59 y z) = (term54 y z).
Proof. exact (eq_refl (term59 y z)). Qed.
Lemma lem1350368 (P : real -> Prop) (x : real) : term114 P x.
Proof. exact (@lem1349589 (term115 P x)). Qed.
Lemma lem1350369 (P : real -> Prop) (x : real) : (term114 P x) = (term116 P x).
Proof. exact (eq_refl (term114 P x)). Qed.
Lemma lem1350370 (P : real -> Prop) (x : real) : term116 P x.
Proof. exact (EQ_MP (@lem1350369 P x) (@lem1350368 P x)). Qed.
Lemma lem1350371 (x : real) : term0 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1350372 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1350374 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1350375 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1350376 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1350375 x) (@lem1350374 x)). Qed.
Lemma lem1350377 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1350376 x y). Qed.
Lemma lem1350378 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1350380 (x : real) : term19 x.
Proof. exact (@lem1338588 x). Qed.
Lemma lem1350381 (x : real) : (term19 x) = ((term20 x) = term21).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1350383 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1350384 (x : real) (h1 : term45) : term46 x.
Proof. exact (@lem1350383 h1 x). Qed.
Lemma lem1350385 (x : real) : (term46 x) = (term47 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1350386 (x : real) (h1 : term45) : term47 x.
Proof. exact (EQ_MP (@lem1350385 x) (@lem1350384 x h1)). Qed.
Lemma lem1350387 (x : real) (y : real) (h1 : term45) : term48 x y.
Proof. exact (@lem1350386 x h1 y). Qed.
Lemma lem1350388 (y : real) (x : real) : (term48 x y) = (term49 y x).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1350389 (y : real) (x : real) (h1 : term45) : term49 y x.
Proof. exact (EQ_MP (@lem1350388 y x) (@lem1350387 x y h1)). Qed.
Lemma lem1350390 (y : real) (x : real) (z : real) (h1 : term45) : term50 y x z.
Proof. exact (@lem1350389 y x h1 z). Qed.
Lemma lem1350391 (y : real) (x : real) (z : real) : (term50 y x z) = (term51 y x z).
Proof. exact (eq_refl (term50 y x z)). Qed.
Lemma lem1350392 (y : real) (x : real) (z : real) (h1 : term45) : term51 y x z.
Proof. exact (EQ_MP (@lem1350391 y x z) (@lem1350390 y x z h1)). Qed.
Lemma lem1350393 (y : real) (z : real) (h1 : real_le y z) : real_le y z.
Proof. exact (h1). Qed.
Lemma lem1350394 (x : real) (y : real) (z : real) (h1 : term45) (h2 : real_le y z) : term52 y x z.
Proof. exact (@lem1350392 y x z h1 (@lem1350393 y z h2)). Qed.
Lemma lem1350395 (y : real) (z : real) (h1 : term45) (h2 : real_le y z) : term53 y z.
Proof. exact (fun x : real => @lem1350394 x y z h1 h2). Qed.
Lemma lem1350396 (y : real) (z : real) (h1 : term45) : term54 y z.
Proof. exact (fun h0 : real_le y z => @lem1350395 y z h1 h0). Qed.
Lemma lem1350397 (y : real) (h1 : term45) : term55 y.
Proof. exact (fun z : real => @lem1350396 y z h1). Qed.
Lemma lem1350398 (h1 : term45) : term56.
Proof. exact (fun y : real => @lem1350397 y h1). Qed.
Lemma lem1350399 : term57.
Proof. exact (fun h0 : term45 => @lem1350398 h0). Qed.
Lemma lem1350400 : term56.
Proof. exact (@lem1350399 (@lem1339889)). Qed.
Lemma lem1350401 (y : real) : term58 y.
Proof. exact (@lem1350400 y). Qed.
Lemma lem1350402 (y : real) : (term58 y) = (term55 y).
Proof. exact (eq_refl (term58 y)). Qed.
Lemma lem1350403 (y : real) : term55 y.
Proof. exact (EQ_MP (@lem1350402 y) (@lem1350401 y)). Qed.
Lemma lem1350404 (y : real) (z : real) : term59 y z.
Proof. exact (@lem1350403 y z). Qed.
Lemma lem1350405 (y : real) (z : real) : (term59 y z) = (term54 y z).
Proof. exact (eq_refl (term59 y z)). Qed.
Lemma lem1350407 (h1 : term117) : term117.
Proof. exact (h1). Qed.
Lemma lem1350408 (P : real -> Prop) (h1 : term117) : term118 P.
Proof. exact (@lem1350407 h1 P). Qed.
Lemma lem1350409 (P : real -> Prop) : (term118 P) = (term119 P).
Proof. exact (eq_refl (term118 P)). Qed.
Lemma lem1350410 (P : real -> Prop) (h1 : term117) : term119 P.
Proof. exact (EQ_MP (@lem1350409 P) (@lem1350408 P h1)). Qed.
Lemma lem1350411 (P : real -> Prop) (h1 : term120 P) : term120 P.
Proof. exact (h1). Qed.
Lemma lem1350412 (P : real -> Prop) (h1 : term117) (h2 : term120 P) : term121 P.
Proof. exact (@lem1350410 P h1 (@lem1350411 P h2)). Qed.
Lemma lem1350413 (P : real -> Prop) (h1 : term120 P) : term122 P.
Proof. exact (fun h0 : term117 => @lem1350412 P h0 h1). Qed.
Lemma lem1350414 (h1 : term117) : term117.
Proof. exact (h1). Qed.
Lemma lem1350415 (P : real -> Prop) (h1 : term117) (h2 : term120 P) : term121 P.
Proof. exact (@lem1350413 P h2 (@lem1350414 h1)). Qed.
Lemma lem1350416 (P : real -> Prop) (h1 : term117) : term119 P.
Proof. exact (fun h0 : term120 P => @lem1350415 P h1 h0). Qed.
Lemma lem1350417 (h1 : term117) : term117.
Proof. exact (fun P : real -> Prop => @lem1350416 P h1). Qed.
Lemma lem1350418 : term123.
Proof. exact (fun h0 : term117 => @lem1350417 h0). Qed.
Lemma lem1350419 : term117.
Proof. exact (@lem1350418 (@lem1349589)). Qed.
Lemma lem1350420 (P : real -> Prop) : term118 P.
Proof. exact (@lem1350419 P). Qed.
Lemma lem1350421 (P : real -> Prop) : (term118 P) = (term119 P).
Proof. exact (eq_refl (term118 P)). Qed.
Lemma lem1350423 : term124.
Proof. exact (@lem1339697 term21). Qed.
Lemma lem1350424 : term124 = term125.
Proof. exact (eq_refl term124). Qed.
Lemma lem1350425 : term125.
Proof. exact (EQ_MP (@lem1350424) (@lem1350423)). Qed.
Lemma lem1350426 (x : real) : term126 x.
Proof. exact (@lem1350425 x). Qed.
Lemma lem1350427 (x : real) : (term126 x) = (term127 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1350428 (x : real) : term127 x.
Proof. exact (EQ_MP (@lem1350427 x) (@lem1350426 x)). Qed.
Lemma lem1350429 (x : real) (h1 : term128 x) : term128 x.
Proof. exact (h1). Qed.
Lemma lem1350430 (x : real) (h1 : term129 x) : term129 x.
Proof. exact (h1). Qed.
Lemma lem1350431 (P : real -> Prop) (h1 : term130 P) : term130 P.
Proof. exact (h1). Qed.
Lemma lem1350432 (P : real -> Prop) (h1 : term131 P) : term131 P.
Proof. exact (h1). Qed.
Lemma lem1350433 (P : real -> Prop) (h1 : term132 P) : term132 P.
Proof. exact (h1). Qed.
Lemma lem1350434 (P : real -> Prop) (x : real) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1350435 (P : real -> Prop) (M : real) (h1 : term133 P M) : term133 P M.
Proof. exact (h1). Qed.
Lemma lem1350437 (P : real -> Prop) : term119 P.
Proof. exact (EQ_MP (@lem1350421 P) (@lem1350420 P)). Qed.
Lemma lem1350438 (P : real -> Prop) (x : real) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem1350445 (x : real) : (term128 x) = ((term128 x) = True).
Proof. exact (@lem7 (term128 x)). Qed.
Lemma lem1350450 (P : real -> Prop) (x : real) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem1350438 P x) (@lem1350434 P x h1)). Qed.
Lemma lem1350451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1350452 (P : real -> Prop) (x : real) (h1 : P x) : (term134 P x) = (and True).
Proof. exact (MK_COMB (@lem1350451) (@lem1350450 P x h1)). Qed.
Lemma lem1350454 (x : real) (h1 : term128 x) : (term128 x) = True.
Proof. exact (EQ_MP (@lem1350445 x) (@lem1350429 x h1)). Qed.
Lemma lem1350455 (P : real -> Prop) (x : real) (h1 : P x) (h2 : term128 x) : (term135 P x) = (True /\ True).
Proof. exact (MK_COMB (@lem1350452 P x h1) (@lem1350454 x h2)). Qed.
Lemma lem1350457 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1350458 : (True /\ True) = True.
Proof. exact (@lem1350457 True). Qed.
Lemma lem1350459 (P : real -> Prop) (x : real) (h1 : P x) (h2 : term128 x) : (term135 P x) = True.
Proof. exact (TRANS (@lem1350455 P x h1 h2) (@lem1350458)). Qed.
Lemma lem1350460 (P : real -> Prop) (x : real) (h1 : P x) (h2 : term128 x) : True = (term135 P x).
Proof. exact (SYM (@lem1350459 P x h1 h2)). Qed.
Lemma lem1350461 (P : real -> Prop) (x : real) (h1 : P x) (h2 : term128 x) : term135 P x.
Proof. exact (EQ_MP (@lem1350460 P x h1 h2) (@lem0)). Qed.
Lemma lem1350464 (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term136 P M x.
Proof. exact (@lem1350435 P M h1 x). Qed.
Lemma lem1350465 (P : real -> Prop) (x : real) (M : real) : (term136 P M x) = (term137 P x M).
Proof. exact (eq_refl (term136 P M x)). Qed.
Lemma lem1350466 (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term137 P x M.
Proof. exact (EQ_MP (@lem1350465 P x M) (@lem1350464 x P M h1)). Qed.
Lemma lem1350467 (P : real -> Prop) (x : real) (M : real) : (term137 P x M) = ((term137 P x M) = True).
Proof. exact (@lem7 (term137 P x M)). Qed.
Lemma lem1350476 (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : (term137 P x M) = True.
Proof. exact (EQ_MP (@lem1350467 P x M) (@lem1350466 x P M h1)). Qed.
Lemma lem1350477 (P : real -> Prop) (M : real) (h1 : term133 P M) : (term138 P M) = term139.
Proof. exact (fun_ext (fun x : real => @lem1350476 x P M h1)). Qed.
Lemma lem1350478 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1350479 (P : real -> Prop) (M : real) (h1 : term133 P M) : (term133 P M) = term140.
Proof. exact (MK_COMB (@lem1350478) (@lem1350477 P M h1)). Qed.
Lemma lem1350481 {A : Type'} (t : Prop) : (term141 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1350482 (t : Prop) : (term142 t) = t.
Proof. exact (@lem1350481 real t). Qed.
Lemma lem1350483 : term140 = True.
Proof. exact (@lem1350482 True). Qed.
Lemma lem1350484 (P : real -> Prop) (M : real) (h1 : term133 P M) : (term133 P M) = True.
Proof. exact (TRANS (@lem1350479 P M h1) (@lem1350483)). Qed.
Lemma lem1350485 (P : real -> Prop) (M : real) (h1 : term133 P M) : True = (term133 P M).
Proof. exact (SYM (@lem1350484 P M h1)). Qed.
Lemma lem1350486 (P : real -> Prop) (M : real) (h1 : term133 P M) : term133 P M.
Proof. exact (EQ_MP (@lem1350485 P M h1) (@lem0)). Qed.
Lemma lem1350487 (P : real -> Prop) (M : real) (h1 : term133 P M) : term131 P.
Proof. exact (ex_intro (term143 P) M (@lem1350486 P M h1)). Qed.
Lemma lem1350488 (P : real -> Prop) (x : real) (h1 : P x) (h2 : term128 x) : term144 P.
Proof. exact (ex_intro (term145 P) x (@lem1350461 P x h1 h2)). Qed.
Lemma lem1350489 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) (h3 : term128 x) : term120 P.
Proof. exact (conj (@lem1350488 P x h2 h3) (@lem1350487 P M h1)). Qed.
Lemma lem1350490 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) (h3 : term128 x) : term121 P.
Proof. exact (@lem1350437 P (@lem1350489 M P x h1 h2 h3)). Qed.
Lemma lem1350492 (y : real) (z : real) : term54 y z.
Proof. exact (EQ_MP (@lem1350405 y z) (@lem1350404 y z)). Qed.
Lemma lem1350493 (x : real) : term146 x.
Proof. exact (@lem1350492 x term21). Qed.
Lemma lem1350494 (x : real) (h1 : term129 x) : term147 x.
Proof. exact (@lem1350493 x (@lem1350430 x h1)). Qed.
Lemma lem1350495 (x : real) (h1 : term147 x) : term147 x.
Proof. exact (h1). Qed.
Lemma lem1350496 (x : real) (h1 : term147 x) : term148 x.
Proof. exact (@lem1350495 x h1 (real_neg x)). Qed.
Lemma lem1350497 (x : real) : (term148 x) = (term149 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1350498 (x : real) (h1 : term147 x) : term149 x.
Proof. exact (EQ_MP (@lem1350497 x) (@lem1350496 x h1)). Qed.
Lemma lem1350502 (x : real) : (term20 x) = term21.
Proof. exact (EQ_MP (@lem1350381 x) (@lem1350380 x)). Qed.
Lemma lem1350503 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1350504 (x : real) : (term150 x) = term151.
Proof. exact (MK_COMB (@lem1350503) (@lem1350502 x)). Qed.
Lemma lem1350507 (x : real) : (term152 x) = (term152 x).
Proof. exact (eq_refl (term152 x)). Qed.
Lemma lem1350508 (x : real) : (term149 x) = (term153 x).
Proof. exact (MK_COMB (@lem1350504 x) (@lem1350507 x)). Qed.
Lemma lem1350509 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350510 (x : real) : (term154 x) = (term155 x).
Proof. exact (MK_COMB (@lem1350509) (@lem1350508 x)). Qed.
Lemma lem1350535 (P : real -> Prop) : (term121 P) = (term121 P).
Proof. exact (eq_refl (term121 P)). Qed.
Lemma lem1350536 (x : real) (P : real -> Prop) : (term156 x P) = (term157 x P).
Proof. exact (MK_COMB (@lem1350510 x) (@lem1350535 P)). Qed.
Lemma lem1350539 (x : real) (P : real -> Prop) : (term157 x P) = (term156 x P).
Proof. exact (SYM (@lem1350536 x P)). Qed.
Lemma lem1350543 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1350378 y x) (@lem1350377 x y)). Qed.
Lemma lem1350544 (x : real) : (term152 x) = (term158 x).
Proof. exact (@lem1350543 term21 (real_neg x)). Qed.
Lemma lem1350545 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem1350546 (x : real) : (term153 x) = (term159 x).
Proof. exact (MK_COMB (@lem1350545) (@lem1350544 x)). Qed.
Lemma lem1350547 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350548 (x : real) : (term155 x) = (term160 x).
Proof. exact (MK_COMB (@lem1350547) (@lem1350546 x)). Qed.
Lemma lem1350573 (P : real -> Prop) : (term121 P) = (term121 P).
Proof. exact (eq_refl (term121 P)). Qed.
Lemma lem1350574 (x : real) (P : real -> Prop) : (term157 x P) = (term161 x P).
Proof. exact (MK_COMB (@lem1350548 x) (@lem1350573 P)). Qed.
Lemma lem1350575 (x : real) (P : real -> Prop) : (term161 x P) = (term157 x P).
Proof. exact (SYM (@lem1350574 x P)). Qed.
Lemma lem1350579 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1350372 x) (@lem1350371 x)). Qed.
Lemma lem1350580 (x : real) : (term158 x) = (real_neg x).
Proof. exact (@lem1350579 (real_neg x)). Qed.
Lemma lem1350581 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem1350582 (x : real) : (term159 x) = (term162 x).
Proof. exact (MK_COMB (@lem1350581) (@lem1350580 x)). Qed.
Lemma lem1350583 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350584 (x : real) : (term160 x) = (term163 x).
Proof. exact (MK_COMB (@lem1350583) (@lem1350582 x)). Qed.
Lemma lem1350609 (P : real -> Prop) : (term121 P) = (term121 P).
Proof. exact (eq_refl (term121 P)). Qed.
Lemma lem1350610 (x : real) (P : real -> Prop) : (term161 x P) = (term164 x P).
Proof. exact (MK_COMB (@lem1350584 x) (@lem1350609 P)). Qed.
Lemma lem1350613 (x : real) (P : real -> Prop) : (term164 x P) = (term161 x P).
Proof. exact (SYM (@lem1350610 x P)). Qed.
Lemma lem1350615 (P : real -> Prop) (x' : real) (x : real) : (term165 P x x') = (term166 P x' x).
Proof. exact (eq_refl (term165 P x x')). Qed.
Lemma lem1350616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1350617 (P : real -> Prop) (x' : real) (x : real) : (term167 P x x') = (term168 P x' x).
Proof. exact (MK_COMB (@lem1350616) (@lem1350615 P x' x)). Qed.
Lemma lem1350618 (x' : real) : (term128 x') = (term128 x').
Proof. exact (eq_refl (term128 x')). Qed.
Lemma lem1350619 (P : real -> Prop) (x : real) (x' : real) : (term169 P x x') = (term170 P x x').
Proof. exact (MK_COMB (@lem1350617 P x' x) (@lem1350618 x')). Qed.
Lemma lem1350620 (P : real -> Prop) (x : real) : (term171 P x) = (term172 P x).
Proof. exact (fun_ext (fun x' : real => @lem1350619 P x x')). Qed.
Lemma lem1350621 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1350622 (P : real -> Prop) (x : real) : (term173 P x) = (term174 P x).
Proof. exact (MK_COMB (@lem1350621) (@lem1350620 P x)). Qed.
Lemma lem1350623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1350624 (P : real -> Prop) (x : real) : (term175 P x) = (term176 P x).
Proof. exact (MK_COMB (@lem1350623) (@lem1350622 P x)). Qed.
Lemma lem1350625 (P : real -> Prop) (x' : real) (x : real) : (term165 P x x') = (term166 P x' x).
Proof. exact (eq_refl (term165 P x x')). Qed.
Lemma lem1350626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350627 (P : real -> Prop) (x' : real) (x : real) : (term177 P x x') = (term178 P x' x).
Proof. exact (MK_COMB (@lem1350626) (@lem1350625 P x' x)). Qed.
Lemma lem1350628 (x' : real) (M : real) : (real_le x' M) = (real_le x' M).
Proof. exact (eq_refl (real_le x' M)). Qed.
Lemma lem1350629 (P : real -> Prop) (x : real) (x' : real) (M : real) : (term179 P x x' M) = (term180 P x x' M).
Proof. exact (MK_COMB (@lem1350627 P x' x) (@lem1350628 x' M)). Qed.
Lemma lem1350630 (P : real -> Prop) (x : real) (M : real) : (term181 P x M) = (term182 P x M).
Proof. exact (fun_ext (fun x' : real => @lem1350629 P x x' M)). Qed.
Lemma lem1350631 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1350632 (P : real -> Prop) (x : real) (M : real) : (term183 P x M) = (term184 P x M).
Proof. exact (MK_COMB (@lem1350631) (@lem1350630 P x M)). Qed.
Lemma lem1350633 (P : real -> Prop) (x : real) : (term185 P x) = (term186 P x).
Proof. exact (fun_ext (fun M : real => @lem1350632 P x M)). Qed.
Lemma lem1350634 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1350635 (P : real -> Prop) (x : real) : (term187 P x) = (term188 P x).
Proof. exact (MK_COMB (@lem1350634) (@lem1350633 P x)). Qed.
Lemma lem1350636 (P : real -> Prop) (x : real) : (term189 P x) = (term190 P x).
Proof. exact (MK_COMB (@lem1350624 P x) (@lem1350635 P x)). Qed.
Lemma lem1350637 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350638 (P : real -> Prop) (x : real) : (term191 P x) = (term192 P x).
Proof. exact (MK_COMB (@lem1350637) (@lem1350636 P x)). Qed.
Lemma lem1350639 (P : real -> Prop) (x' : real) (x : real) : (term165 P x x') = (term166 P x' x).
Proof. exact (eq_refl (term165 P x x')). Qed.
Lemma lem1350640 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350641 (P : real -> Prop) (x' : real) (x : real) : (term177 P x x') = (term178 P x' x).
Proof. exact (MK_COMB (@lem1350640) (@lem1350639 P x' x)). Qed.
Lemma lem1350642 (x' : real) (M : real) : (real_le x' M) = (real_le x' M).
Proof. exact (eq_refl (real_le x' M)). Qed.
Lemma lem1350643 (P : real -> Prop) (x : real) (x' : real) (M : real) : (term179 P x x' M) = (term180 P x x' M).
Proof. exact (MK_COMB (@lem1350641 P x' x) (@lem1350642 x' M)). Qed.
Lemma lem1350644 (P : real -> Prop) (x : real) (M : real) : (term181 P x M) = (term182 P x M).
Proof. exact (fun_ext (fun x' : real => @lem1350643 P x x' M)). Qed.
Lemma lem1350645 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1350646 (P : real -> Prop) (x : real) (M : real) : (term183 P x M) = (term184 P x M).
Proof. exact (MK_COMB (@lem1350645) (@lem1350644 P x M)). Qed.
Lemma lem1350647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1350648 (P : real -> Prop) (x : real) (M : real) : (term193 P x M) = (term194 P x M).
Proof. exact (MK_COMB (@lem1350647) (@lem1350646 P x M)). Qed.
Lemma lem1350649 (P : real -> Prop) (x' : real) (x : real) : (term165 P x x') = (term166 P x' x).
Proof. exact (eq_refl (term165 P x x')). Qed.
Lemma lem1350650 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350651 (P : real -> Prop) (x' : real) (x : real) : (term177 P x x') = (term178 P x' x).
Proof. exact (MK_COMB (@lem1350650) (@lem1350649 P x' x)). Qed.
Lemma lem1350652 (x' : real) (M' : real) : (real_le x' M') = (real_le x' M').
Proof. exact (eq_refl (real_le x' M')). Qed.
Lemma lem1350653 (P : real -> Prop) (x : real) (x' : real) (M' : real) : (term179 P x x' M') = (term180 P x x' M').
Proof. exact (MK_COMB (@lem1350651 P x' x) (@lem1350652 x' M')). Qed.
Lemma lem1350654 (P : real -> Prop) (x : real) (M' : real) : (term181 P x M') = (term182 P x M').
Proof. exact (fun_ext (fun x' : real => @lem1350653 P x x' M')). Qed.
Lemma lem1350655 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1350656 (P : real -> Prop) (x : real) (M' : real) : (term183 P x M') = (term184 P x M').
Proof. exact (MK_COMB (@lem1350655) (@lem1350654 P x M')). Qed.
Lemma lem1350657 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350658 (P : real -> Prop) (x : real) (M' : real) : (term195 P x M') = (term196 P x M').
Proof. exact (MK_COMB (@lem1350657) (@lem1350656 P x M')). Qed.
Lemma lem1350659 (M : real) (M' : real) : (real_le M M') = (real_le M M').
Proof. exact (eq_refl (real_le M M')). Qed.
Lemma lem1350660 (P : real -> Prop) (x : real) (M : real) (M' : real) : (term197 P x M M') = (term198 P x M M').
Proof. exact (MK_COMB (@lem1350658 P x M') (@lem1350659 M M')). Qed.
Lemma lem1350661 (P : real -> Prop) (x : real) (M : real) : (term199 P x M) = (term200 P x M).
Proof. exact (fun_ext (fun M' : real => @lem1350660 P x M M')). Qed.
Lemma lem1350662 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1350663 (P : real -> Prop) (x : real) (M : real) : (term201 P x M) = (term202 P x M).
Proof. exact (MK_COMB (@lem1350662) (@lem1350661 P x M)). Qed.
Lemma lem1350664 (P : real -> Prop) (x : real) (M : real) : (term203 P x M) = (term204 P x M).
Proof. exact (MK_COMB (@lem1350648 P x M) (@lem1350663 P x M)). Qed.
Lemma lem1350665 (P : real -> Prop) (x : real) : (term205 P x) = (term206 P x).
Proof. exact (fun_ext (fun M : real => @lem1350664 P x M)). Qed.
Lemma lem1350666 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1350667 (P : real -> Prop) (x : real) : (term207 P x) = (term208 P x).
Proof. exact (MK_COMB (@lem1350666) (@lem1350665 P x)). Qed.
Lemma lem1350668 (P : real -> Prop) (x : real) : (term116 P x) = (term209 P x).
Proof. exact (MK_COMB (@lem1350638 P x) (@lem1350667 P x)). Qed.
Lemma lem1350669 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350670 (P : real -> Prop) (x : real) : (term210 P x) = (term211 P x).
Proof. exact (MK_COMB (@lem1350669) (@lem1350668 P x)). Qed.
Lemma lem1350671 (P : real -> Prop) : (term121 P) = (term121 P).
Proof. exact (eq_refl (term121 P)). Qed.
Lemma lem1350672 (x : real) (P : real -> Prop) : (term212 x P) = (term213 x P).
Proof. exact (MK_COMB (@lem1350670 P x) (@lem1350671 P)). Qed.
Lemma lem1350673 (x : real) (P : real -> Prop) : (term213 x P) = (term212 x P).
Proof. exact (SYM (@lem1350672 x P)). Qed.
Lemma lem1350674 (P : real -> Prop) (x : real) (h1 : term190 P x) : term190 P x.
Proof. exact (h1). Qed.
Lemma lem1350675 (x : real) : term0 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1350676 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1350678 (x : real) : term214 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem1350679 (x : real) : (term214 x) = (real_le x x).
Proof. exact (eq_refl (term214 x)). Qed.
Lemma lem1350680 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem1350679 x) (@lem1350678 x)). Qed.
Lemma lem1350681 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem1350683 (P : real -> Prop) (x : real) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem1350697 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1350676 x) (@lem1350675 x)). Qed.
Lemma lem1350698 (P : real -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1350699 (P : real -> Prop) (x : real) : (term215 P x) = (P x).
Proof. exact (MK_COMB (@lem1350698 P) (@lem1350697 x)). Qed.
Lemma lem1350701 (P : real -> Prop) (x : real) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem1350683 P x) (@lem1350434 P x h1)). Qed.
Lemma lem1350702 (P : real -> Prop) (x : real) (h1 : P x) : (term215 P x) = True.
Proof. exact (TRANS (@lem1350699 P x) (@lem1350701 P x h1)). Qed.
Lemma lem1350703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1350704 (P : real -> Prop) (x : real) (h1 : P x) : (term216 P x) = (and True).
Proof. exact (MK_COMB (@lem1350703) (@lem1350702 P x h1)). Qed.
Lemma lem1350706 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem1350681 x) (@lem1350680 x)). Qed.
Lemma lem1350707 : term217 = True.
Proof. exact (@lem1350706 term21). Qed.
Lemma lem1350708 (P : real -> Prop) (x : real) (h1 : P x) : (term218 P x) = (True /\ True).
Proof. exact (MK_COMB (@lem1350704 P x h1) (@lem1350707)). Qed.
Lemma lem1350710 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1350711 : (True /\ True) = True.
Proof. exact (@lem1350710 True). Qed.
Lemma lem1350712 (P : real -> Prop) (x : real) (h1 : P x) : (term218 P x) = True.
Proof. exact (TRANS (@lem1350708 P x h1) (@lem1350711)). Qed.
Lemma lem1350713 (P : real -> Prop) (x : real) (h1 : P x) : True = (term218 P x).
Proof. exact (SYM (@lem1350712 P x h1)). Qed.
Lemma lem1350714 (P : real -> Prop) (x : real) (h1 : P x) : term218 P x.
Proof. exact (EQ_MP (@lem1350713 P x h1) (@lem0)). Qed.
Lemma lem1350715 (P : real -> Prop) (x : real) (h1 : P x) : term174 P x.
Proof. exact (ex_intro (term172 P x) term21 (@lem1350714 P x h1)). Qed.
Lemma lem1350716 (P : real -> Prop) (x' : real) (x : real) (h1 : term166 P x' x) : term166 P x' x.
Proof. exact (h1). Qed.
Lemma lem1350717 (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term136 P M x.
Proof. exact (@lem1350435 P M h1 x). Qed.
Lemma lem1350718 (P : real -> Prop) (x : real) (M : real) : (term136 P M x) = (term137 P x M).
Proof. exact (eq_refl (term136 P M x)). Qed.
Lemma lem1350721 (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term137 P x M.
Proof. exact (EQ_MP (@lem1350718 P x M) (@lem1350717 x P M h1)). Qed.
Lemma lem1350722 (x' : real) (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term219 P x' x M.
Proof. exact (@lem1350721 (real_add x' x) P M h1). Qed.
Lemma lem1350723 (M : real) (P : real -> Prop) (x' : real) (x : real) (h1 : term133 P M) (h2 : term166 P x' x) : term220 x' x M.
Proof. exact (@lem1350722 x' x P M h1 (@lem1350716 P x' x h2)). Qed.
Lemma lem1350724 (x' : real) (x : real) (M : real) (h1 : term220 x' x M) : term220 x' x M.
Proof. exact (h1). Qed.
Lemma lem1350726 (y : real) (z : real) : term54 y z.
Proof. exact (EQ_MP (@lem1350366 y z) (@lem1350365 y z)). Qed.
Lemma lem1350727 (x' : real) (x : real) (M : real) : term221 x' x M.
Proof. exact (@lem1350726 (real_add x' x) M). Qed.
Lemma lem1350728 (x' : real) (x : real) (M : real) (h1 : term220 x' x M) : term222 x' x M.
Proof. exact (@lem1350727 x' x M (@lem1350724 x' x M h1)). Qed.
Lemma lem1350729 (x' : real) (x : real) (M : real) (h1 : term220 x' x M) : term223 x' M x.
Proof. exact (@lem1350728 x' x M h1 (real_neg x)). Qed.
Lemma lem1350730 (x' : real) (x : real) (M : real) : (term223 x' M x) = (term224 x' x M).
Proof. exact (eq_refl (term223 x' M x)). Qed.
Lemma lem1350731 (x' : real) (x : real) (M : real) (h1 : term220 x' x M) : term224 x' x M.
Proof. exact (EQ_MP (@lem1350730 x' x M) (@lem1350729 x' x M h1)). Qed.
Lemma lem1350732 (x' : real) (x : real) (M : real) (h1 : term224 x' x M) : term224 x' x M.
Proof. exact (h1). Qed.
Lemma lem1350734 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1350342 y x) (@lem1350341 x y)). Qed.
Lemma lem1350735 (x' : real) (x : real) : (term225 x' x) = (term226 x' x).
Proof. exact (@lem1350734 (real_add x' x) (real_neg x)). Qed.
Lemma lem1350736 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1350737 (x' : real) (x : real) : (term227 x' x) = (term228 x' x).
Proof. exact (MK_COMB (@lem1350736) (@lem1350735 x' x)). Qed.
Lemma lem1350739 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1350342 y x) (@lem1350341 x y)). Qed.
Lemma lem1350740 (M : real) (x : real) : (term229 x M) = (term28 M x).
Proof. exact (@lem1350739 M (real_neg x)). Qed.
Lemma lem1350741 (x' : real) (M : real) (x : real) : (term224 x' x M) = (term230 x' M x).
Proof. exact (MK_COMB (@lem1350737 x' x) (@lem1350740 M x)). Qed.
Lemma lem1350742 (x' : real) (x : real) (M : real) (h1 : term224 x' x M) : term230 x' M x.
Proof. exact (EQ_MP (@lem1350741 x' M x) (@lem1350732 x' x M h1)). Qed.
Lemma lem1350746 (x : real) (y : real) (z : real) : (term6 x y z) = (term5 x y z).
Proof. exact (EQ_MP (@lem1350336 x y z) (@lem1350335 x y z)). Qed.
Lemma lem1350747 (x' : real) (x : real) : (term226 x' x) = (term231 x' x).
Proof. exact (@lem1350746 x' x (real_neg x)). Qed.
Lemma lem1350748 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1350749 (x' : real) (x : real) : (term228 x' x) = (term232 x' x).
Proof. exact (MK_COMB (@lem1350748) (@lem1350747 x' x)). Qed.
Lemma lem1350750 (M : real) (x : real) : (term28 M x) = (term28 M x).
Proof. exact (eq_refl (term28 M x)). Qed.
Lemma lem1350751 (x' : real) (M : real) (x : real) : (term230 x' M x) = (term233 x' M x).
Proof. exact (MK_COMB (@lem1350749 x' x) (@lem1350750 M x)). Qed.
Lemma lem1350752 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350753 (x' : real) (M : real) (x : real) : (term234 x' M x) = (term235 x' M x).
Proof. exact (MK_COMB (@lem1350752) (@lem1350751 x' M x)). Qed.
Lemma lem1350754 (x' : real) (M : real) (x : real) : (term236 x' M x) = (term236 x' M x).
Proof. exact (eq_refl (term236 x' M x)). Qed.
Lemma lem1350755 (x' : real) (M : real) (x : real) : (term237 x' M x) = (term238 x' M x).
Proof. exact (MK_COMB (@lem1350753 x' M x) (@lem1350754 x' M x)). Qed.
Lemma lem1350758 (x' : real) (M : real) (x : real) : (term238 x' M x) = (term237 x' M x).
Proof. exact (SYM (@lem1350755 x' M x)). Qed.
Lemma lem1350762 (x : real) : (term60 x) = term21.
Proof. exact (EQ_MP (@lem1350309 x) (@lem1350308 x)). Qed.
Lemma lem1350763 (x' : real) : (real_add x') = (real_add x').
Proof. exact (eq_refl (real_add x')). Qed.
Lemma lem1350764 (x : real) (x' : real) : (term231 x' x) = (term34 x').
Proof. exact (MK_COMB (@lem1350763 x') (@lem1350762 x)). Qed.
Lemma lem1350765 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1350766 (x : real) (x' : real) : (term232 x' x) = (term239 x').
Proof. exact (MK_COMB (@lem1350765) (@lem1350764 x x')). Qed.
Lemma lem1350769 (M : real) (x : real) : (term28 M x) = (term28 M x).
Proof. exact (eq_refl (term28 M x)). Qed.
Lemma lem1350770 (x' : real) (M : real) (x : real) : (term233 x' M x) = (term240 x' M x).
Proof. exact (MK_COMB (@lem1350766 x x') (@lem1350769 M x)). Qed.
Lemma lem1350771 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350772 (x' : real) (M : real) (x : real) : (term235 x' M x) = (term241 x' M x).
Proof. exact (MK_COMB (@lem1350771) (@lem1350770 x' M x)). Qed.
Lemma lem1350775 (x' : real) (M : real) (x : real) : (term236 x' M x) = (term236 x' M x).
Proof. exact (eq_refl (term236 x' M x)). Qed.
Lemma lem1350776 (x' : real) (M : real) (x : real) : (term238 x' M x) = (term242 x' M x).
Proof. exact (MK_COMB (@lem1350772 x' M x) (@lem1350775 x' M x)). Qed.
Lemma lem1350779 (x' : real) (M : real) (x : real) : (term242 x' M x) = (term238 x' M x).
Proof. exact (SYM (@lem1350776 x' M x)). Qed.
Lemma lem1350783 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1350283 x) (@lem1350282 x)). Qed.
Lemma lem1350784 (x' : real) : (term34 x') = x'.
Proof. exact (@lem1350783 x'). Qed.
Lemma lem1350785 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1350786 (x' : real) : (term239 x') = (real_le x').
Proof. exact (MK_COMB (@lem1350785) (@lem1350784 x')). Qed.
Lemma lem1350787 (M : real) (x : real) : (term28 M x) = (term28 M x).
Proof. exact (eq_refl (term28 M x)). Qed.
Lemma lem1350788 (x' : real) (M : real) (x : real) : (term240 x' M x) = (term236 x' M x).
Proof. exact (MK_COMB (@lem1350786 x') (@lem1350787 M x)). Qed.
Lemma lem1350789 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350790 (x' : real) (M : real) (x : real) : (term241 x' M x) = (term243 x' M x).
Proof. exact (MK_COMB (@lem1350789) (@lem1350788 x' M x)). Qed.
Lemma lem1350791 (x' : real) (M : real) (x : real) : (term236 x' M x) = (term236 x' M x).
Proof. exact (eq_refl (term236 x' M x)). Qed.
Lemma lem1350792 (x' : real) (M : real) (x : real) : (term242 x' M x) = (term244 x' M x).
Proof. exact (MK_COMB (@lem1350790 x' M x) (@lem1350791 x' M x)). Qed.
Lemma lem1350794 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1350795 (x' : real) (M : real) (x : real) : (term244 x' M x) = True.
Proof. exact (@lem1350794 (term236 x' M x)). Qed.
Lemma lem1350796 (x' : real) (M : real) (x : real) : (term242 x' M x) = True.
Proof. exact (TRANS (@lem1350792 x' M x) (@lem1350795 x' M x)). Qed.
Lemma lem1350797 (x' : real) (M : real) (x : real) : True = (term242 x' M x).
Proof. exact (SYM (@lem1350796 x' M x)). Qed.
Lemma lem1350798 (x' : real) (M : real) (x : real) : term242 x' M x.
Proof. exact (EQ_MP (@lem1350797 x' M x) (@lem0)). Qed.
Lemma lem1350799 (x' : real) (M : real) (x : real) : term238 x' M x.
Proof. exact (EQ_MP (@lem1350779 x' M x) (@lem1350798 x' M x)). Qed.
Lemma lem1350800 (x' : real) (M : real) (x : real) : term237 x' M x.
Proof. exact (EQ_MP (@lem1350758 x' M x) (@lem1350799 x' M x)). Qed.
Lemma lem1350801 (x' : real) (x : real) (M : real) (h1 : term224 x' x M) : term236 x' M x.
Proof. exact (@lem1350800 x' M x (@lem1350742 x' x M h1)). Qed.
Lemma lem1350802 (x' : real) (M : real) (x : real) : term245 x' M x.
Proof. exact (fun h0 : term224 x' x M => @lem1350801 x' x M h0). Qed.
Lemma lem1350803 (x' : real) (x : real) (M : real) (h1 : term220 x' x M) : term236 x' M x.
Proof. exact (@lem1350802 x' M x (@lem1350731 x' x M h1)). Qed.
Lemma lem1350804 (x' : real) (M : real) (x : real) : term246 x' M x.
Proof. exact (fun h0 : term220 x' x M => @lem1350803 x' x M h0). Qed.
Lemma lem1350805 (M : real) (P : real -> Prop) (x' : real) (x : real) (h1 : term133 P M) (h2 : term166 P x' x) : term236 x' M x.
Proof. exact (@lem1350804 x' M x (@lem1350723 M P x' x h1 h2)). Qed.
Lemma lem1350806 (x' : real) (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term247 P x' M x.
Proof. exact (fun h0 : term166 P x' x => @lem1350805 M P x' x h1 h0). Qed.
Lemma lem1350811 (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term248 P M x.
Proof. exact (fun x' : real => @lem1350806 x' x P M h1). Qed.
Lemma lem1350812 (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term188 P x.
Proof. exact (ex_intro (term186 P x) (term28 M x) (@lem1350811 x P M h1)). Qed.
Lemma lem1350813 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : term190 P x.
Proof. exact (conj (@lem1350715 P x h2) (@lem1350812 x P M h1)). Qed.
Lemma lem1350815 (a : Prop) (b : Prop) (c : Prop) : term75 a b c.
Proof. exact (@lem1350257 a b c (@lem1350249 a b c)). Qed.
Lemma lem1350816 (x : real) (P : real -> Prop) : term249 x P.
Proof. exact (@lem1350815 (term190 P x) (term208 P x) (term121 P)). Qed.
Lemma lem1350817 (P : real -> Prop) (x : real) (h1 : term208 P x) : term208 P x.
Proof. exact (h1). Qed.
Lemma lem1350818 (P : real -> Prop) (x : real) (B : real) (h1 : term204 P x B) : term204 P x B.
Proof. exact (h1). Qed.
Lemma lem1350819 (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term202 P x B.
Proof. exact (h1). Qed.
Lemma lem1350820 (P : real -> Prop) (x : real) (B : real) (h1 : term184 P x B) : term184 P x B.
Proof. exact (h1). Qed.
Lemma lem1350822 (y : real) (x : real) : y = (term31 y x).
Proof. exact (EQ_MP (@lem1349657 y x) (@lem1349680 y)). Qed.
Lemma lem1350823 (x' : real) (x : real) : x' = (term31 x' x).
Proof. exact (@lem1350822 x' x). Qed.
Lemma lem1350824 (P : real -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1350825 (P : real -> Prop) (x' : real) (x : real) : (P x') = (term250 P x' x).
Proof. exact (MK_COMB (@lem1350824 P) (@lem1350823 x' x)). Qed.
Lemma lem1350826 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350827 (P : real -> Prop) (x' : real) (x : real) : (term251 P x') = (term252 P x' x).
Proof. exact (MK_COMB (@lem1350826) (@lem1350825 P x' x)). Qed.
Lemma lem1350828 (x' : real) (B : real) (x : real) : (term253 x' B x) = (term253 x' B x).
Proof. exact (eq_refl (term253 x' B x)). Qed.
Lemma lem1350829 (P : real -> Prop) (x' : real) (B : real) (x : real) : (term254 P x' B x) = (term255 P x' B x).
Proof. exact (MK_COMB (@lem1350827 P x' x) (@lem1350828 x' B x)). Qed.
Lemma lem1350830 (P : real -> Prop) (x' : real) (B : real) (x : real) : (term255 P x' B x) = (term254 P x' B x).
Proof. exact (SYM (@lem1350829 P x' B x)). Qed.
Lemma lem1350831 (P : real -> Prop) (x' : real) (x : real) (h1 : term250 P x' x) : term250 P x' x.
Proof. exact (h1). Qed.
Lemma lem1350832 (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term136 P M x.
Proof. exact (@lem1350435 P M h1 x). Qed.
Lemma lem1350833 (P : real -> Prop) (x : real) (M : real) : (term136 P M x) = (term137 P x M).
Proof. exact (eq_refl (term136 P M x)). Qed.
Lemma lem1350836 (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term137 P x M.
Proof. exact (EQ_MP (@lem1350833 P x M) (@lem1350832 x P M h1)). Qed.
Lemma lem1350837 (x' : real) (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term256 P x' x M.
Proof. exact (@lem1350836 (term31 x' x) P M h1). Qed.
Lemma lem1350838 (M : real) (P : real -> Prop) (x' : real) (x : real) (h1 : term133 P M) (h2 : term250 P x' x) : term257 x' x M.
Proof. exact (@lem1350837 x' x P M h1 (@lem1350831 P x' x h2)). Qed.
Lemma lem1350840 (y : real) (z : real) : term54 y z.
Proof. exact (EQ_MP (@lem1350003 y z) (@lem1350002 y z)). Qed.
Lemma lem1350841 (x' : real) (x : real) (M : real) : term258 x' x M.
Proof. exact (@lem1350840 (term31 x' x) M). Qed.
Lemma lem1350842 (M : real) (P : real -> Prop) (x' : real) (x : real) (h1 : term133 P M) (h2 : term250 P x' x) : term259 x' x M.
Proof. exact (@lem1350841 x' x M (@lem1350838 M P x' x h1 h2)). Qed.
Lemma lem1350843 (M : real) (P : real -> Prop) (x' : real) (x : real) (h1 : term133 P M) (h2 : term250 P x' x) : term260 x' M x.
Proof. exact (@lem1350842 M P x' x h1 h2 x). Qed.
Lemma lem1350844 (x' : real) (x : real) (M : real) : (term260 x' M x) = (term261 x' x M).
Proof. exact (eq_refl (term260 x' M x)). Qed.
Lemma lem1350845 (M : real) (P : real -> Prop) (x' : real) (x : real) (h1 : term133 P M) (h2 : term250 P x' x) : term261 x' x M.
Proof. exact (EQ_MP (@lem1350844 x' x M) (@lem1350843 M P x' x h1 h2)). Qed.
Lemma lem1350846 (x' : real) (P : real -> Prop) (x : real) (B : real) (h1 : term184 P x B) : term262 P x B x'.
Proof. exact (@lem1350820 P x B h1 x'). Qed.
Lemma lem1350847 (P : real -> Prop) (x : real) (x' : real) (B : real) : (term262 P x B x') = (term180 P x x' B).
Proof. exact (eq_refl (term262 P x B x')). Qed.
Lemma lem1350850 (x' : real) (P : real -> Prop) (x : real) (B : real) (h1 : term184 P x B) : term180 P x x' B.
Proof. exact (EQ_MP (@lem1350847 P x x' B) (@lem1350846 x' P x B h1)). Qed.
Lemma lem1350851 (x' : real) (P : real -> Prop) (x : real) (B : real) (h1 : term184 P x B) : term263 P x' x B.
Proof. exact (@lem1350850 (real_sub x' x) P x B h1). Qed.
Lemma lem1350852 (B : real) (P : real -> Prop) (x' : real) (x : real) (h1 : term184 P x B) (h2 : term250 P x' x) : term264 x' x B.
Proof. exact (@lem1350851 x' P x B h1 (@lem1350831 P x' x h2)). Qed.
Lemma lem1350854 (y : real) (z : real) : term54 y z.
Proof. exact (EQ_MP (@lem1350003 y z) (@lem1350002 y z)). Qed.
Lemma lem1350855 (x' : real) (x : real) (B : real) : term265 x' x B.
Proof. exact (@lem1350854 (real_sub x' x) B). Qed.
Lemma lem1350856 (B : real) (P : real -> Prop) (x' : real) (x : real) (h1 : term184 P x B) (h2 : term250 P x' x) : term266 x' x B.
Proof. exact (@lem1350855 x' x B (@lem1350852 B P x' x h1 h2)). Qed.
Lemma lem1350857 (B : real) (P : real -> Prop) (x' : real) (x : real) (h1 : term184 P x B) (h2 : term250 P x' x) : term267 x' B x.
Proof. exact (@lem1350856 B P x' x h1 h2 x). Qed.
Lemma lem1350858 (x' : real) (x : real) (B : real) : (term267 x' B x) = (term268 x' x B).
Proof. exact (eq_refl (term267 x' B x)). Qed.
Lemma lem1350859 (B : real) (P : real -> Prop) (x' : real) (x : real) (h1 : term184 P x B) (h2 : term250 P x' x) : term268 x' x B.
Proof. exact (EQ_MP (@lem1350858 x' x B) (@lem1350857 B P x' x h1 h2)). Qed.
Lemma lem1350868 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349979 y x) (@lem1349978 x y)). Qed.
Lemma lem1350869 (x' : real) (x : real) : (term269 x' x) = (term270 x' x).
Proof. exact (@lem1350868 (term31 x' x) x). Qed.
Lemma lem1350870 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1350871 (x' : real) (x : real) : (term271 x' x) = (term272 x' x).
Proof. exact (MK_COMB (@lem1350870) (@lem1350869 x' x)). Qed.
Lemma lem1350873 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349979 y x) (@lem1349978 x y)). Qed.
Lemma lem1350874 (M : real) (x : real) : (real_add x M) = (real_add M x).
Proof. exact (@lem1350873 M x). Qed.
Lemma lem1350875 (x' : real) (M : real) (x : real) : (term261 x' x M) = (term273 x' M x).
Proof. exact (MK_COMB (@lem1350871 x' x) (@lem1350874 M x)). Qed.
Lemma lem1350876 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350877 (x' : real) (M : real) (x : real) : (term274 x' x M) = (term275 x' M x).
Proof. exact (MK_COMB (@lem1350876) (@lem1350875 x' M x)). Qed.
Lemma lem1350881 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349979 y x) (@lem1349978 x y)). Qed.
Lemma lem1350882 (x' : real) (x : real) : (term276 x' x) = (term31 x' x).
Proof. exact (@lem1350881 (real_sub x' x) x). Qed.
Lemma lem1350883 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1350884 (x' : real) (x : real) : (term277 x' x) = (term278 x' x).
Proof. exact (MK_COMB (@lem1350883) (@lem1350882 x' x)). Qed.
Lemma lem1350886 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349979 y x) (@lem1349978 x y)). Qed.
Lemma lem1350887 (B : real) (x : real) : (real_add x B) = (real_add B x).
Proof. exact (@lem1350886 B x). Qed.
Lemma lem1350888 (x' : real) (B : real) (x : real) : (term268 x' x B) = (term279 x' B x).
Proof. exact (MK_COMB (@lem1350884 x' x) (@lem1350887 B x)). Qed.
Lemma lem1350889 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350890 (x' : real) (B : real) (x : real) : (term280 x' x B) = (term281 x' B x).
Proof. exact (MK_COMB (@lem1350889) (@lem1350888 x' B x)). Qed.
Lemma lem1350892 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349979 y x) (@lem1349978 x y)). Qed.
Lemma lem1350893 (x : real) (B : real) : (real_add B x) = (real_add x B).
Proof. exact (@lem1350892 x B). Qed.
Lemma lem1350894 (x' : real) : (real_le x') = (real_le x').
Proof. exact (eq_refl (real_le x')). Qed.
Lemma lem1350895 (x' : real) (x : real) (B : real) : (term253 x' B x) = (term253 x' x B).
Proof. exact (MK_COMB (@lem1350894 x') (@lem1350893 x B)). Qed.
Lemma lem1350896 (x' : real) (x : real) (B : real) : (term282 x' B x) = (term283 x' x B).
Proof. exact (MK_COMB (@lem1350890 x' B x) (@lem1350895 x' x B)). Qed.
Lemma lem1350897 (M : real) (x' : real) (x : real) (B : real) : (term284 M x' B x) = (term285 M x' x B).
Proof. exact (MK_COMB (@lem1350877 x' M x) (@lem1350896 x' x B)). Qed.
Lemma lem1350898 (M : real) (x' : real) (B : real) (x : real) : (term285 M x' x B) = (term284 M x' B x).
Proof. exact (SYM (@lem1350897 M x' x B)). Qed.
Lemma lem1350902 (x : real) (y : real) (z : real) : (term6 x y z) = (term5 x y z).
Proof. exact (EQ_MP (@lem1349967 x y z) (@lem1349966 x y z)). Qed.
Lemma lem1350903 (x' : real) (x : real) : (term270 x' x) = (term286 x' x).
Proof. exact (@lem1350902 (real_sub x' x) x x). Qed.
Lemma lem1350905 (x : real) (y : real) : (real_sub x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1349973 x y) (@lem1349972 x y)). Qed.
Lemma lem1350906 (x' : real) (x : real) : (real_sub x' x) = (term28 x' x).
Proof. exact (@lem1350905 x' x). Qed.
Lemma lem1350907 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1350908 (x' : real) (x : real) : (term29 x' x) = (term30 x' x).
Proof. exact (MK_COMB (@lem1350907) (@lem1350906 x' x)). Qed.
Lemma lem1350909 (x : real) : (real_add x x) = (real_add x x).
Proof. exact (eq_refl (real_add x x)). Qed.
Lemma lem1350910 (x' : real) (x : real) : (term286 x' x) = (term287 x' x).
Proof. exact (MK_COMB (@lem1350908 x' x) (@lem1350909 x)). Qed.
Lemma lem1350912 (x : real) (y : real) (z : real) : (term6 x y z) = (term5 x y z).
Proof. exact (EQ_MP (@lem1349967 x y z) (@lem1349966 x y z)). Qed.
Lemma lem1350913 (x' : real) (x : real) : (term287 x' x) = (term288 x' x).
Proof. exact (@lem1350912 x' (real_neg x) (real_add x x)). Qed.
Lemma lem1350916 (x' : real) (x : real) : (term286 x' x) = (term288 x' x).
Proof. exact (TRANS (@lem1350910 x' x) (@lem1350913 x' x)). Qed.
Lemma lem1350917 (x' : real) (x : real) : (term270 x' x) = (term288 x' x).
Proof. exact (TRANS (@lem1350903 x' x) (@lem1350916 x' x)). Qed.
Lemma lem1350918 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1350919 (x' : real) (x : real) : (term272 x' x) = (term289 x' x).
Proof. exact (MK_COMB (@lem1350918) (@lem1350917 x' x)). Qed.
Lemma lem1350920 (M : real) (x : real) : (real_add M x) = (real_add M x).
Proof. exact (eq_refl (real_add M x)). Qed.
Lemma lem1350921 (x' : real) (M : real) (x : real) : (term273 x' M x) = (term290 x' M x).
Proof. exact (MK_COMB (@lem1350919 x' x) (@lem1350920 M x)). Qed.
Lemma lem1350922 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350923 (x' : real) (M : real) (x : real) : (term275 x' M x) = (term291 x' M x).
Proof. exact (MK_COMB (@lem1350922) (@lem1350921 x' M x)). Qed.
Lemma lem1350927 (x : real) (y : real) : (real_sub x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1349973 x y) (@lem1349972 x y)). Qed.
Lemma lem1350928 (x' : real) (x : real) : (real_sub x' x) = (term28 x' x).
Proof. exact (@lem1350927 x' x). Qed.
Lemma lem1350929 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1350930 (x' : real) (x : real) : (term29 x' x) = (term30 x' x).
Proof. exact (MK_COMB (@lem1350929) (@lem1350928 x' x)). Qed.
Lemma lem1350931 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1350932 (x' : real) (x : real) : (term31 x' x) = (term32 x' x).
Proof. exact (MK_COMB (@lem1350930 x' x) (@lem1350931 x)). Qed.
Lemma lem1350934 (x : real) (y : real) (z : real) : (term6 x y z) = (term5 x y z).
Proof. exact (EQ_MP (@lem1349967 x y z) (@lem1349966 x y z)). Qed.
Lemma lem1350935 (x' : real) (x : real) : (term32 x' x) = (term33 x' x).
Proof. exact (@lem1350934 x' (real_neg x) x). Qed.
Lemma lem1350937 (x : real) : (term20 x) = term21.
Proof. exact (EQ_MP (@lem1349958 x) (@lem1349957 x)). Qed.
Lemma lem1350938 (x' : real) : (real_add x') = (real_add x').
Proof. exact (eq_refl (real_add x')). Qed.
Lemma lem1350939 (x : real) (x' : real) : (term33 x' x) = (term34 x').
Proof. exact (MK_COMB (@lem1350938 x') (@lem1350937 x)). Qed.
Lemma lem1350940 (x : real) (x' : real) : (term32 x' x) = (term34 x').
Proof. exact (TRANS (@lem1350935 x' x) (@lem1350939 x x')). Qed.
Lemma lem1350941 (x : real) (x' : real) : (term31 x' x) = (term34 x').
Proof. exact (TRANS (@lem1350932 x' x) (@lem1350940 x x')). Qed.
Lemma lem1350942 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1350943 (x : real) (x' : real) : (term278 x' x) = (term239 x').
Proof. exact (MK_COMB (@lem1350942) (@lem1350941 x x')). Qed.
Lemma lem1350944 (B : real) (x : real) : (real_add B x) = (real_add B x).
Proof. exact (eq_refl (real_add B x)). Qed.
Lemma lem1350945 (x' : real) (B : real) (x : real) : (term279 x' B x) = (term292 x' B x).
Proof. exact (MK_COMB (@lem1350943 x x') (@lem1350944 B x)). Qed.
Lemma lem1350946 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350947 (x' : real) (B : real) (x : real) : (term281 x' B x) = (term293 x' B x).
Proof. exact (MK_COMB (@lem1350946) (@lem1350945 x' B x)). Qed.
Lemma lem1350948 (x' : real) (x : real) (B : real) : (term253 x' x B) = (term253 x' x B).
Proof. exact (eq_refl (term253 x' x B)). Qed.
Lemma lem1350949 (x' : real) (x : real) (B : real) : (term283 x' x B) = (term294 x' x B).
Proof. exact (MK_COMB (@lem1350947 x' B x) (@lem1350948 x' x B)). Qed.
Lemma lem1350952 (M : real) (x' : real) (x : real) (B : real) : (term285 M x' x B) = (term295 M x' x B).
Proof. exact (MK_COMB (@lem1350923 x' M x) (@lem1350949 x' x B)). Qed.
Lemma lem1350955 (M : real) (x' : real) (x : real) (B : real) : (term295 M x' x B) = (term285 M x' x B).
Proof. exact (SYM (@lem1350952 M x' x B)). Qed.
Lemma lem1350961 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1349937 x) (@lem1349936 x)). Qed.
Lemma lem1350962 (x' : real) : (term34 x') = x'.
Proof. exact (@lem1350961 x'). Qed.
Lemma lem1350963 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1350964 (x' : real) : (term239 x') = (real_le x').
Proof. exact (MK_COMB (@lem1350963) (@lem1350962 x')). Qed.
Lemma lem1350965 (B : real) (x : real) : (real_add B x) = (real_add B x).
Proof. exact (eq_refl (real_add B x)). Qed.
Lemma lem1350966 (x' : real) (B : real) (x : real) : (term292 x' B x) = (term253 x' B x).
Proof. exact (MK_COMB (@lem1350964 x') (@lem1350965 B x)). Qed.
Lemma lem1350967 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1350968 (x' : real) (B : real) (x : real) : (term293 x' B x) = (term296 x' B x).
Proof. exact (MK_COMB (@lem1350967) (@lem1350966 x' B x)). Qed.
Lemma lem1350969 (x' : real) (x : real) (B : real) : (term253 x' x B) = (term253 x' x B).
Proof. exact (eq_refl (term253 x' x B)). Qed.
Lemma lem1350970 (x' : real) (x : real) (B : real) : (term294 x' x B) = (term297 x' x B).
Proof. exact (MK_COMB (@lem1350968 x' B x) (@lem1350969 x' x B)). Qed.
Lemma lem1350973 (x' : real) (M : real) (x : real) : (term291 x' M x) = (term291 x' M x).
Proof. exact (eq_refl (term291 x' M x)). Qed.
Lemma lem1350974 (M : real) (x' : real) (x : real) (B : real) : (term295 M x' x B) = (term298 M x' x B).
Proof. exact (MK_COMB (@lem1350973 x' M x) (@lem1350970 x' x B)). Qed.
Lemma lem1350977 (M : real) (x' : real) (x : real) (B : real) : (term298 M x' x B) = (term295 M x' x B).
Proof. exact (SYM (@lem1350974 M x' x B)). Qed.
Lemma lem1350979 (x' : real) (B : real) (x : real) (h1 : term253 x' B x) : term253 x' B x.
Proof. exact (h1). Qed.
Lemma lem1350981 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349911 y x) (@lem1349910 x y)). Qed.
Lemma lem1350982 (B : real) (x : real) : (real_add x B) = (real_add B x).
Proof. exact (@lem1350981 B x). Qed.
Lemma lem1350983 (x' : real) : (real_le x') = (real_le x').
Proof. exact (eq_refl (real_le x')). Qed.
Lemma lem1350984 (x' : real) (B : real) (x : real) : (term253 x' x B) = (term253 x' B x).
Proof. exact (MK_COMB (@lem1350983 x') (@lem1350982 B x)). Qed.
Lemma lem1350985 (x' : real) (x : real) (B : real) : (term253 x' B x) = (term253 x' x B).
Proof. exact (SYM (@lem1350984 x' B x)). Qed.
Lemma lem1351009 (x' : real) (B : real) (x : real) : (term253 x' B x) = ((term253 x' B x) = True).
Proof. exact (@lem7 (term253 x' B x)). Qed.
Lemma lem1351012 (x' : real) (B : real) (x : real) (h1 : term253 x' B x) : (term253 x' B x) = True.
Proof. exact (EQ_MP (@lem1351009 x' B x) (@lem1350979 x' B x h1)). Qed.
Lemma lem1351013 (x' : real) (B : real) (x : real) (h1 : term253 x' B x) : True = (term253 x' B x).
Proof. exact (SYM (@lem1351012 x' B x h1)). Qed.
Lemma lem1351014 (x' : real) (B : real) (x : real) (h1 : term253 x' B x) : term253 x' B x.
Proof. exact (EQ_MP (@lem1351013 x' B x h1) (@lem0)). Qed.
Lemma lem1351015 (x' : real) (B : real) (x : real) (h1 : term253 x' B x) : term253 x' x B.
Proof. exact (EQ_MP (@lem1350985 x' x B) (@lem1351014 x' B x h1)). Qed.
Lemma lem1351016 (x' : real) (B : real) (x : real) (h1 : term253 x' B x) : (term253 x' B x) = (term253 x' x B).
Proof. exact (prop_ext (fun h2 : term253 x' B x => @lem1351015 x' B x h1) (fun h2 : term253 x' x B => @lem1350979 x' B x h1)). Qed.
Lemma lem1351017 (x' : real) (B : real) (x : real) (h1 : term253 x' B x) : term253 x' x B.
Proof. exact (EQ_MP (@lem1351016 x' B x h1) (@lem1350979 x' B x h1)). Qed.
Lemma lem1351018 (x' : real) (x : real) (B : real) : term297 x' x B.
Proof. exact (fun h0 : term253 x' B x => @lem1351017 x' B x h0). Qed.
Lemma lem1351019 (M : real) (x' : real) (x : real) (B : real) : term298 M x' x B.
Proof. exact (fun h0 : term290 x' M x => @lem1351018 x' x B). Qed.
Lemma lem1351020 (M : real) (x' : real) (x : real) (B : real) : term295 M x' x B.
Proof. exact (EQ_MP (@lem1350977 M x' x B) (@lem1351019 M x' x B)). Qed.
Lemma lem1351021 (M : real) (x' : real) (x : real) (B : real) : term285 M x' x B.
Proof. exact (EQ_MP (@lem1350955 M x' x B) (@lem1351020 M x' x B)). Qed.
Lemma lem1351022 (M : real) (x' : real) (B : real) (x : real) : term284 M x' B x.
Proof. exact (EQ_MP (@lem1350898 M x' B x) (@lem1351021 M x' x B)). Qed.
Lemma lem1351023 (B : real) (M : real) (P : real -> Prop) (x' : real) (x : real) (h1 : term133 P M) (h2 : term250 P x' x) : term282 x' B x.
Proof. exact (@lem1351022 M x' B x (@lem1350845 M P x' x h1 h2)). Qed.
Lemma lem1351024 (M : real) (B : real) (P : real -> Prop) (x' : real) (x : real) (h1 : term133 P M) (h2 : term184 P x B) (h3 : term250 P x' x) : term253 x' B x.
Proof. exact (@lem1351023 B M P x' x h1 h3 (@lem1350859 B P x' x h2 h3)). Qed.
Lemma lem1351025 (x' : real) (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term133 P M) (h2 : term184 P x B) : term255 P x' B x.
Proof. exact (fun h0 : term250 P x' x => @lem1351024 M B P x' x h1 h2 h0). Qed.
Lemma lem1351026 (x' : real) (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term133 P M) (h2 : term184 P x B) : term254 P x' B x.
Proof. exact (EQ_MP (@lem1350830 P x' B x) (@lem1351025 x' M P x B h1 h2)). Qed.
Lemma lem1351031 (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term133 P M) (h2 : term184 P x B) : term299 P B x.
Proof. exact (fun x' : real => @lem1351026 x' M P x B h1 h2). Qed.
Lemma lem1351032 (P : real -> Prop) (M' : real) (h1 : term133 P M') : term133 P M'.
Proof. exact (h1). Qed.
Lemma lem1351033 (B : real) (M' : real) (x : real) (h1 : term300 B M' x) : term300 B M' x.
Proof. exact (h1). Qed.
Lemma lem1351052 (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term202 P x B.
Proof. exact (h1). Qed.
Lemma lem1351053 (M' : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term301 P x B M'.
Proof. exact (@lem1351052 P x B h1 M'). Qed.
Lemma lem1351054 (P : real -> Prop) (x : real) (B : real) (M' : real) : (term301 P x B M') = (term198 P x B M').
Proof. exact (eq_refl (term301 P x B M')). Qed.
Lemma lem1351055 (M' : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term198 P x B M'.
Proof. exact (EQ_MP (@lem1351054 P x B M') (@lem1351053 M' P x B h1)). Qed.
Lemma lem1351056 (P : real -> Prop) (x : real) (M' : real) (h1 : term184 P x M') : term184 P x M'.
Proof. exact (h1). Qed.
Lemma lem1351057 (B : real) (P : real -> Prop) (x : real) (M' : real) (h1 : term202 P x B) (h2 : term184 P x M') : real_le B M'.
Proof. exact (@lem1351055 M' P x B h1 (@lem1351056 P x M' h2)). Qed.
Lemma lem1351058 (B : real) (P : real -> Prop) (x : real) (M' : real) (h1 : term184 P x M') : term302 P x B M'.
Proof. exact (fun h0 : term202 P x B => @lem1351057 B P x M' h0 h1). Qed.
Lemma lem1351059 (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term202 P x B.
Proof. exact (h1). Qed.
Lemma lem1351060 (B : real) (P : real -> Prop) (x : real) (M' : real) (h1 : term202 P x B) (h2 : term184 P x M') : real_le B M'.
Proof. exact (@lem1351058 B P x M' h2 (@lem1351059 P x B h1)). Qed.
Lemma lem1351061 (M' : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term198 P x B M'.
Proof. exact (fun h0 : term184 P x M' => @lem1351060 B P x M' h1 h0). Qed.
Lemma lem1351062 (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term202 P x B.
Proof. exact (fun M' : real => @lem1351061 M' P x B h1). Qed.
Lemma lem1351063 (P : real -> Prop) (x : real) (B : real) : term303 P x B.
Proof. exact (fun h0 : term202 P x B => @lem1351062 P x B h0). Qed.
Lemma lem1351064 (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term202 P x B.
Proof. exact (@lem1351063 P x B (@lem1350819 P x B h1)). Qed.
Lemma lem1351065 (M' : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term301 P x B M'.
Proof. exact (@lem1351064 P x B h1 M'). Qed.
Lemma lem1351066 (P : real -> Prop) (x : real) (B : real) (M' : real) : (term301 P x B M') = (term198 P x B M').
Proof. exact (eq_refl (term301 P x B M')). Qed.
Lemma lem1351069 (M' : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term198 P x B M'.
Proof. exact (EQ_MP (@lem1351066 P x B M') (@lem1351065 M' P x B h1)). Qed.
Lemma lem1351070 (M' : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term304 P B M' x.
Proof. exact (@lem1351069 (real_sub M' x) P x B h1). Qed.
Lemma lem1351071 (P : real -> Prop) (z : real) (x : real) (h1 : term166 P z x) : term166 P z x.
Proof. exact (h1). Qed.
Lemma lem1351072 (z : real) (x : real) (M' : real) (h1 : term220 z x M') : term220 z x M'.
Proof. exact (h1). Qed.
Lemma lem1351073 (P : real -> Prop) (M' : real) (h1 : term133 P M') : term133 P M'.
Proof. exact (h1). Qed.
Lemma lem1351074 (x : real) (P : real -> Prop) (M' : real) (h1 : term133 P M') : term136 P M' x.
Proof. exact (@lem1351073 P M' h1 x). Qed.
Lemma lem1351075 (P : real -> Prop) (x : real) (M' : real) : (term136 P M' x) = (term137 P x M').
Proof. exact (eq_refl (term136 P M' x)). Qed.
Lemma lem1351076 (x : real) (P : real -> Prop) (M' : real) (h1 : term133 P M') : term137 P x M'.
Proof. exact (EQ_MP (@lem1351075 P x M') (@lem1351074 x P M' h1)). Qed.
Lemma lem1351077 (P : real -> Prop) (x : real) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1351078 (M' : real) (P : real -> Prop) (x : real) (h1 : term133 P M') (h2 : P x) : real_le x M'.
Proof. exact (@lem1351076 x P M' h1 (@lem1351077 P x h2)). Qed.
Lemma lem1351079 (M' : real) (P : real -> Prop) (x : real) (h1 : P x) : term305 P x M'.
Proof. exact (fun h0 : term133 P M' => @lem1351078 M' P x h0 h1). Qed.
Lemma lem1351080 (P : real -> Prop) (M' : real) (h1 : term133 P M') : term133 P M'.
Proof. exact (h1). Qed.
Lemma lem1351081 (M' : real) (P : real -> Prop) (x : real) (h1 : term133 P M') (h2 : P x) : real_le x M'.
Proof. exact (@lem1351079 M' P x h2 (@lem1351080 P M' h1)). Qed.
Lemma lem1351082 (x : real) (P : real -> Prop) (M' : real) (h1 : term133 P M') : term137 P x M'.
Proof. exact (fun h0 : P x => @lem1351081 M' P x h1 h0). Qed.
Lemma lem1351083 (P : real -> Prop) (M' : real) (h1 : term133 P M') : term133 P M'.
Proof. exact (fun x : real => @lem1351082 x P M' h1). Qed.
Lemma lem1351084 (P : real -> Prop) (M' : real) : term306 P M'.
Proof. exact (fun h0 : term133 P M' => @lem1351083 P M' h0). Qed.
Lemma lem1351085 (P : real -> Prop) (M' : real) (h1 : term133 P M') : term133 P M'.
Proof. exact (@lem1351084 P M' (@lem1351032 P M' h1)). Qed.
Lemma lem1351086 (x : real) (P : real -> Prop) (M' : real) (h1 : term133 P M') : term136 P M' x.
Proof. exact (@lem1351085 P M' h1 x). Qed.
Lemma lem1351087 (P : real -> Prop) (x : real) (M' : real) : (term136 P M' x) = (term137 P x M').
Proof. exact (eq_refl (term136 P M' x)). Qed.
Lemma lem1351090 (x : real) (P : real -> Prop) (M' : real) (h1 : term133 P M') : term137 P x M'.
Proof. exact (EQ_MP (@lem1351087 P x M') (@lem1351086 x P M' h1)). Qed.
Lemma lem1351091 (z : real) (x : real) (P : real -> Prop) (M' : real) (h1 : term133 P M') : term219 P z x M'.
Proof. exact (@lem1351090 (real_add z x) P M' h1). Qed.
Lemma lem1351118 (P : real -> Prop) (z : real) (x : real) : (term166 P z x) = ((term166 P z x) = True).
Proof. exact (@lem7 (term166 P z x)). Qed.
Lemma lem1351121 (P : real -> Prop) (z : real) (x : real) (h1 : term166 P z x) : (term166 P z x) = True.
Proof. exact (EQ_MP (@lem1351118 P z x) (@lem1351071 P z x h1)). Qed.
Lemma lem1351122 (P : real -> Prop) (z : real) (x : real) (h1 : term166 P z x) : True = (term166 P z x).
Proof. exact (SYM (@lem1351121 P z x h1)). Qed.
Lemma lem1351123 (P : real -> Prop) (z : real) (x : real) (h1 : term166 P z x) : term166 P z x.
Proof. exact (EQ_MP (@lem1351122 P z x h1) (@lem0)). Qed.
Lemma lem1351124 (M' : real) (P : real -> Prop) (z : real) (x : real) (h1 : term133 P M') (h2 : term166 P z x) : term220 z x M'.
Proof. exact (@lem1351091 z x P M' h1 (@lem1351123 P z x h2)). Qed.
Lemma lem1351125 (z : real) (x : real) (M' : real) (h1 : term220 z x M') : term220 z x M'.
Proof. exact (h1). Qed.
Lemma lem1351127 (y : real) (z : real) : term54 y z.
Proof. exact (EQ_MP (@lem1349905 y z) (@lem1349904 y z)). Qed.
Lemma lem1351128 (z : real) (x : real) (M' : real) : term221 z x M'.
Proof. exact (@lem1351127 (real_add z x) M'). Qed.
Lemma lem1351129 (z : real) (x : real) (M' : real) (h1 : term220 z x M') : term222 z x M'.
Proof. exact (@lem1351128 z x M' (@lem1351125 z x M' h1)). Qed.
Lemma lem1351130 (z : real) (x : real) (M' : real) (h1 : term220 z x M') : term223 z M' x.
Proof. exact (@lem1351129 z x M' h1 (real_neg x)). Qed.
Lemma lem1351131 (z : real) (x : real) (M' : real) : (term223 z M' x) = (term224 z x M').
Proof. exact (eq_refl (term223 z M' x)). Qed.
Lemma lem1351132 (z : real) (x : real) (M' : real) (h1 : term220 z x M') : term224 z x M'.
Proof. exact (EQ_MP (@lem1351131 z x M') (@lem1351130 z x M' h1)). Qed.
Lemma lem1351136 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349881 y x) (@lem1349880 x y)). Qed.
Lemma lem1351137 (z : real) (x : real) : (term225 z x) = (term226 z x).
Proof. exact (@lem1351136 (real_add z x) (real_neg x)). Qed.
Lemma lem1351138 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1351139 (z : real) (x : real) : (term227 z x) = (term228 z x).
Proof. exact (MK_COMB (@lem1351138) (@lem1351137 z x)). Qed.
Lemma lem1351141 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349881 y x) (@lem1349880 x y)). Qed.
Lemma lem1351142 (M' : real) (x : real) : (term229 x M') = (term28 M' x).
Proof. exact (@lem1351141 M' (real_neg x)). Qed.
Lemma lem1351143 (z : real) (M' : real) (x : real) : (term224 z x M') = (term230 z M' x).
Proof. exact (MK_COMB (@lem1351139 z x) (@lem1351142 M' x)). Qed.
Lemma lem1351144 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1351145 (z : real) (M' : real) (x : real) : (term307 z x M') = (term234 z M' x).
Proof. exact (MK_COMB (@lem1351144) (@lem1351143 z M' x)). Qed.
Lemma lem1351146 (z : real) (M' : real) (x : real) : (term300 z M' x) = (term300 z M' x).
Proof. exact (eq_refl (term300 z M' x)). Qed.
Lemma lem1351147 (z : real) (M' : real) (x : real) : (term308 z M' x) = (term309 z M' x).
Proof. exact (MK_COMB (@lem1351145 z M' x) (@lem1351146 z M' x)). Qed.
Lemma lem1351148 (z : real) (M' : real) (x : real) : (term309 z M' x) = (term308 z M' x).
Proof. exact (SYM (@lem1351147 z M' x)). Qed.
Lemma lem1351152 (x : real) (y : real) : (real_sub x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1349875 x y) (@lem1349874 x y)). Qed.
Lemma lem1351153 (M' : real) (x : real) : (real_sub M' x) = (term28 M' x).
Proof. exact (@lem1351152 M' x). Qed.
Lemma lem1351154 (z : real) : (real_le z) = (real_le z).
Proof. exact (eq_refl (real_le z)). Qed.
Lemma lem1351155 (z : real) (M' : real) (x : real) : (term300 z M' x) = (term236 z M' x).
Proof. exact (MK_COMB (@lem1351154 z) (@lem1351153 M' x)). Qed.
Lemma lem1351156 (z : real) (M' : real) (x : real) : (term234 z M' x) = (term234 z M' x).
Proof. exact (eq_refl (term234 z M' x)). Qed.
Lemma lem1351157 (z : real) (M' : real) (x : real) : (term309 z M' x) = (term237 z M' x).
Proof. exact (MK_COMB (@lem1351156 z M' x) (@lem1351155 z M' x)). Qed.
Lemma lem1351160 (z : real) (M' : real) (x : real) : (term237 z M' x) = (term309 z M' x).
Proof. exact (SYM (@lem1351157 z M' x)). Qed.
Lemma lem1351162 (a : Prop) (b : Prop) : term42 a b.
Proof. exact (@lem1349869 a b (@lem1157 a b)). Qed.
Lemma lem1351163 (z : real) (M' : real) (x : real) : term310 z M' x.
Proof. exact (@lem1351162 (term230 z M' x) (term236 z M' x)). Qed.
Lemma lem1351164 (M' : real) (x : real) : (term28 M' x) = (term28 M' x).
Proof. exact (eq_refl (term28 M' x)). Qed.
Lemma lem1351165 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1351169 (x : real) (y : real) (z : real) : (term6 x y z) = (term5 x y z).
Proof. exact (EQ_MP (@lem1349860 x y z) (@lem1349859 x y z)). Qed.
Lemma lem1351170 (z : real) (x : real) : (term226 z x) = (term231 z x).
Proof. exact (@lem1351169 z x (real_neg x)). Qed.
Lemma lem1351171 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1351172 (z : real) (x : real) : (term311 z x) = (term312 z x).
Proof. exact (MK_COMB (@lem1351171) (@lem1351170 z x)). Qed.
Lemma lem1351173 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1351174 (x : real) (z : real) : ((term226 z x) = z) = ((term231 z x) = z).
Proof. exact (MK_COMB (@lem1351172 z x) (@lem1351173 z)). Qed.
Lemma lem1351177 (x : real) (z : real) : ((term231 z x) = z) = ((term226 z x) = z).
Proof. exact (SYM (@lem1351174 x z)). Qed.
Lemma lem1351181 (x : real) : (term60 x) = term21.
Proof. exact (EQ_MP (@lem1349833 x) (@lem1349832 x)). Qed.
Lemma lem1351182 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1351183 (x : real) (z : real) : (term231 z x) = (term34 z).
Proof. exact (MK_COMB (@lem1351182 z) (@lem1351181 x)). Qed.
Lemma lem1351184 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1351185 (x : real) (z : real) : (term312 z x) = (term36 z).
Proof. exact (MK_COMB (@lem1351184) (@lem1351183 x z)). Qed.
Lemma lem1351186 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1351187 (x : real) (z : real) : ((term231 z x) = z) = ((term34 z) = z).
Proof. exact (MK_COMB (@lem1351185 x z) (@lem1351186 z)). Qed.
Lemma lem1351190 (x : real) (z : real) : ((term34 z) = z) = ((term231 z x) = z).
Proof. exact (SYM (@lem1351187 x z)). Qed.
Lemma lem1351194 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1349807 x) (@lem1349806 x)). Qed.
Lemma lem1351195 (z : real) : (term34 z) = z.
Proof. exact (@lem1351194 z). Qed.
Lemma lem1351196 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1351197 (z : real) : (term36 z) = (@eq real z).
Proof. exact (MK_COMB (@lem1351196) (@lem1351195 z)). Qed.
Lemma lem1351198 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1351199 (z : real) : ((term34 z) = z) = (z = z).
Proof. exact (MK_COMB (@lem1351197 z) (@lem1351198 z)). Qed.
Lemma lem1351201 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1351202 (x : real) : (x = x) = True.
Proof. exact (@lem1351201 real x). Qed.
Lemma lem1351203 (z : real) : (z = z) = True.
Proof. exact (@lem1351202 z). Qed.
Lemma lem1351204 (z : real) : ((term34 z) = z) = True.
Proof. exact (TRANS (@lem1351199 z) (@lem1351203 z)). Qed.
Lemma lem1351205 (z : real) : True = ((term34 z) = z).
Proof. exact (SYM (@lem1351204 z)). Qed.
Lemma lem1351206 (z : real) : (term34 z) = z.
Proof. exact (EQ_MP (@lem1351205 z) (@lem0)). Qed.
Lemma lem1351207 (x : real) (z : real) : (term231 z x) = z.
Proof. exact (EQ_MP (@lem1351190 x z) (@lem1351206 z)). Qed.
Lemma lem1351208 (x : real) (z : real) : (term226 z x) = z.
Proof. exact (EQ_MP (@lem1351177 x z) (@lem1351207 x z)). Qed.
Lemma lem1351209 (x : real) (z : real) : (term228 z x) = (real_le z).
Proof. exact (MK_COMB (@lem1351165) (@lem1351208 x z)). Qed.
Lemma lem1351210 (z : real) (M' : real) (x : real) : (term230 z M' x) = (term236 z M' x).
Proof. exact (MK_COMB (@lem1351209 x z) (@lem1351164 M' x)). Qed.
Lemma lem1351211 (z : real) (M' : real) (x : real) : term237 z M' x.
Proof. exact (@lem1351163 z M' x (@lem1351210 z M' x)). Qed.
Lemma lem1351212 (z : real) (M' : real) (x : real) : term309 z M' x.
Proof. exact (EQ_MP (@lem1351160 z M' x) (@lem1351211 z M' x)). Qed.
Lemma lem1351213 (z : real) (M' : real) (x : real) : term308 z M' x.
Proof. exact (EQ_MP (@lem1351148 z M' x) (@lem1351212 z M' x)). Qed.
Lemma lem1351214 (z : real) (x : real) (M' : real) (h1 : term220 z x M') : term300 z M' x.
Proof. exact (@lem1351213 z M' x (@lem1351132 z x M' h1)). Qed.
Lemma lem1351215 (z : real) (M' : real) (x : real) : term313 z M' x.
Proof. exact (fun h0 : term220 z x M' => @lem1351214 z x M' h0). Qed.
Lemma lem1351216 (z : real) (x : real) (M' : real) (h1 : term220 z x M') : term300 z M' x.
Proof. exact (@lem1351215 z M' x (@lem1351072 z x M' h1)). Qed.
Lemma lem1351217 (M' : real) (P : real -> Prop) (z : real) (x : real) (h1 : term133 P M') (h2 : term166 P z x) : (term220 z x M') = (term300 z M' x).
Proof. exact (prop_ext (fun h3 : term220 z x M' => @lem1351216 z x M' h3) (fun h3 : term300 z M' x => @lem1351124 M' P z x h1 h2)). Qed.
Lemma lem1351218 (M' : real) (P : real -> Prop) (z : real) (x : real) (h1 : term133 P M') (h2 : term166 P z x) : term300 z M' x.
Proof. exact (EQ_MP (@lem1351217 M' P z x h1 h2) (@lem1351124 M' P z x h1 h2)). Qed.
Lemma lem1351219 (z : real) (x : real) (P : real -> Prop) (M' : real) (h1 : term133 P M') : term314 P z M' x.
Proof. exact (fun h0 : term166 P z x => @lem1351218 M' P z x h1 h0). Qed.
Lemma lem1351224 (x : real) (P : real -> Prop) (M' : real) (h1 : term133 P M') : term315 P M' x.
Proof. exact (fun z : real => @lem1351219 z x P M' h1). Qed.
Lemma lem1351225 (x : real) (B : real) (P : real -> Prop) (M' : real) (h1 : term202 P x B) (h2 : term133 P M') : term300 B M' x.
Proof. exact (@lem1351070 M' P x B h1 (@lem1351224 x P M' h2)). Qed.
Lemma lem1351226 (B : real) (M' : real) (x : real) (h1 : term300 B M' x) : term300 B M' x.
Proof. exact (h1). Qed.
Lemma lem1351228 (y : real) (z : real) : term54 y z.
Proof. exact (EQ_MP (@lem1349781 y z) (@lem1349780 y z)). Qed.
Lemma lem1351229 (B : real) (M' : real) (x : real) : term316 B M' x.
Proof. exact (@lem1351228 B (real_sub M' x)). Qed.
Lemma lem1351230 (B : real) (M' : real) (x : real) (h1 : term300 B M' x) : term317 B M' x.
Proof. exact (@lem1351229 B M' x (@lem1351226 B M' x h1)). Qed.
Lemma lem1351231 (B : real) (M' : real) (x : real) (h1 : term300 B M' x) : term318 B M' x.
Proof. exact (@lem1351230 B M' x h1 x). Qed.
Lemma lem1351232 (B : real) (M' : real) (x : real) : (term318 B M' x) = (term319 B M' x).
Proof. exact (eq_refl (term318 B M' x)). Qed.
Lemma lem1351233 (B : real) (M' : real) (x : real) (h1 : term300 B M' x) : term319 B M' x.
Proof. exact (EQ_MP (@lem1351232 B M' x) (@lem1351231 B M' x h1)). Qed.
Lemma lem1351235 (a : Prop) (b : Prop) : term42 a b.
Proof. exact (@lem1349757 a b (@lem1157 a b)). Qed.
Lemma lem1351236 (B : real) (x : real) (M' : real) : term320 B x M'.
Proof. exact (@lem1351235 (term319 B M' x) (term220 B x M')). Qed.
Lemma lem1351237 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1351238 (x : real) : term2 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1351239 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1351240 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1351239 x) (@lem1351238 x)). Qed.
Lemma lem1351241 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1351240 x y). Qed.
Lemma lem1351242 (y : real) (x : real) : (term4 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1351245 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1351242 y x) (@lem1351241 x y)). Qed.
Lemma lem1351246 (B : real) (x : real) : (real_add x B) = (real_add B x).
Proof. exact (@lem1351245 B x). Qed.
Lemma lem1351250 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1349748 y x) (@lem1349747 x y)). Qed.
Lemma lem1351251 (M' : real) (x : real) : (term276 M' x) = (term31 M' x).
Proof. exact (@lem1351250 (real_sub M' x) x). Qed.
Lemma lem1351252 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1351253 (M' : real) (x : real) : (term321 M' x) = (term322 M' x).
Proof. exact (MK_COMB (@lem1351252) (@lem1351251 M' x)). Qed.
Lemma lem1351254 (M' : real) : M' = M'.
Proof. exact (eq_refl M'). Qed.
Lemma lem1351255 (x : real) (M' : real) : ((term276 M' x) = M') = ((term31 M' x) = M').
Proof. exact (MK_COMB (@lem1351253 M' x) (@lem1351254 M')). Qed.
Lemma lem1351256 (x : real) (M' : real) : ((term31 M' x) = M') = ((term276 M' x) = M').
Proof. exact (SYM (@lem1351255 x M')). Qed.
Lemma lem1351260 (x : real) (y : real) : (real_sub x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1349742 x y) (@lem1349741 x y)). Qed.
Lemma lem1351261 (M' : real) (x : real) : (real_sub M' x) = (term28 M' x).
Proof. exact (@lem1351260 M' x). Qed.
Lemma lem1351262 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1351263 (M' : real) (x : real) : (term29 M' x) = (term30 M' x).
Proof. exact (MK_COMB (@lem1351262) (@lem1351261 M' x)). Qed.
Lemma lem1351264 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1351265 (M' : real) (x : real) : (term31 M' x) = (term32 M' x).
Proof. exact (MK_COMB (@lem1351263 M' x) (@lem1351264 x)). Qed.
Lemma lem1351266 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1351267 (M' : real) (x : real) : (term322 M' x) = (term323 M' x).
Proof. exact (MK_COMB (@lem1351266) (@lem1351265 M' x)). Qed.
Lemma lem1351268 (M' : real) : M' = M'.
Proof. exact (eq_refl M'). Qed.
Lemma lem1351269 (x : real) (M' : real) : ((term31 M' x) = M') = ((term32 M' x) = M').
Proof. exact (MK_COMB (@lem1351267 M' x) (@lem1351268 M')). Qed.
Lemma lem1351272 (x : real) (M' : real) : ((term32 M' x) = M') = ((term31 M' x) = M').
Proof. exact (SYM (@lem1351269 x M')). Qed.
Lemma lem1351276 (x : real) (y : real) (z : real) : (term6 x y z) = (term5 x y z).
Proof. exact (EQ_MP (@lem1349736 x y z) (@lem1349735 x y z)). Qed.
Lemma lem1351277 (M' : real) (x : real) : (term32 M' x) = (term33 M' x).
Proof. exact (@lem1351276 M' (real_neg x) x). Qed.
Lemma lem1351279 (x : real) : (term20 x) = term21.
Proof. exact (EQ_MP (@lem1349727 x) (@lem1349726 x)). Qed.
Lemma lem1351280 (M' : real) : (real_add M') = (real_add M').
Proof. exact (eq_refl (real_add M')). Qed.
Lemma lem1351281 (x : real) (M' : real) : (term33 M' x) = (term34 M').
Proof. exact (MK_COMB (@lem1351280 M') (@lem1351279 x)). Qed.
Lemma lem1351282 (x : real) (M' : real) : (term32 M' x) = (term34 M').
Proof. exact (TRANS (@lem1351277 M' x) (@lem1351281 x M')). Qed.
Lemma lem1351283 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1351284 (x : real) (M' : real) : (term323 M' x) = (term36 M').
Proof. exact (MK_COMB (@lem1351283) (@lem1351282 x M')). Qed.
Lemma lem1351285 (M' : real) : M' = M'.
Proof. exact (eq_refl M'). Qed.
Lemma lem1351286 (x : real) (M' : real) : ((term32 M' x) = M') = ((term34 M') = M').
Proof. exact (MK_COMB (@lem1351284 x M') (@lem1351285 M')). Qed.
Lemma lem1351289 (x : real) (M' : real) : ((term34 M') = M') = ((term32 M' x) = M').
Proof. exact (SYM (@lem1351286 x M')). Qed.
Lemma lem1351293 (x : real) : (term34 x) = x.
Proof. exact (EQ_MP (@lem1349706 x) (@lem1349705 x)). Qed.
Lemma lem1351294 (M' : real) : (term34 M') = M'.
Proof. exact (@lem1351293 M'). Qed.
Lemma lem1351295 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1351296 (M' : real) : (term36 M') = (@eq real M').
Proof. exact (MK_COMB (@lem1351295) (@lem1351294 M')). Qed.
Lemma lem1351297 (M' : real) : M' = M'.
Proof. exact (eq_refl M'). Qed.
Lemma lem1351298 (M' : real) : ((term34 M') = M') = (M' = M').
Proof. exact (MK_COMB (@lem1351296 M') (@lem1351297 M')). Qed.
Lemma lem1351300 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1351301 (x : real) : (x = x) = True.
Proof. exact (@lem1351300 real x). Qed.
Lemma lem1351302 (M' : real) : (M' = M') = True.
Proof. exact (@lem1351301 M'). Qed.
Lemma lem1351303 (M' : real) : ((term34 M') = M') = True.
Proof. exact (TRANS (@lem1351298 M') (@lem1351302 M')). Qed.
Lemma lem1351304 (M' : real) : True = ((term34 M') = M').
Proof. exact (SYM (@lem1351303 M')). Qed.
Lemma lem1351305 (M' : real) : (term34 M') = M'.
Proof. exact (EQ_MP (@lem1351304 M') (@lem0)). Qed.
Lemma lem1351306 (x : real) (M' : real) : (term32 M' x) = M'.
Proof. exact (EQ_MP (@lem1351289 x M') (@lem1351305 M')). Qed.
Lemma lem1351307 (x : real) (M' : real) : (term31 M' x) = M'.
Proof. exact (EQ_MP (@lem1351272 x M') (@lem1351306 x M')). Qed.
Lemma lem1351308 (x : real) (M' : real) : (term276 M' x) = M'.
Proof. exact (EQ_MP (@lem1351256 x M') (@lem1351307 x M')). Qed.
Lemma lem1351309 (B : real) (x : real) : (term324 x B) = (term324 B x).
Proof. exact (MK_COMB (@lem1351237) (@lem1351246 B x)). Qed.
Lemma lem1351310 (B : real) (x : real) (M' : real) : (term319 B M' x) = (term220 B x M').
Proof. exact (MK_COMB (@lem1351309 B x) (@lem1351308 x M')). Qed.
Lemma lem1351311 (B : real) (x : real) (M' : real) : term325 B x M'.
Proof. exact (@lem1351236 B x M' (@lem1351310 B x M')). Qed.
Lemma lem1351312 (B : real) (M' : real) (x : real) (h1 : term300 B M' x) : term220 B x M'.
Proof. exact (@lem1351311 B x M' (@lem1351233 B M' x h1)). Qed.
Lemma lem1351313 (B : real) (x : real) (M' : real) : term326 B x M'.
Proof. exact (fun h0 : term300 B M' x => @lem1351312 B M' x h0). Qed.
Lemma lem1351314 (B : real) (M' : real) (x : real) (h1 : term300 B M' x) : term220 B x M'.
Proof. exact (@lem1351313 B x M' (@lem1351033 B M' x h1)). Qed.
Lemma lem1351315 (x : real) (B : real) (P : real -> Prop) (M' : real) (h1 : term202 P x B) (h2 : term133 P M') : (term300 B M' x) = (term220 B x M').
Proof. exact (prop_ext (fun h3 : term300 B M' x => @lem1351314 B M' x h3) (fun h3 : term220 B x M' => @lem1351225 x B P M' h1 h2)). Qed.
Lemma lem1351316 (x : real) (B : real) (P : real -> Prop) (M' : real) (h1 : term202 P x B) (h2 : term133 P M') : term220 B x M'.
Proof. exact (EQ_MP (@lem1351315 x B P M' h1 h2) (@lem1351225 x B P M' h1 h2)). Qed.
Lemma lem1351317 (x : real) (B : real) (P : real -> Prop) (M' : real) (h1 : term202 P x B) (h2 : term133 P M') : (term133 P M') = (term220 B x M').
Proof. exact (prop_ext (fun h3 : term133 P M' => @lem1351316 x B P M' h1 h2) (fun h3 : term220 B x M' => @lem1351032 P M' h2)). Qed.
Lemma lem1351318 (x : real) (B : real) (P : real -> Prop) (M' : real) (h1 : term202 P x B) (h2 : term133 P M') : term220 B x M'.
Proof. exact (EQ_MP (@lem1351317 x B P M' h1 h2) (@lem1351032 P M' h2)). Qed.
Lemma lem1351319 (M' : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term327 P B x M'.
Proof. exact (fun h0 : term133 P M' => @lem1351318 x B P M' h1 h0). Qed.
Lemma lem1351324 (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) : term328 P B x.
Proof. exact (fun M' : real => @lem1351319 M' P x B h1). Qed.
Lemma lem1351325 (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) (h2 : term133 P M) (h3 : term184 P x B) : term329 P B x.
Proof. exact (conj (@lem1351031 M P x B h2 h3) (@lem1351324 P x B h1)). Qed.
Lemma lem1351326 (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) (h2 : term133 P M) (h3 : term184 P x B) : term121 P.
Proof. exact (ex_intro (term330 P) (real_add B x) (@lem1351325 M P x B h1 h2 h3)). Qed.
Lemma lem1351327 (P : real -> Prop) (x : real) (B : real) (h1 : term204 P x B) : term202 P x B.
Proof. exact (proj2 (@lem1350818 P x B h1)). Qed.
Lemma lem1351328 (P : real -> Prop) (x : real) (B : real) (h1 : term204 P x B) : term184 P x B.
Proof. exact (proj1 (@lem1350818 P x B h1)). Qed.
Lemma lem1351329 (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) (h2 : term133 P M) (h3 : term184 P x B) : (term202 P x B) = (term121 P).
Proof. exact (prop_ext (fun h4 : term202 P x B => @lem1351326 M P x B h1 h2 h3) (fun h4 : term121 P => @lem1350819 P x B h1)). Qed.
Lemma lem1351330 (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) (h2 : term133 P M) (h3 : term184 P x B) : term121 P.
Proof. exact (EQ_MP (@lem1351329 M P x B h1 h2 h3) (@lem1350819 P x B h1)). Qed.
Lemma lem1351331 (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) (h2 : term133 P M) (h3 : term184 P x B) : (term184 P x B) = (term121 P).
Proof. exact (prop_ext (fun h4 : term184 P x B => @lem1351330 M P x B h1 h2 h3) (fun h4 : term121 P => @lem1350820 P x B h3)). Qed.
Lemma lem1351332 (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term202 P x B) (h2 : term133 P M) (h3 : term184 P x B) : term121 P.
Proof. exact (EQ_MP (@lem1351331 M P x B h1 h2 h3) (@lem1350820 P x B h3)). Qed.
Lemma lem1351333 (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term133 P M) (h2 : term184 P x B) (h3 : term204 P x B) : (term202 P x B) = (term121 P).
Proof. exact (prop_ext (fun h4 : term202 P x B => @lem1351332 M P x B h4 h1 h2) (fun h4 : term121 P => @lem1351327 P x B h3)). Qed.
Lemma lem1351334 (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term133 P M) (h2 : term184 P x B) (h3 : term204 P x B) : term121 P.
Proof. exact (EQ_MP (@lem1351333 M P x B h1 h2 h3) (@lem1351327 P x B h3)). Qed.
Lemma lem1351335 (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term133 P M) (h2 : term204 P x B) : (term184 P x B) = (term121 P).
Proof. exact (prop_ext (fun h3 : term184 P x B => @lem1351334 M P x B h1 h3 h2) (fun h3 : term121 P => @lem1351328 P x B h2)). Qed.
Lemma lem1351336 (M : real) (P : real -> Prop) (x : real) (B : real) (h1 : term133 P M) (h2 : term204 P x B) : term121 P.
Proof. exact (EQ_MP (@lem1351335 M P x B h1 h2) (@lem1351328 P x B h2)). Qed.
Lemma lem1351337 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : term208 P x) : term121 P.
Proof. exact (ex_elim (@lem1350817 P x h2) (fun B : real => fun h0 : term206 P x B => @lem1351336 M P x B h1 h0)). Qed.
Lemma lem1351338 (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term331 x P.
Proof. exact (fun h0 : term208 P x => @lem1351337 M P x h1 h0). Qed.
Lemma lem1351339 (x : real) (P : real -> Prop) (M : real) (h1 : term133 P M) : term332 x P.
Proof. exact (@lem1350816 x P (@lem1351338 x P M h1)). Qed.
Lemma lem1351340 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : term190 P x) : term213 x P.
Proof. exact (@lem1351339 x P M h1 (@lem1350674 P x h2)). Qed.
Lemma lem1351341 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : (term190 P x) = (term213 x P).
Proof. exact (prop_ext (fun h3 : term190 P x => @lem1351340 M P x h1 h3) (fun h3 : term213 x P => @lem1350813 M P x h1 h2)). Qed.
Lemma lem1351342 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : term213 x P.
Proof. exact (EQ_MP (@lem1351341 M P x h1 h2) (@lem1350813 M P x h1 h2)). Qed.
Lemma lem1351343 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : term212 x P.
Proof. exact (EQ_MP (@lem1350673 x P) (@lem1351342 M P x h1 h2)). Qed.
Lemma lem1351344 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : term121 P.
Proof. exact (@lem1351343 M P x h1 h2 (@lem1350370 P x)). Qed.
Lemma lem1351345 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : term164 x P.
Proof. exact (fun h0 : term162 x => @lem1351344 M P x h1 h2). Qed.
Lemma lem1351346 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : term161 x P.
Proof. exact (EQ_MP (@lem1350613 x P) (@lem1351345 M P x h1 h2)). Qed.
Lemma lem1351347 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : term157 x P.
Proof. exact (EQ_MP (@lem1350575 x P) (@lem1351346 M P x h1 h2)). Qed.
Lemma lem1351348 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : term156 x P.
Proof. exact (EQ_MP (@lem1350539 x P) (@lem1351347 M P x h1 h2)). Qed.
Lemma lem1351349 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : term147 x) (h3 : P x) : term121 P.
Proof. exact (@lem1351348 M P x h1 h3 (@lem1350498 x h2)). Qed.
Lemma lem1351350 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : term333 x P.
Proof. exact (fun h0 : term147 x => @lem1351349 M P x h1 h0 h2). Qed.
Lemma lem1351351 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) (h3 : term129 x) : term121 P.
Proof. exact (@lem1351350 M P x h1 h2 (@lem1350494 x h3)). Qed.
Lemma lem1351352 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : term121 P.
Proof. exact (or_elim (@lem1350428 x) (fun h0 : term128 x => @lem1350490 M P x h1 h2 h0) (fun h0 : term129 x => @lem1351351 M P x h1 h2 h0)). Qed.
Lemma lem1351353 (P : real -> Prop) (h1 : term130 P) : term131 P.
Proof. exact (proj2 (@lem1350431 P h1)). Qed.
Lemma lem1351354 (P : real -> Prop) (h1 : term130 P) : term132 P.
Proof. exact (proj1 (@lem1350431 P h1)). Qed.
Lemma lem1351355 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : (term133 P M) = (term121 P).
Proof. exact (prop_ext (fun h3 : term133 P M => @lem1351352 M P x h1 h2) (fun h3 : term121 P => @lem1350435 P M h1)). Qed.
Lemma lem1351356 (M : real) (P : real -> Prop) (x : real) (h1 : term133 P M) (h2 : P x) : term121 P.
Proof. exact (EQ_MP (@lem1351355 M P x h1 h2) (@lem1350435 P M h1)). Qed.
Lemma lem1351357 (P : real -> Prop) (x : real) (h1 : term131 P) (h2 : P x) : term121 P.
Proof. exact (ex_elim (@lem1350432 P h1) (fun M : real => fun h0 : term143 P M => @lem1351356 M P x h0 h2)). Qed.
Lemma lem1351358 (P : real -> Prop) (x : real) (h1 : term131 P) (h2 : P x) : (P x) = (term121 P).
Proof. exact (prop_ext (fun h3 : P x => @lem1351357 P x h1 h2) (fun h3 : term121 P => @lem1350434 P x h2)). Qed.
Lemma lem1351359 (P : real -> Prop) (x : real) (h1 : term131 P) (h2 : P x) : term121 P.
Proof. exact (EQ_MP (@lem1351358 P x h1 h2) (@lem1350434 P x h2)). Qed.
Lemma lem1351360 (P : real -> Prop) (h1 : term131 P) (h2 : term132 P) : term121 P.
Proof. exact (ex_elim (@lem1350433 P h2) (fun x : real => fun h0 : term334 P x => @lem1351359 P x h1 h0)). Qed.
Lemma lem1351361 (P : real -> Prop) (h1 : term132 P) (h2 : term130 P) : (term131 P) = (term121 P).
Proof. exact (prop_ext (fun h3 : term131 P => @lem1351360 P h3 h1) (fun h3 : term121 P => @lem1351353 P h2)). Qed.
Lemma lem1351362 (P : real -> Prop) (h1 : term132 P) (h2 : term130 P) : term121 P.
Proof. exact (EQ_MP (@lem1351361 P h1 h2) (@lem1351353 P h2)). Qed.
Lemma lem1351363 (P : real -> Prop) (h1 : term130 P) : (term132 P) = (term121 P).
Proof. exact (prop_ext (fun h2 : term132 P => @lem1351362 P h2 h1) (fun h2 : term121 P => @lem1351354 P h1)). Qed.
Lemma lem1351364 (P : real -> Prop) (h1 : term130 P) : term121 P.
Proof. exact (EQ_MP (@lem1351363 P h1) (@lem1351354 P h1)). Qed.
Lemma lem1351365 (P : real -> Prop) : term335 P.
Proof. exact (fun h0 : term130 P => @lem1351364 P h0). Qed.
Lemma lem1351370 : term336.
Proof. exact (fun P : real -> Prop => @lem1351365 P). Qed.
