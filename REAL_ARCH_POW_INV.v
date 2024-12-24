Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ARCH_POW_INV_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import MONO_EXISTS_spec.
Require Import REAL_ARCH_POW_spec.
Require Import REAL_INV_INV_spec.
Require Import REAL_LET_TRANS_spec.
Require Import REAL_LT_INV_spec.
Require Import REAL_LT_INV2_spec.
Require Import REAL_NOT_LT_spec.
Require Import REAL_POW_1_spec.
Require Import REAL_POW_INV_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1592014_spec.
Require Import thm1592030_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17784_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem1707684 (x : real) (n : nat) (h1 : (term0 x n) = (term1 x n)) : (term0 x n) = (term1 x n).
Proof. exact (h1). Qed.
Lemma lem1707685 (x : real) (n : nat) (h1 : (term0 x n) = (term1 x n)) : (term1 x n) = (term0 x n).
Proof. exact (SYM (@lem1707684 x n h1)). Qed.
Lemma lem1707686 (x : real) (n : nat) (h1 : (term1 x n) = (term0 x n)) : (term1 x n) = (term0 x n).
Proof. exact (h1). Qed.
Lemma lem1707687 (x : real) (n : nat) (h1 : (term1 x n) = (term0 x n)) : (term0 x n) = (term1 x n).
Proof. exact (SYM (@lem1707686 x n h1)). Qed.
Lemma lem1707688 (x : real) (n : nat) : ((term0 x n) = (term1 x n)) = ((term1 x n) = (term0 x n)).
Proof. exact (prop_ext (fun h1 : (term0 x n) = (term1 x n) => @lem1707685 x n h1) (fun h1 : (term1 x n) = (term0 x n) => @lem1707687 x n h1)). Qed.
Lemma lem1707689 (x : real) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun n : nat => @lem1707688 x n)). Qed.
Lemma lem1707690 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1707691 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem1707690) (@lem1707689 x)). Qed.
Lemma lem1707692 : term6 = term7.
Proof. exact (fun_ext (fun x : real => @lem1707691 x)). Qed.
Lemma lem1707693 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707694 : term8 = term9.
Proof. exact (MK_COMB (@lem1707693) (@lem1707692)). Qed.
Lemma lem1707695 : term9.
Proof. exact (EQ_MP (@lem1707694) (@lem1595679)). Qed.
Lemma lem1707697 (x : real) (h1 : (term10 x) = x) : (term10 x) = x.
Proof. exact (h1). Qed.
Lemma lem1707698 (x : real) (h1 : (term10 x) = x) : x = (term10 x).
Proof. exact (SYM (@lem1707697 x h1)). Qed.
Lemma lem1707699 (x : real) (h1 : x = (term10 x)) : x = (term10 x).
Proof. exact (h1). Qed.
Lemma lem1707700 (x : real) (h1 : x = (term10 x)) : (term10 x) = x.
Proof. exact (SYM (@lem1707699 x h1)). Qed.
Lemma lem1707701 (x : real) : ((term10 x) = x) = (x = (term10 x)).
Proof. exact (prop_ext (fun h1 : (term10 x) = x => @lem1707698 x h1) (fun h1 : x = (term10 x) => @lem1707700 x h1)). Qed.
Lemma lem1707702 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem1707701 x)). Qed.
Lemma lem1707703 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707704 : term13 = term14.
Proof. exact (MK_COMB (@lem1707703) (@lem1707702)). Qed.
Lemma lem1707705 : term14.
Proof. exact (EQ_MP (@lem1707704) (@lem1587920)). Qed.
Lemma lem1707706 (x : real) : term15 x.
Proof. exact (@lem1707705 x). Qed.
Lemma lem1707707 (x : real) : (term15 x) = (x = (term10 x)).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1707709 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term16 A P Q) : term16 A P Q.
Proof. exact (h1). Qed.
Lemma lem1707710 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term17 A P Q) : term17 A P Q.
Proof. exact (h1). Qed.
Lemma lem1707711 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term17 A P Q) (h2 : term16 A P Q) : term18 A P Q.
Proof. exact (@lem1707709 A P Q h2 (@lem1707710 A P Q h1)). Qed.
Lemma lem1707712 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term17 A P Q) : term19 A P Q.
Proof. exact (fun h0 : term16 A P Q => @lem1707711 A P Q h1 h0). Qed.
Lemma lem1707713 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term16 A P Q) : term16 A P Q.
Proof. exact (h1). Qed.
Lemma lem1707714 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term17 A P Q) (h2 : term16 A P Q) : term18 A P Q.
Proof. exact (@lem1707712 A P Q h1 (@lem1707713 A P Q h2)). Qed.
Lemma lem1707715 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term16 A P Q) : term16 A P Q.
Proof. exact (fun h0 : term17 A P Q => @lem1707714 A P Q h0 h1). Qed.
Lemma lem1707716 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term20 A P Q.
Proof. exact (fun h0 : term16 A P Q => @lem1707715 A P Q h0). Qed.
Lemma lem1707718 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem1707719 (x : real) (h1 : term21) : term22 x.
Proof. exact (@lem1707718 h1 x). Qed.
Lemma lem1707720 (x : real) : (term22 x) = (term23 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1707721 (x : real) (h1 : term21) : term23 x.
Proof. exact (EQ_MP (@lem1707720 x) (@lem1707719 x h1)). Qed.
Lemma lem1707722 (x : real) (y : real) (h1 : term21) : term24 x y.
Proof. exact (@lem1707721 x h1 y). Qed.
Lemma lem1707723 (y : real) (x : real) : (term24 x y) = (term25 y x).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1707724 (y : real) (x : real) (h1 : term21) : term25 y x.
Proof. exact (EQ_MP (@lem1707723 y x) (@lem1707722 x y h1)). Qed.
Lemma lem1707725 (x : real) (h1 : term26 x) : term26 x.
Proof. exact (h1). Qed.
Lemma lem1707726 (y : real) (x : real) (h1 : term21) (h2 : term26 x) : term27 y x.
Proof. exact (@lem1707724 y x h1 (@lem1707725 x h2)). Qed.
Lemma lem1707727 (x : real) (h1 : term21) (h2 : term26 x) : term28 x.
Proof. exact (fun y : real => @lem1707726 y x h1 h2). Qed.
Lemma lem1707728 (x : real) (h1 : term21) : term29 x.
Proof. exact (fun h0 : term26 x => @lem1707727 x h1 h0). Qed.
Lemma lem1707729 (h1 : term21) : term30.
Proof. exact (fun x : real => @lem1707728 x h1). Qed.
Lemma lem1707730 : term31.
Proof. exact (fun h0 : term21 => @lem1707729 h0). Qed.
Lemma lem1707731 : term30.
Proof. exact (@lem1707730 (@lem1706981)). Qed.
Lemma lem1707732 (x : real) : term32 x.
Proof. exact (@lem1707731 x). Qed.
Lemma lem1707733 (x : real) : (term32 x) = (term29 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1707735 (t1 : Prop) : term33 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1707736 (t1 : Prop) : (term33 t1) = (term34 t1).
Proof. exact (eq_refl (term33 t1)). Qed.
Lemma lem1707737 (t1 : Prop) : term34 t1.
Proof. exact (EQ_MP (@lem1707736 t1) (@lem1707735 t1)). Qed.
Lemma lem1707738 (t1 : Prop) (t2 : Prop) : term35 t1 t2.
Proof. exact (@lem1707737 t1 t2). Qed.
Lemma lem1707739 (t1 : Prop) (t2 : Prop) : (term35 t1 t2) = (term36 t1 t2).
Proof. exact (eq_refl (term35 t1 t2)). Qed.
Lemma lem1707740 (t1 : Prop) (t2 : Prop) : term36 t1 t2.
Proof. exact (EQ_MP (@lem1707739 t1 t2) (@lem1707738 t1 t2)). Qed.
Lemma lem1707741 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term37 t1 t2 t3.
Proof. exact (@lem1707740 t1 t2 t3). Qed.
Lemma lem1707742 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term37 t1 t2 t3) = ((term38 t1 t2 t3) = (term39 t1 t2 t3)).
Proof. exact (eq_refl (term37 t1 t2 t3)). Qed.
Lemma lem1707743 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term38 t1 t2 t3) = (term39 t1 t2 t3).
Proof. exact (EQ_MP (@lem1707742 t1 t2 t3) (@lem1707741 t1 t2 t3)). Qed.
Lemma lem1707744 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term39 t1 t2 t3) = (term38 t1 t2 t3).
Proof. exact (SYM (@lem1707743 t1 t2 t3)). Qed.
Lemma lem1707745 (x : real) : term40 x.
Proof. exact (@lem9784 (term41 x)). Qed.
Lemma lem1707746 (x : real) : (term40 x) = (term42 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1707747 (x : real) : term42 x.
Proof. exact (EQ_MP (@lem1707746 x) (@lem1707745 x)). Qed.
Lemma lem1707748 (x : real) (h1 : term41 x) : term41 x.
Proof. exact (h1). Qed.
Lemma lem1707749 (x : real) (h1 : term43 x) : term43 x.
Proof. exact (h1). Qed.
Lemma lem1707750 (y : real) (x : real) (h1 : term44 y x) : term44 y x.
Proof. exact (h1). Qed.
Lemma lem1707751 (x : real) (h1 : term45 x) : term45 x.
Proof. exact (h1). Qed.
Lemma lem1707752 (y : real) (h1 : term41 y) : term41 y.
Proof. exact (h1). Qed.
Lemma lem1707754 (p : Prop) : p = (term46 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1707755 (x : real) (y : real) : (term47 x y) = (term48 x y).
Proof. exact (@lem1707754 (term47 x y)). Qed.
Lemma lem1707756 (x : real) (y : real) : (term48 x y) = (term47 x y).
Proof. exact (SYM (@lem1707755 x y)). Qed.
Lemma lem1707757 (x : real) (y : real) (h1 : term49 x y) : term49 x y.
Proof. exact (h1). Qed.
Lemma lem1707760 (x : real) (y : real) (h1 : term50 x y) : term50 x y.
Proof. exact (h1). Qed.
Lemma lem1707761 (x : real) (y : real) : term51 x y.
Proof. exact (fun h0 : term50 x y => @lem1707760 x y h0). Qed.
Lemma lem1707762 (x : real) (y : real) (h1 : term51 x y) : term51 x y.
Proof. exact (h1). Qed.
Lemma lem1707763 (x : real) (y : real) (h1 : term50 x y) : term50 x y.
Proof. exact (h1). Qed.
Lemma lem1707764 (x : real) (y : real) (h1 : term51 x y) (h2 : term50 x y) : term50 x y.
Proof. exact (@lem1707762 x y h1 (@lem1707763 x y h2)). Qed.
Lemma lem1707765 (x : real) (y : real) (h1 : term50 x y) : term52 x y.
Proof. exact (fun h0 : term51 x y => @lem1707764 x y h0 h1). Qed.
Lemma lem1707766 (x : real) (y : real) (h1 : term51 x y) : term51 x y.
Proof. exact (h1). Qed.
Lemma lem1707767 (x : real) (y : real) (h1 : term51 x y) (h2 : term50 x y) : term50 x y.
Proof. exact (@lem1707765 x y h2 (@lem1707766 x y h1)). Qed.
Lemma lem1707768 (x : real) (y : real) (h1 : term51 x y) : term51 x y.
Proof. exact (fun h0 : term50 x y => @lem1707767 x y h1 h0). Qed.
Lemma lem1707769 (x : real) (y : real) : term53 x y.
Proof. exact (fun h0 : term51 x y => @lem1707768 x y h0). Qed.
Lemma lem1707772 (x : real) (y : real) : term51 x y.
Proof. exact (@lem1707769 x y (@lem1707761 x y)). Qed.
Lemma lem1707822 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1707823 : term54 = term55.
Proof. exact (@lem1707822 term56). Qed.
Lemma lem1707828 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem1707829 : term58 = term59.
Proof. exact (MK_COMB (@lem1707828) (@lem1707823)). Qed.
Lemma lem1707832 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1707833 : term61 = term62.
Proof. exact (MK_COMB (@lem1707832) (@lem1707829)). Qed.
Lemma lem1707836 (x : real) (y : real) : (term63 x y) = (term63 x y).
Proof. exact (eq_refl (term63 x y)). Qed.
Lemma lem1707837 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1707836 x y) (@lem1707833)). Qed.
Lemma lem1707840 (x : real) : (term66 x) = (term66 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1707841 (x : real) (y : real) : (term67 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1707840 x) (@lem1707837 x y)). Qed.
Lemma lem1707844 (x : real) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem1707845 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1707844 x) (@lem1707841 x y)). Qed.
Lemma lem1707848 (y : real) : (term72 y) = (term72 y).
Proof. exact (eq_refl (term72 y)). Qed.
Lemma lem1707849 (x : real) (y : real) : (term50 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem1707848 y) (@lem1707845 x y)). Qed.
Lemma lem1707852 (y : real) : (term74 y) = (term75 y).
Proof. exact (fun_ext (fun x : real => @lem1707849 x y)). Qed.
Lemma lem1707853 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707854 (y : real) : (term76 y) = (term77 y).
Proof. exact (MK_COMB (@lem1707853) (@lem1707852 y)). Qed.
Lemma lem1707859 : term78 = term79.
Proof. exact (fun_ext (fun y : real => @lem1707854 y)). Qed.
Lemma lem1707860 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707869 : term80 = term81.
Proof. exact (MK_COMB (@lem1707860) (@lem1707859)). Qed.
Lemma lem1707870 (x : real) : ((term82 x) = x) = ((term82 x) = x).
Proof. exact (eq_refl ((term82 x) = x)). Qed.
Lemma lem1707871 : term83 = term83.
Proof. exact (fun_ext (fun x : real => @lem1707870 x)). Qed.
Lemma lem1707872 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707873 : term56 = term56.
Proof. exact (MK_COMB (@lem1707872) (@lem1707871)). Qed.
Lemma lem1707874 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1707875 : term55 = term55.
Proof. exact (MK_COMB (@lem1707874) (@lem1707873)). Qed.
Lemma lem1707884 (y : real) (x : real) (z : real) : (term84 y x z) = (term84 y x z).
Proof. exact (eq_refl (term84 y x z)). Qed.
Lemma lem1707885 (y : real) (x : real) : (term85 y x) = (term85 y x).
Proof. exact (fun_ext (fun z : real => @lem1707884 y x z)). Qed.
Lemma lem1707886 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707887 (y : real) (x : real) : (term86 y x) = (term86 y x).
Proof. exact (MK_COMB (@lem1707886) (@lem1707885 y x)). Qed.
Lemma lem1707888 (x : real) : (term87 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem1707887 y x)). Qed.
Lemma lem1707889 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707890 (x : real) : (term88 x) = (term88 x).
Proof. exact (MK_COMB (@lem1707889) (@lem1707888 x)). Qed.
Lemma lem1707891 : term89 = term89.
Proof. exact (fun_ext (fun x : real => @lem1707890 x)). Qed.
Lemma lem1707892 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707893 : term90 = term90.
Proof. exact (MK_COMB (@lem1707892) (@lem1707891)). Qed.
Lemma lem1707894 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1707895 : term57 = term57.
Proof. exact (MK_COMB (@lem1707894) (@lem1707893)). Qed.
Lemma lem1707896 : term59 = term59.
Proof. exact (MK_COMB (@lem1707895) (@lem1707875)). Qed.
Lemma lem1707903 (y : real) (x : real) : ((term91 x y) = (real_le y x)) = ((term91 x y) = (real_le y x)).
Proof. exact (eq_refl ((term91 x y) = (real_le y x))). Qed.
Lemma lem1707904 (x : real) : (term92 x) = (term92 x).
Proof. exact (fun_ext (fun y : real => @lem1707903 y x)). Qed.
Lemma lem1707905 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707906 (x : real) : (term93 x) = (term93 x).
Proof. exact (MK_COMB (@lem1707905) (@lem1707904 x)). Qed.
Lemma lem1707907 : term94 = term94.
Proof. exact (fun_ext (fun x : real => @lem1707906 x)). Qed.
Lemma lem1707908 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707909 : term95 = term95.
Proof. exact (MK_COMB (@lem1707908) (@lem1707907)). Qed.
Lemma lem1707910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1707911 : term60 = term60.
Proof. exact (MK_COMB (@lem1707910) (@lem1707909)). Qed.
Lemma lem1707912 : term62 = term62.
Proof. exact (MK_COMB (@lem1707911) (@lem1707896)). Qed.
Lemma lem1707913 (x : real) (n : nat) (y : real) : (term96 x n y) = (term96 x n y).
Proof. exact (eq_refl (term96 x n y)). Qed.
Lemma lem1707914 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (fun_ext (fun n : nat => @lem1707913 x n y)). Qed.
Lemma lem1707915 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1707916 (x : real) (y : real) : (term47 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1707915) (@lem1707914 x y)). Qed.
Lemma lem1707917 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1707918 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1707917) (@lem1707916 x y)). Qed.
Lemma lem1707919 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1707920 (x : real) (y : real) : (term63 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1707919) (@lem1707918 x y)). Qed.
Lemma lem1707921 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1707920 x y) (@lem1707912)). Qed.
Lemma lem1707926 (x : real) : (term66 x) = (term66 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1707927 (x : real) (y : real) : (term68 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1707926 x) (@lem1707921 x y)). Qed.
Lemma lem1707930 (x : real) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem1707931 (x : real) (y : real) : (term71 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1707930 x) (@lem1707927 x y)). Qed.
Lemma lem1707934 (y : real) : (term72 y) = (term72 y).
Proof. exact (eq_refl (term72 y)). Qed.
Lemma lem1707935 (x : real) (y : real) : (term73 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem1707934 y) (@lem1707931 x y)). Qed.
Lemma lem1707936 (y : real) : (term75 y) = (term75 y).
Proof. exact (fun_ext (fun x : real => @lem1707935 x y)). Qed.
Lemma lem1707937 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707938 (y : real) : (term77 y) = (term77 y).
Proof. exact (MK_COMB (@lem1707937) (@lem1707936 y)). Qed.
Lemma lem1707939 : term79 = term79.
Proof. exact (fun_ext (fun y : real => @lem1707938 y)). Qed.
Lemma lem1707940 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707941 : term81 = term81.
Proof. exact (MK_COMB (@lem1707940) (@lem1707939)). Qed.
Lemma lem1708014 : term80 = term81.
Proof. exact (TRANS (@lem1707869) (@lem1707941)). Qed.
Lemma lem1708015 : term81 = term80.
Proof. exact (SYM (@lem1708014)). Qed.
Lemma lem1708019 (x : real) (y : real) (h1 : term49 x y) : term49 x y.
Proof. exact (h1). Qed.
Lemma lem1708020 (h1 : term95) : term95.
Proof. exact (h1). Qed.
Lemma lem1708021 (h1 : term90) : term90.
Proof. exact (h1). Qed.
Lemma lem1708022 (h1 : term56) : term56.
Proof. exact (h1). Qed.
Lemma lem1708028 (y : real) (h1 : term41 y) : term41 y.
Proof. exact (h1). Qed.
Lemma lem1708040 (x : real) (h1 : term43 x) : term43 x.
Proof. exact (h1). Qed.
Lemma lem1708042 (P : nat -> Prop) : (term98 P) = (term99 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1708043 (x : real) (y : real) : (term49 x y) = (term100 x y).
Proof. exact (@lem1708042 (term97 x y)). Qed.
Lemma lem1708044 (x : real) (n : nat) (y : real) : (term101 x y n) = (term96 x n y).
Proof. exact (eq_refl (term101 x y n)). Qed.
Lemma lem1708045 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1708047 (x : real) (n : nat) (y : real) : (term102 x y n) = (term103 x n y).
Proof. exact (MK_COMB (@lem1708045) (@lem1708044 x n y)). Qed.
Lemma lem1708048 (x : real) (y : real) : (term104 x y) = (term105 x y).
Proof. exact (fun_ext (fun n : nat => @lem1708047 x n y)). Qed.
Lemma lem1708049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1708050 (x : real) (y : real) : (term100 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1708049) (@lem1708048 x y)). Qed.
Lemma lem1708059 (x : real) (y : real) : (term49 x y) = (term106 x y).
Proof. exact (TRANS (@lem1708043 x y) (@lem1708050 x y)). Qed.
Lemma lem1708060 (x : real) (y : real) (h1 : term49 x y) : term106 x y.
Proof. exact (EQ_MP (@lem1708059 x y) (@lem1708019 x y h1)). Qed.
Lemma lem1708064 (x : real) (y : real) : (term107 x y) = (real_lt x y).
Proof. exact (@lem16933 (real_lt x y)). Qed.
Lemma lem1708066 (y : real) (x : real) : (real_le y x) = (real_le y x).
Proof. exact (eq_refl (real_le y x)). Qed.
Lemma lem1708067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1708068 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1708067) (@lem1708064 x y)). Qed.
Lemma lem1708069 (y : real) (x : real) : (term110 y x) = (term111 y x).
Proof. exact (MK_COMB (@lem1708068 x y) (@lem1708066 y x)). Qed.
Lemma lem1708074 (y : real) (x : real) : (term112 y x) = (term112 y x).
Proof. exact (eq_refl (term112 y x)). Qed.
Lemma lem1708075 (y : real) (x : real) : (term113 y x) = (term114 y x).
Proof. exact (MK_COMB (@lem1708074 y x) (@lem1708069 y x)). Qed.
Lemma lem1708076 (y : real) (x : real) : ((term91 x y) = (real_le y x)) = (term113 y x).
Proof. exact (@lem17784 (term91 x y) (real_le y x)). Qed.
Lemma lem1708077 (y : real) (x : real) : ((term91 x y) = (real_le y x)) = (term114 y x).
Proof. exact (TRANS (@lem1708076 y x) (@lem1708075 y x)). Qed.
Lemma lem1708078 (x : real) : (term92 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1708077 y x)). Qed.
Lemma lem1708079 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708080 (x : real) : (term93 x) = (term116 x).
Proof. exact (MK_COMB (@lem1708079) (@lem1708078 x)). Qed.
Lemma lem1708081 : term94 = term117.
Proof. exact (fun_ext (fun x : real => @lem1708080 x)). Qed.
Lemma lem1708082 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708083 : term95 = term118.
Proof. exact (MK_COMB (@lem1708082) (@lem1708081)). Qed.
Lemma lem1708089 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1708090 (P : real -> Prop) (Q : real -> Prop) : (term121 P Q) = (term122 P Q).
Proof. exact (@lem1708089 real P Q). Qed.
Lemma lem1708091 (x : real) : (term123 x) = (term124 x).
Proof. exact (@lem1708090 (term125 x) (term126 x)). Qed.
Lemma lem1708092 (y : real) (x : real) : (term127 x y) = (term128 y x).
Proof. exact (eq_refl (term127 x y)). Qed.
Lemma lem1708093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1708094 (y : real) (x : real) : (term129 x y) = (term112 y x).
Proof. exact (MK_COMB (@lem1708093) (@lem1708092 y x)). Qed.
Lemma lem1708095 (y : real) (x : real) : (term130 x y) = (term111 y x).
Proof. exact (eq_refl (term130 x y)). Qed.
Lemma lem1708096 (y : real) (x : real) : (term131 x y) = (term114 y x).
Proof. exact (MK_COMB (@lem1708094 y x) (@lem1708095 y x)). Qed.
Lemma lem1708097 (x : real) : (term132 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1708096 y x)). Qed.
Lemma lem1708098 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708099 (x : real) : (term123 x) = (term116 x).
Proof. exact (MK_COMB (@lem1708098) (@lem1708097 x)). Qed.
Lemma lem1708100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1708101 (x : real) : (term133 x) = (term134 x).
Proof. exact (MK_COMB (@lem1708100) (@lem1708099 x)). Qed.
Lemma lem1708102 (y : real) (x : real) : (term127 x y) = (term128 y x).
Proof. exact (eq_refl (term127 x y)). Qed.
Lemma lem1708103 (x : real) : (term135 x) = (term125 x).
Proof. exact (fun_ext (fun y : real => @lem1708102 y x)). Qed.
Lemma lem1708104 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708105 (x : real) : (term136 x) = (term137 x).
Proof. exact (MK_COMB (@lem1708104) (@lem1708103 x)). Qed.
Lemma lem1708106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1708107 (x : real) : (term138 x) = (term139 x).
Proof. exact (MK_COMB (@lem1708106) (@lem1708105 x)). Qed.
Lemma lem1708108 (y : real) (x : real) : (term130 x y) = (term111 y x).
Proof. exact (eq_refl (term130 x y)). Qed.
Lemma lem1708109 (x : real) : (term140 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1708108 y x)). Qed.
Lemma lem1708110 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708111 (x : real) : (term141 x) = (term142 x).
Proof. exact (MK_COMB (@lem1708110) (@lem1708109 x)). Qed.
Lemma lem1708112 (x : real) : (term124 x) = (term143 x).
Proof. exact (MK_COMB (@lem1708107 x) (@lem1708111 x)). Qed.
Lemma lem1708113 (x : real) : ((term123 x) = (term124 x)) = ((term116 x) = (term143 x)).
Proof. exact (MK_COMB (@lem1708101 x) (@lem1708112 x)). Qed.
Lemma lem1708114 (x : real) : (term116 x) = (term143 x).
Proof. exact (EQ_MP (@lem1708113 x) (@lem1708091 x)). Qed.
Lemma lem1708211 : term117 = term144.
Proof. exact (fun_ext (fun x : real => @lem1708114 x)). Qed.
Lemma lem1708212 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708213 : term118 = term145.
Proof. exact (MK_COMB (@lem1708212) (@lem1708211)). Qed.
Lemma lem1708215 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1708216 (P : real -> Prop) (Q : real -> Prop) : (term121 P Q) = (term122 P Q).
Proof. exact (@lem1708215 real P Q). Qed.
Lemma lem1708217 : term146 = term147.
Proof. exact (@lem1708216 term148 term149). Qed.
Lemma lem1708218 (x : real) : (term150 x) = (term137 x).
Proof. exact (eq_refl (term150 x)). Qed.
Lemma lem1708219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1708220 (x : real) : (term151 x) = (term139 x).
Proof. exact (MK_COMB (@lem1708219) (@lem1708218 x)). Qed.
Lemma lem1708221 (x : real) : (term152 x) = (term142 x).
Proof. exact (eq_refl (term152 x)). Qed.
Lemma lem1708222 (x : real) : (term153 x) = (term143 x).
Proof. exact (MK_COMB (@lem1708220 x) (@lem1708221 x)). Qed.
Lemma lem1708223 : term154 = term144.
Proof. exact (fun_ext (fun x : real => @lem1708222 x)). Qed.
Lemma lem1708224 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708225 : term146 = term145.
Proof. exact (MK_COMB (@lem1708224) (@lem1708223)). Qed.
Lemma lem1708226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1708227 : term155 = term156.
Proof. exact (MK_COMB (@lem1708226) (@lem1708225)). Qed.
Lemma lem1708228 (x : real) : (term150 x) = (term137 x).
Proof. exact (eq_refl (term150 x)). Qed.
Lemma lem1708229 : term157 = term148.
Proof. exact (fun_ext (fun x : real => @lem1708228 x)). Qed.
Lemma lem1708230 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708231 : term158 = term159.
Proof. exact (MK_COMB (@lem1708230) (@lem1708229)). Qed.
Lemma lem1708232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1708233 : term160 = term161.
Proof. exact (MK_COMB (@lem1708232) (@lem1708231)). Qed.
Lemma lem1708234 (x : real) : (term152 x) = (term142 x).
Proof. exact (eq_refl (term152 x)). Qed.
Lemma lem1708235 : term162 = term149.
Proof. exact (fun_ext (fun x : real => @lem1708234 x)). Qed.
Lemma lem1708236 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708237 : term163 = term164.
Proof. exact (MK_COMB (@lem1708236) (@lem1708235)). Qed.
Lemma lem1708238 : term147 = term165.
Proof. exact (MK_COMB (@lem1708233) (@lem1708237)). Qed.
Lemma lem1708239 : (term146 = term147) = (term145 = term165).
Proof. exact (MK_COMB (@lem1708227) (@lem1708238)). Qed.
Lemma lem1708240 : term145 = term165.
Proof. exact (EQ_MP (@lem1708239) (@lem1708217)). Qed.
Lemma lem1708347 : term118 = term165.
Proof. exact (TRANS (@lem1708213) (@lem1708240)). Qed.
Lemma lem1708348 : term95 = term165.
Proof. exact (TRANS (@lem1708083) (@lem1708347)). Qed.
Lemma lem1708349 (h1 : term95) : term165.
Proof. exact (EQ_MP (@lem1708348) (@lem1708020 h1)). Qed.
Lemma lem1708356 (x : real) (y : real) (z : real) : (term166 x y z) = (term167 x y z).
Proof. exact (@lem17045 (real_le x y) (real_lt y z)). Qed.
Lemma lem1708357 (x : real) (z : real) : (real_lt x z) = (real_lt x z).
Proof. exact (eq_refl (real_lt x z)). Qed.
Lemma lem1708358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1708359 (x : real) (y : real) (z : real) : (term168 x y z) = (term169 x y z).
Proof. exact (MK_COMB (@lem1708358) (@lem1708356 x y z)). Qed.
Lemma lem1708360 (y : real) (x : real) (z : real) : (term170 y x z) = (term171 y x z).
Proof. exact (MK_COMB (@lem1708359 x y z) (@lem1708357 x z)). Qed.
Lemma lem1708361 (y : real) (x : real) (z : real) : (term84 y x z) = (term170 y x z).
Proof. exact (@lem17265 (term172 x y z) (real_lt x z)). Qed.
Lemma lem1708362 (y : real) (x : real) (z : real) : (term84 y x z) = (term171 y x z).
Proof. exact (TRANS (@lem1708361 y x z) (@lem1708360 y x z)). Qed.
Lemma lem1708363 (y : real) (x : real) : (term85 y x) = (term173 y x).
Proof. exact (fun_ext (fun z : real => @lem1708362 y x z)). Qed.
Lemma lem1708364 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708365 (y : real) (x : real) : (term86 y x) = (term174 y x).
Proof. exact (MK_COMB (@lem1708364) (@lem1708363 y x)). Qed.
Lemma lem1708366 (x : real) : (term87 x) = (term175 x).
Proof. exact (fun_ext (fun y : real => @lem1708365 y x)). Qed.
Lemma lem1708367 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708368 (x : real) : (term88 x) = (term176 x).
Proof. exact (MK_COMB (@lem1708367) (@lem1708366 x)). Qed.
Lemma lem1708369 : term89 = term177.
Proof. exact (fun_ext (fun x : real => @lem1708368 x)). Qed.
Lemma lem1708370 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708431 : term90 = term178.
Proof. exact (MK_COMB (@lem1708370) (@lem1708369)). Qed.
Lemma lem1708432 (h1 : term90) : term178.
Proof. exact (EQ_MP (@lem1708431) (@lem1708021 h1)). Qed.
Lemma lem1708433 (x : real) : ((term82 x) = x) = ((term82 x) = x).
Proof. exact (eq_refl ((term82 x) = x)). Qed.
Lemma lem1708434 : term83 = term83.
Proof. exact (fun_ext (fun x : real => @lem1708433 x)). Qed.
Lemma lem1708435 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708444 : term56 = term56.
Proof. exact (MK_COMB (@lem1708435) (@lem1708434)). Qed.
Lemma lem1708445 (h1 : term56) : term56.
Proof. exact (EQ_MP (@lem1708444) (@lem1708022 h1)). Qed.
Lemma lem1708455 (y : real) (h1 : term41 y) : term41 y.
Proof. exact (h1). Qed.
Lemma lem1708479 (x : real) (h1 : term43 x) : term43 x.
Proof. exact (h1). Qed.
Lemma lem1708490 (x : real) (n : nat) (y : real) : (term103 x n y) = (term103 x n y).
Proof. exact (eq_refl (term103 x n y)). Qed.
Lemma lem1708491 (x : real) (y : real) : (term105 x y) = (term105 x y).
Proof. exact (fun_ext (fun n : nat => @lem1708490 x n y)). Qed.
Lemma lem1708492 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1708493 (x : real) (y : real) : (term106 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1708492) (@lem1708491 x y)). Qed.
Lemma lem1708494 (x : real) (y : real) (h1 : term49 x y) : term106 x y.
Proof. exact (EQ_MP (@lem1708493 x y) (@lem1708060 x y h1)). Qed.
Lemma lem1708507 (y : real) (x : real) : (term111 y x) = (term111 y x).
Proof. exact (eq_refl (term111 y x)). Qed.
Lemma lem1708508 (x : real) : (term126 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1708507 y x)). Qed.
Lemma lem1708509 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708510 (x : real) : (term142 x) = (term142 x).
Proof. exact (MK_COMB (@lem1708509) (@lem1708508 x)). Qed.
Lemma lem1708511 : term149 = term149.
Proof. exact (fun_ext (fun x : real => @lem1708510 x)). Qed.
Lemma lem1708512 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708513 : term164 = term164.
Proof. exact (MK_COMB (@lem1708512) (@lem1708511)). Qed.
Lemma lem1708530 (y : real) (x : real) : (term128 y x) = (term128 y x).
Proof. exact (eq_refl (term128 y x)). Qed.
Lemma lem1708531 (x : real) : (term125 x) = (term125 x).
Proof. exact (fun_ext (fun y : real => @lem1708530 y x)). Qed.
Lemma lem1708532 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708533 (x : real) : (term137 x) = (term137 x).
Proof. exact (MK_COMB (@lem1708532) (@lem1708531 x)). Qed.
Lemma lem1708534 : term148 = term148.
Proof. exact (fun_ext (fun x : real => @lem1708533 x)). Qed.
Lemma lem1708535 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708536 : term159 = term159.
Proof. exact (MK_COMB (@lem1708535) (@lem1708534)). Qed.
Lemma lem1708537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1708538 : term161 = term161.
Proof. exact (MK_COMB (@lem1708537) (@lem1708536)). Qed.
Lemma lem1708539 : term165 = term165.
Proof. exact (MK_COMB (@lem1708538) (@lem1708513)). Qed.
Lemma lem1708540 (h1 : term95) : term165.
Proof. exact (EQ_MP (@lem1708539) (@lem1708349 h1)). Qed.
Lemma lem1708565 (y : real) (x : real) (z : real) : (term171 y x z) = (term171 y x z).
Proof. exact (eq_refl (term171 y x z)). Qed.
Lemma lem1708566 (y : real) (x : real) : (term173 y x) = (term173 y x).
Proof. exact (fun_ext (fun z : real => @lem1708565 y x z)). Qed.
Lemma lem1708567 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708568 (y : real) (x : real) : (term174 y x) = (term174 y x).
Proof. exact (MK_COMB (@lem1708567) (@lem1708566 y x)). Qed.
Lemma lem1708569 (x : real) : (term175 x) = (term175 x).
Proof. exact (fun_ext (fun y : real => @lem1708568 y x)). Qed.
Lemma lem1708570 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708571 (x : real) : (term176 x) = (term176 x).
Proof. exact (MK_COMB (@lem1708570) (@lem1708569 x)). Qed.
Lemma lem1708572 : term177 = term177.
Proof. exact (fun_ext (fun x : real => @lem1708571 x)). Qed.
Lemma lem1708573 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708574 : term178 = term178.
Proof. exact (MK_COMB (@lem1708573) (@lem1708572)). Qed.
Lemma lem1708575 (h1 : term90) : term178.
Proof. exact (EQ_MP (@lem1708574) (@lem1708432 h1)). Qed.
Lemma lem1708588 (x : real) : ((term82 x) = x) = ((term82 x) = x).
Proof. exact (eq_refl ((term82 x) = x)). Qed.
Lemma lem1708589 : term83 = term83.
Proof. exact (fun_ext (fun x : real => @lem1708588 x)). Qed.
Lemma lem1708590 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708591 : term56 = term56.
Proof. exact (MK_COMB (@lem1708590) (@lem1708589)). Qed.
Lemma lem1708592 (h1 : term56) : term56.
Proof. exact (EQ_MP (@lem1708591) (@lem1708445 h1)). Qed.
Lemma lem1708593 (h1 : term95) : term164.
Proof. exact (proj2 (@lem1708540 h1)). Qed.
Lemma lem1708598 (y : real) (h1 : term41 y) : term41 y.
Proof. exact (h1). Qed.
Lemma lem1708606 (x : real) (h1 : term43 x) : term43 x.
Proof. exact (h1). Qed.
Lemma lem1708608 (x : real) (n : nat) (y : real) : (term103 x n y) = (term103 x n y).
Proof. exact (eq_refl (term103 x n y)). Qed.
Lemma lem1708609 (x : real) (y : real) : (term105 x y) = (term105 x y).
Proof. exact (fun_ext (fun n : nat => @lem1708608 x n y)). Qed.
Lemma lem1708610 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1708612 (x : real) (y : real) : (term106 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1708610) (@lem1708609 x y)). Qed.
Lemma lem1708613 (x : real) (y : real) (h1 : term49 x y) : term106 x y.
Proof. exact (EQ_MP (@lem1708612 x y) (@lem1708494 x y h1)). Qed.
Lemma lem1708627 (y : real) (x : real) (z : real) : (term171 y x z) = (term171 y x z).
Proof. exact (eq_refl (term171 y x z)). Qed.
Lemma lem1708628 (y : real) (x : real) : (term173 y x) = (term173 y x).
Proof. exact (fun_ext (fun z : real => @lem1708627 y x z)). Qed.
Lemma lem1708629 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708630 (y : real) (x : real) : (term174 y x) = (term174 y x).
Proof. exact (MK_COMB (@lem1708629) (@lem1708628 y x)). Qed.
Lemma lem1708631 (x : real) : (term175 x) = (term175 x).
Proof. exact (fun_ext (fun y : real => @lem1708630 y x)). Qed.
Lemma lem1708632 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708633 (x : real) : (term176 x) = (term176 x).
Proof. exact (MK_COMB (@lem1708632) (@lem1708631 x)). Qed.
Lemma lem1708634 : term177 = term177.
Proof. exact (fun_ext (fun x : real => @lem1708633 x)). Qed.
Lemma lem1708635 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708637 : term178 = term178.
Proof. exact (MK_COMB (@lem1708635) (@lem1708634)). Qed.
Lemma lem1708638 (h1 : term90) : term178.
Proof. exact (EQ_MP (@lem1708637) (@lem1708575 h1)). Qed.
Lemma lem1708640 (x : real) : ((term82 x) = x) = ((term82 x) = x).
Proof. exact (eq_refl ((term82 x) = x)). Qed.
Lemma lem1708641 : term83 = term83.
Proof. exact (fun_ext (fun x : real => @lem1708640 x)). Qed.
Lemma lem1708642 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708644 : term56 = term56.
Proof. exact (MK_COMB (@lem1708642) (@lem1708641)). Qed.
Lemma lem1708645 (h1 : term56) : term56.
Proof. exact (EQ_MP (@lem1708644) (@lem1708592 h1)). Qed.
Lemma lem1708669 (y : real) (x : real) : (term111 y x) = (term111 y x).
Proof. exact (eq_refl (term111 y x)). Qed.
Lemma lem1708670 (x : real) : (term126 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1708669 y x)). Qed.
Lemma lem1708671 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708672 (x : real) : (term142 x) = (term142 x).
Proof. exact (MK_COMB (@lem1708671) (@lem1708670 x)). Qed.
Lemma lem1708673 : term149 = term149.
Proof. exact (fun_ext (fun x : real => @lem1708672 x)). Qed.
Lemma lem1708674 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1708676 : term164 = term164.
Proof. exact (MK_COMB (@lem1708674) (@lem1708673)). Qed.
Lemma lem1708677 (h1 : term95) : term164.
Proof. exact (EQ_MP (@lem1708676) (@lem1708593 h1)). Qed.
Lemma lem1708678 (_26444 : nat) (x : real) (y : real) (h1 : term49 x y) : term179 x y _26444.
Proof. exact (@lem1708613 x y h1 _26444). Qed.
Lemma lem1708679 (x : real) (_26444 : nat) (y : real) : (term179 x y _26444) = (term103 x _26444 y).
Proof. exact (eq_refl (term179 x y _26444)). Qed.
Lemma lem1708681 (_26445 : real) (h1 : term90) : term180 _26445.
Proof. exact (@lem1708638 h1 _26445). Qed.
Lemma lem1708682 (_26445 : real) : (term180 _26445) = (term176 _26445).
Proof. exact (eq_refl (term180 _26445)). Qed.
Lemma lem1708683 (_26445 : real) (h1 : term90) : term176 _26445.
Proof. exact (EQ_MP (@lem1708682 _26445) (@lem1708681 _26445 h1)). Qed.
Lemma lem1708684 (_26445 : real) (_26446 : real) (h1 : term90) : term181 _26445 _26446.
Proof. exact (@lem1708683 _26445 h1 _26446). Qed.
Lemma lem1708685 (_26446 : real) (_26445 : real) : (term181 _26445 _26446) = (term174 _26446 _26445).
Proof. exact (eq_refl (term181 _26445 _26446)). Qed.
Lemma lem1708686 (_26446 : real) (_26445 : real) (h1 : term90) : term174 _26446 _26445.
Proof. exact (EQ_MP (@lem1708685 _26446 _26445) (@lem1708684 _26445 _26446 h1)). Qed.
Lemma lem1708687 (_26446 : real) (_26445 : real) (_26447 : real) (h1 : term90) : term182 _26446 _26445 _26447.
Proof. exact (@lem1708686 _26446 _26445 h1 _26447). Qed.
Lemma lem1708688 (_26446 : real) (_26445 : real) (_26447 : real) : (term182 _26446 _26445 _26447) = (term171 _26446 _26445 _26447).
Proof. exact (eq_refl (term182 _26446 _26445 _26447)). Qed.
Lemma lem1708689 (_26446 : real) (_26445 : real) (_26447 : real) (h1 : term90) : term171 _26446 _26445 _26447.
Proof. exact (EQ_MP (@lem1708688 _26446 _26445 _26447) (@lem1708687 _26446 _26445 _26447 h1)). Qed.
Lemma lem1708690 (_26448 : real) (h1 : term56) : term183 _26448.
Proof. exact (@lem1708645 h1 _26448). Qed.
Lemma lem1708691 (_26448 : real) : (term183 _26448) = ((term82 _26448) = _26448).
Proof. exact (eq_refl (term183 _26448)). Qed.
Lemma lem1708699 (_26451 : real) (h1 : term95) : term152 _26451.
Proof. exact (@lem1708677 h1 _26451). Qed.
Lemma lem1708700 (_26451 : real) : (term152 _26451) = (term142 _26451).
Proof. exact (eq_refl (term152 _26451)). Qed.
Lemma lem1708701 (_26451 : real) (h1 : term95) : term142 _26451.
Proof. exact (EQ_MP (@lem1708700 _26451) (@lem1708699 _26451 h1)). Qed.
Lemma lem1708702 (_26451 : real) (_26452 : real) (h1 : term95) : term130 _26451 _26452.
Proof. exact (@lem1708701 _26451 h1 _26452). Qed.
Lemma lem1708703 (_26452 : real) (_26451 : real) : (term130 _26451 _26452) = (term111 _26452 _26451).
Proof. exact (eq_refl (term130 _26451 _26452)). Qed.
Lemma lem1708706 (y : real) (h1 : term41 y) : term41 y.
Proof. exact (h1). Qed.
Lemma lem1708710 (x : real) (h1 : term43 x) : term43 x.
Proof. exact (h1). Qed.
Lemma lem1708712 (_26444 : nat) (x : real) (y : real) (h1 : term49 x y) : term103 x _26444 y.
Proof. exact (EQ_MP (@lem1708679 x _26444 y) (@lem1708678 _26444 x y h1)). Qed.
Lemma lem1708723 (_26446 : real) (_26445 : real) (_26447 : real) : (term171 _26446 _26445 _26447) = (term184 _26446 _26445 _26447).
Proof. exact (@lem1707744 (term185 _26445 _26446) (term91 _26446 _26447) (real_lt _26445 _26447)). Qed.
Lemma lem1708724 (_26446 : real) (_26445 : real) (_26447 : real) (h1 : term90) : term184 _26446 _26445 _26447.
Proof. exact (EQ_MP (@lem1708723 _26446 _26445 _26447) (@lem1708689 _26446 _26445 _26447 h1)). Qed.
Lemma lem1708738 (_26452 : real) (_26451 : real) (h1 : term95) : term111 _26452 _26451.
Proof. exact (EQ_MP (@lem1708703 _26452 _26451) (@lem1708702 _26451 _26452 h1)). Qed.
Lemma lem1708758 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1708759 (_26457 : real) (_26459 : real) (h1 : _26457 = _26459) : _26457 = _26459.
Proof. exact (h1). Qed.
Lemma lem1708760 (_26458 : real) (_26460 : real) (h1 : _26458 = _26460) : _26458 = _26460.
Proof. exact (h1). Qed.
Lemma lem1708761 (_26457 : real) (_26459 : real) (h1 : _26457 = _26459) : (real_lt _26457) = (real_lt _26459).
Proof. exact (MK_COMB (@lem1708758) (@lem1708759 _26457 _26459 h1)). Qed.
Lemma lem1708762 (_26457 : real) (_26459 : real) (_26458 : real) (_26460 : real) (h1 : _26457 = _26459) (h2 : _26458 = _26460) : (real_lt _26457 _26458) = (real_lt _26459 _26460).
Proof. exact (MK_COMB (@lem1708761 _26457 _26459 h1) (@lem1708760 _26458 _26460 h2)). Qed.
Lemma lem1708764 (b : Prop) (a : Prop) : term186 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1708765 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : term187 _26459 _26460 _26457 _26458.
Proof. exact (@lem1708764 (real_lt _26459 _26460) (real_lt _26457 _26458)). Qed.
Lemma lem1708766 (_26457 : real) (_26459 : real) (_26458 : real) (_26460 : real) (h1 : _26457 = _26459) (h2 : _26458 = _26460) : term188 _26459 _26460 _26457 _26458.
Proof. exact (@lem1708765 _26459 _26460 _26457 _26458 (@lem1708762 _26457 _26459 _26458 _26460 h1 h2)). Qed.
Lemma lem1708767 (_26460 : real) (_26458 : real) (_26457 : real) (_26459 : real) (h1 : _26457 = _26459) : term189 _26459 _26460 _26457 _26458.
Proof. exact (fun h0 : _26458 = _26460 => @lem1708766 _26457 _26459 _26458 _26460 h1 h0). Qed.
Lemma lem1708769 (a : Prop) (b : Prop) : (a -> b) = (term190 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1708770 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term189 _26459 _26460 _26457 _26458) = (term191 _26459 _26460 _26457 _26458).
Proof. exact (@lem1708769 (_26458 = _26460) (term188 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1708771 (_26460 : real) (_26458 : real) (_26457 : real) (_26459 : real) (h1 : _26457 = _26459) : term191 _26459 _26460 _26457 _26458.
Proof. exact (EQ_MP (@lem1708770 _26459 _26460 _26457 _26458) (@lem1708767 _26460 _26458 _26457 _26459 h1)). Qed.
Lemma lem1708772 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : term192 _26459 _26460 _26457 _26458.
Proof. exact (fun h0 : _26457 = _26459 => @lem1708771 _26460 _26458 _26457 _26459 h0). Qed.
Lemma lem1708774 (a : Prop) (b : Prop) : (a -> b) = (term190 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1708775 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term192 _26459 _26460 _26457 _26458) = (term193 _26459 _26460 _26457 _26458).
Proof. exact (@lem1708774 (_26457 = _26459) (term191 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1708776 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : term193 _26459 _26460 _26457 _26458.
Proof. exact (EQ_MP (@lem1708775 _26459 _26460 _26457 _26458) (@lem1708772 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1708821 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1708822 : term194 = term194.
Proof. exact (@lem1708821 term194). Qed.
Lemma lem1708823 : term195.
Proof. exact (fun h0 : term196 => @lem1708822). Qed.
Lemma lem1708825 (p : Prop) : (term197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1708826 : term195 = (term194 = term194).
Proof. exact (@lem1708825 (term194 = term194)). Qed.
Lemma lem1708827 : term194 = term194.
Proof. exact (EQ_MP (@lem1708826) (@lem1708823)). Qed.
Lemma lem1708829 (_26448 : real) (h1 : term56) : (term82 _26448) = _26448.
Proof. exact (EQ_MP (@lem1708691 _26448) (@lem1708690 _26448 h1)). Qed.
Lemma lem1708830 (x : real) (h1 : term56) : (term82 x) = x.
Proof. exact (@lem1708829 x h1). Qed.
Lemma lem1708831 (x : real) (h1 : term56) : term198 x.
Proof. exact (fun h0 : term199 x => @lem1708830 x h1). Qed.
Lemma lem1708833 (p : Prop) : (term197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1708834 (x : real) : (term198 x) = ((term82 x) = x).
Proof. exact (@lem1708833 ((term82 x) = x)). Qed.
Lemma lem1708835 (x : real) (h1 : term56) : (term82 x) = x.
Proof. exact (EQ_MP (@lem1708834 x) (@lem1708831 x h1)). Qed.
Lemma lem1708837 (x : real) (h1 : term43 x) : term43 x.
Proof. exact (h1). Qed.
Lemma lem1708838 (x : real) (h1 : term43 x) : term200 x.
Proof. exact (fun h0 : term41 x => @lem1708837 x h1). Qed.
Lemma lem1708840 (p : Prop) : (term201 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1708841 (x : real) : (term200 x) = (term43 x).
Proof. exact (@lem1708840 (term41 x)). Qed.
Lemma lem1708842 (x : real) (h1 : term43 x) : term43 x.
Proof. exact (EQ_MP (@lem1708841 x) (@lem1708838 x h1)). Qed.
Lemma lem1708860 (q : Prop) (p : Prop) (r : Prop) : (term38 p q r) = (term38 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1708861 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term191 _26459 _26460 _26457 _26458) = (term202 _26459 _26460 _26457 _26458).
Proof. exact (@lem1708860 (real_lt _26459 _26460) (term203 _26458 _26460) (term91 _26457 _26458)). Qed.
Lemma lem1708879 (_26457 : real) (_26459 : real) : (term204 _26457 _26459) = (term204 _26457 _26459).
Proof. exact (eq_refl (term204 _26457 _26459)). Qed.
Lemma lem1708880 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term193 _26459 _26460 _26457 _26458) = (term205 _26459 _26460 _26457 _26458).
Proof. exact (MK_COMB (@lem1708879 _26457 _26459) (@lem1708861 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1708884 (q : Prop) (p : Prop) (r : Prop) : (term38 p q r) = (term38 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1708885 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term205 _26459 _26460 _26457 _26458) = (term206 _26459 _26460 _26457 _26458).
Proof. exact (@lem1708884 (real_lt _26459 _26460) (term203 _26457 _26459) (term207 _26460 _26457 _26458)). Qed.
Lemma lem1708915 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term193 _26459 _26460 _26457 _26458) = (term206 _26459 _26460 _26457 _26458).
Proof. exact (TRANS (@lem1708880 _26459 _26460 _26457 _26458) (@lem1708885 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1708916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1708917 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term208 _26459 _26460 _26457 _26458) = (term209 _26459 _26460 _26457 _26458).
Proof. exact (MK_COMB (@lem1708916) (@lem1708915 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1708921 (q : Prop) (p : Prop) (r : Prop) : (term38 p q r) = (term38 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1708922 (_26457 : real) (_26458 : real) (_26459 : real) (_26460 : real) : (term210 _26457 _26458 _26459 _26460) = (term211 _26457 _26458 _26459 _26460).
Proof. exact (@lem1708921 (term203 _26457 _26459) (term91 _26457 _26458) (term212 _26458 _26459 _26460)). Qed.
Lemma lem1708938 (q : Prop) (p : Prop) (r : Prop) : (term38 p q r) = (term38 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1708939 (_26457 : real) (_26458 : real) (_26459 : real) (_26460 : real) : (term213 _26457 _26458 _26459 _26460) = (term214 _26457 _26458 _26459 _26460).
Proof. exact (@lem1708938 (term203 _26458 _26460) (term91 _26457 _26458) (real_lt _26459 _26460)). Qed.
Lemma lem1708955 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1708956 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term215 _26457 _26458 _26459 _26460) = (term188 _26459 _26460 _26457 _26458).
Proof. exact (@lem1708955 (real_lt _26459 _26460) (term91 _26457 _26458)). Qed.
Lemma lem1708962 (_26458 : real) (_26460 : real) : (term204 _26458 _26460) = (term204 _26458 _26460).
Proof. exact (eq_refl (term204 _26458 _26460)). Qed.
Lemma lem1708963 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term214 _26457 _26458 _26459 _26460) = (term191 _26459 _26460 _26457 _26458).
Proof. exact (MK_COMB (@lem1708962 _26458 _26460) (@lem1708956 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1708967 (q : Prop) (p : Prop) (r : Prop) : (term38 p q r) = (term38 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1708968 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term191 _26459 _26460 _26457 _26458) = (term202 _26459 _26460 _26457 _26458).
Proof. exact (@lem1708967 (real_lt _26459 _26460) (term203 _26458 _26460) (term91 _26457 _26458)). Qed.
Lemma lem1708986 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term214 _26457 _26458 _26459 _26460) = (term202 _26459 _26460 _26457 _26458).
Proof. exact (TRANS (@lem1708963 _26459 _26460 _26457 _26458) (@lem1708968 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1708987 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term213 _26457 _26458 _26459 _26460) = (term202 _26459 _26460 _26457 _26458).
Proof. exact (TRANS (@lem1708939 _26457 _26458 _26459 _26460) (@lem1708986 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1708988 (_26457 : real) (_26459 : real) : (term204 _26457 _26459) = (term204 _26457 _26459).
Proof. exact (eq_refl (term204 _26457 _26459)). Qed.
Lemma lem1708989 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term211 _26457 _26458 _26459 _26460) = (term205 _26459 _26460 _26457 _26458).
Proof. exact (MK_COMB (@lem1708988 _26457 _26459) (@lem1708987 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1708993 (q : Prop) (p : Prop) (r : Prop) : (term38 p q r) = (term38 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1708994 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term205 _26459 _26460 _26457 _26458) = (term206 _26459 _26460 _26457 _26458).
Proof. exact (@lem1708993 (real_lt _26459 _26460) (term203 _26457 _26459) (term207 _26460 _26457 _26458)). Qed.
Lemma lem1709024 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term211 _26457 _26458 _26459 _26460) = (term206 _26459 _26460 _26457 _26458).
Proof. exact (TRANS (@lem1708989 _26459 _26460 _26457 _26458) (@lem1708994 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1709025 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term210 _26457 _26458 _26459 _26460) = (term206 _26459 _26460 _26457 _26458).
Proof. exact (TRANS (@lem1708922 _26457 _26458 _26459 _26460) (@lem1709024 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1709026 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : ((term193 _26459 _26460 _26457 _26458) = (term210 _26457 _26458 _26459 _26460)) = ((term206 _26459 _26460 _26457 _26458) = (term206 _26459 _26460 _26457 _26458)).
Proof. exact (MK_COMB (@lem1708917 _26459 _26460 _26457 _26458) (@lem1709025 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1709028 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1709029 (x : Prop) : (x = x) = True.
Proof. exact (@lem1709028 Prop x). Qed.
Lemma lem1709030 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : ((term206 _26459 _26460 _26457 _26458) = (term206 _26459 _26460 _26457 _26458)) = True.
Proof. exact (@lem1709029 (term206 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1709031 (_26457 : real) (_26458 : real) (_26459 : real) (_26460 : real) : ((term193 _26459 _26460 _26457 _26458) = (term210 _26457 _26458 _26459 _26460)) = True.
Proof. exact (TRANS (@lem1709026 _26459 _26460 _26457 _26458) (@lem1709030 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1709032 (_26457 : real) (_26458 : real) (_26459 : real) (_26460 : real) : True = ((term193 _26459 _26460 _26457 _26458) = (term210 _26457 _26458 _26459 _26460)).
Proof. exact (SYM (@lem1709031 _26457 _26458 _26459 _26460)). Qed.
Lemma lem1709033 (_26457 : real) (_26458 : real) (_26459 : real) (_26460 : real) : (term193 _26459 _26460 _26457 _26458) = (term210 _26457 _26458 _26459 _26460).
Proof. exact (EQ_MP (@lem1709032 _26457 _26458 _26459 _26460) (@lem0)). Qed.
Lemma lem1709034 (_26457 : real) (_26458 : real) (_26459 : real) (_26460 : real) : term210 _26457 _26458 _26459 _26460.
Proof. exact (EQ_MP (@lem1709033 _26457 _26458 _26459 _26460) (@lem1708776 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1709036 (b : Prop) (a : Prop) : (a \/ b) = (term216 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1709037 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term210 _26457 _26458 _26459 _26460) = (term217 _26459 _26460 _26457 _26458).
Proof. exact (@lem1709036 (term218 _26457 _26458 _26459 _26460) (term91 _26457 _26458)). Qed.
Lemma lem1709039 (a : Prop) (b : Prop) : (term219 a b) = (term220 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1709040 (_26457 : real) (_26458 : real) (_26459 : real) (_26460 : real) : (term221 _26457 _26458 _26459 _26460) = (term222 _26457 _26458 _26459 _26460).
Proof. exact (@lem1709039 (term203 _26457 _26459) (term212 _26458 _26459 _26460)). Qed.
Lemma lem1709042 (a : Prop) : (term223 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1709043 (_26457 : real) (_26459 : real) : (term224 _26457 _26459) = (_26457 = _26459).
Proof. exact (@lem1709042 (_26457 = _26459)). Qed.
Lemma lem1709044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1709045 (_26457 : real) (_26459 : real) : (term225 _26457 _26459) = (term226 _26457 _26459).
Proof. exact (MK_COMB (@lem1709044) (@lem1709043 _26457 _26459)). Qed.
Lemma lem1709047 (a : Prop) (b : Prop) : (term219 a b) = (term220 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1709048 (_26458 : real) (_26459 : real) (_26460 : real) : (term227 _26458 _26459 _26460) = (term228 _26458 _26459 _26460).
Proof. exact (@lem1709047 (term203 _26458 _26460) (real_lt _26459 _26460)). Qed.
Lemma lem1709050 (a : Prop) : (term223 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1709051 (_26458 : real) (_26460 : real) : (term224 _26458 _26460) = (_26458 = _26460).
Proof. exact (@lem1709050 (_26458 = _26460)). Qed.
Lemma lem1709052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1709053 (_26458 : real) (_26460 : real) : (term225 _26458 _26460) = (term226 _26458 _26460).
Proof. exact (MK_COMB (@lem1709052) (@lem1709051 _26458 _26460)). Qed.
Lemma lem1709054 (_26459 : real) (_26460 : real) : (term91 _26459 _26460) = (term91 _26459 _26460).
Proof. exact (eq_refl (term91 _26459 _26460)). Qed.
Lemma lem1709055 (_26458 : real) (_26459 : real) (_26460 : real) : (term228 _26458 _26459 _26460) = (term229 _26458 _26459 _26460).
Proof. exact (MK_COMB (@lem1709053 _26458 _26460) (@lem1709054 _26459 _26460)). Qed.
Lemma lem1709056 (_26458 : real) (_26459 : real) (_26460 : real) : (term227 _26458 _26459 _26460) = (term229 _26458 _26459 _26460).
Proof. exact (TRANS (@lem1709048 _26458 _26459 _26460) (@lem1709055 _26458 _26459 _26460)). Qed.
Lemma lem1709057 (_26457 : real) (_26458 : real) (_26459 : real) (_26460 : real) : (term222 _26457 _26458 _26459 _26460) = (term230 _26457 _26458 _26459 _26460).
Proof. exact (MK_COMB (@lem1709045 _26457 _26459) (@lem1709056 _26458 _26459 _26460)). Qed.
Lemma lem1709058 (_26457 : real) (_26458 : real) (_26459 : real) (_26460 : real) : (term221 _26457 _26458 _26459 _26460) = (term230 _26457 _26458 _26459 _26460).
Proof. exact (TRANS (@lem1709040 _26457 _26458 _26459 _26460) (@lem1709057 _26457 _26458 _26459 _26460)). Qed.
Lemma lem1709059 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1709060 (_26457 : real) (_26458 : real) (_26459 : real) (_26460 : real) : (term231 _26457 _26458 _26459 _26460) = (term232 _26457 _26458 _26459 _26460).
Proof. exact (MK_COMB (@lem1709059) (@lem1709058 _26457 _26458 _26459 _26460)). Qed.
Lemma lem1709061 (_26457 : real) (_26458 : real) : (term91 _26457 _26458) = (term91 _26457 _26458).
Proof. exact (eq_refl (term91 _26457 _26458)). Qed.
Lemma lem1709062 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term217 _26459 _26460 _26457 _26458) = (term233 _26459 _26460 _26457 _26458).
Proof. exact (MK_COMB (@lem1709060 _26457 _26458 _26459 _26460) (@lem1709061 _26457 _26458)). Qed.
Lemma lem1709063 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : (term210 _26457 _26458 _26459 _26460) = (term233 _26459 _26460 _26457 _26458).
Proof. exact (TRANS (@lem1709037 _26459 _26460 _26457 _26458) (@lem1709062 _26459 _26460 _26457 _26458)). Qed.
Lemma lem1709065 (x : real) (h1 : term56) (h2 : term43 x) : term234 x.
Proof. exact (conj (@lem1708835 x h1) (@lem1708842 x h2)). Qed.
Lemma lem1709066 (x : real) (h1 : term56) (h2 : term43 x) : term235 x.
Proof. exact (conj (@lem1708827) (@lem1709065 x h1 h2)). Qed.
Lemma lem1709068 (_26459 : real) (_26460 : real) (_26457 : real) (_26458 : real) : term233 _26459 _26460 _26457 _26458.
Proof. exact (EQ_MP (@lem1709063 _26459 _26460 _26457 _26458) (@lem1709034 _26457 _26458 _26459 _26460)). Qed.
Lemma lem1709069 (x : real) : term236 x.
Proof. exact (@lem1709068 term194 x term194 (term82 x)). Qed.
Lemma lem1709072 (x : real) (h1 : term56) (h2 : term43 x) : term237 x.
Proof. exact (@lem1709069 x (@lem1709066 x h1 h2)). Qed.
Lemma lem1709073 (x : real) (h1 : term56) (h2 : term43 x) : term238 x.
Proof. exact (fun h0 : term239 x => @lem1709072 x h1 h2). Qed.
Lemma lem1709075 (p : Prop) : (term201 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1709076 (x : real) : (term238 x) = (term237 x).
Proof. exact (@lem1709075 (term239 x)). Qed.
Lemma lem1709077 (x : real) (h1 : term56) (h2 : term43 x) : term237 x.
Proof. exact (EQ_MP (@lem1709076 x) (@lem1709073 x h1 h2)). Qed.
Lemma lem1709083 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1709084 (_26451 : real) (_26452 : real) : (term111 _26452 _26451) = (term240 _26451 _26452).
Proof. exact (@lem1709083 (real_le _26452 _26451) (real_lt _26451 _26452)). Qed.
Lemma lem1709090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1709091 (_26451 : real) (_26452 : real) : (term241 _26452 _26451) = (term242 _26451 _26452).
Proof. exact (MK_COMB (@lem1709090) (@lem1709084 _26451 _26452)). Qed.
Lemma lem1709097 (_26451 : real) (_26452 : real) : (term240 _26451 _26452) = (term240 _26451 _26452).
Proof. exact (eq_refl (term240 _26451 _26452)). Qed.
Lemma lem1709098 (_26451 : real) (_26452 : real) : ((term111 _26452 _26451) = (term240 _26451 _26452)) = ((term240 _26451 _26452) = (term240 _26451 _26452)).
Proof. exact (MK_COMB (@lem1709091 _26451 _26452) (@lem1709097 _26451 _26452)). Qed.
Lemma lem1709100 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1709101 (x : Prop) : (x = x) = True.
Proof. exact (@lem1709100 Prop x). Qed.
Lemma lem1709102 (_26451 : real) (_26452 : real) : ((term240 _26451 _26452) = (term240 _26451 _26452)) = True.
Proof. exact (@lem1709101 (term240 _26451 _26452)). Qed.
Lemma lem1709103 (_26451 : real) (_26452 : real) : ((term111 _26452 _26451) = (term240 _26451 _26452)) = True.
Proof. exact (TRANS (@lem1709098 _26451 _26452) (@lem1709102 _26451 _26452)). Qed.
Lemma lem1709104 (_26451 : real) (_26452 : real) : True = ((term111 _26452 _26451) = (term240 _26451 _26452)).
Proof. exact (SYM (@lem1709103 _26451 _26452)). Qed.
Lemma lem1709105 (_26451 : real) (_26452 : real) : (term111 _26452 _26451) = (term240 _26451 _26452).
Proof. exact (EQ_MP (@lem1709104 _26451 _26452) (@lem0)). Qed.
Lemma lem1709106 (_26451 : real) (_26452 : real) (h1 : term95) : term240 _26451 _26452.
Proof. exact (EQ_MP (@lem1709105 _26451 _26452) (@lem1708738 _26452 _26451 h1)). Qed.
Lemma lem1709108 (b : Prop) (a : Prop) : (a \/ b) = (term216 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1709111 (_26452 : real) (_26451 : real) : (term240 _26451 _26452) = (term243 _26452 _26451).
Proof. exact (@lem1709108 (real_lt _26451 _26452) (real_le _26452 _26451)). Qed.
Lemma lem1709114 (_26452 : real) (_26451 : real) (h1 : term95) : term243 _26452 _26451.
Proof. exact (EQ_MP (@lem1709111 _26452 _26451) (@lem1709106 _26451 _26452 h1)). Qed.
Lemma lem1709115 (x : real) (h1 : term95) : term244 x.
Proof. exact (@lem1709114 (term82 x) term194 h1). Qed.
Lemma lem1709118 (x : real) (h1 : term95) (h2 : term56) (h3 : term43 x) : term245 x.
Proof. exact (@lem1709115 x h1 (@lem1709077 x h2 h3)). Qed.
Lemma lem1709119 (x : real) (h1 : term95) (h2 : term56) (h3 : term43 x) : term246 x.
Proof. exact (fun h0 : term247 x => @lem1709118 x h1 h2 h3). Qed.
Lemma lem1709121 (p : Prop) : (term197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1709122 (x : real) : (term246 x) = (term245 x).
Proof. exact (@lem1709121 (term245 x)). Qed.
Lemma lem1709123 (x : real) (h1 : term95) (h2 : term56) (h3 : term43 x) : term245 x.
Proof. exact (EQ_MP (@lem1709122 x) (@lem1709119 x h1 h2 h3)). Qed.
Lemma lem1709125 (y : real) (h1 : term41 y) : term41 y.
Proof. exact (h1). Qed.
Lemma lem1709126 (y : real) (h1 : term41 y) : term248 y.
Proof. exact (fun h0 : term43 y => @lem1709125 y h1). Qed.
Lemma lem1709128 (p : Prop) : (term197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1709129 (y : real) : (term248 y) = (term41 y).
Proof. exact (@lem1709128 (term41 y)). Qed.
Lemma lem1709130 (y : real) (h1 : term41 y) : term41 y.
Proof. exact (EQ_MP (@lem1709129 y) (@lem1709126 y h1)). Qed.
Lemma lem1709146 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1709147 (_26445 : real) (_26446 : real) (_26447 : real) : (term249 _26446 _26445 _26447) = (term250 _26445 _26446 _26447).
Proof. exact (@lem1709146 (real_lt _26445 _26447) (term91 _26446 _26447)). Qed.
Lemma lem1709153 (_26445 : real) (_26446 : real) : (term251 _26445 _26446) = (term251 _26445 _26446).
Proof. exact (eq_refl (term251 _26445 _26446)). Qed.
Lemma lem1709154 (_26445 : real) (_26446 : real) (_26447 : real) : (term184 _26446 _26445 _26447) = (term252 _26445 _26446 _26447).
Proof. exact (MK_COMB (@lem1709153 _26445 _26446) (@lem1709147 _26445 _26446 _26447)). Qed.
Lemma lem1709158 (q : Prop) (p : Prop) (r : Prop) : (term38 p q r) = (term38 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1709159 (_26445 : real) (_26446 : real) (_26447 : real) : (term252 _26445 _26446 _26447) = (term253 _26445 _26446 _26447).
Proof. exact (@lem1709158 (real_lt _26445 _26447) (term185 _26445 _26446) (term91 _26446 _26447)). Qed.
Lemma lem1709175 (_26445 : real) (_26446 : real) (_26447 : real) : (term184 _26446 _26445 _26447) = (term253 _26445 _26446 _26447).
Proof. exact (TRANS (@lem1709154 _26445 _26446 _26447) (@lem1709159 _26445 _26446 _26447)). Qed.
Lemma lem1709176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1709177 (_26445 : real) (_26446 : real) (_26447 : real) : (term254 _26446 _26445 _26447) = (term255 _26445 _26446 _26447).
Proof. exact (MK_COMB (@lem1709176) (@lem1709175 _26445 _26446 _26447)). Qed.
Lemma lem1709193 (_26445 : real) (_26446 : real) (_26447 : real) : (term253 _26445 _26446 _26447) = (term253 _26445 _26446 _26447).
Proof. exact (eq_refl (term253 _26445 _26446 _26447)). Qed.
Lemma lem1709194 (_26445 : real) (_26446 : real) (_26447 : real) : ((term184 _26446 _26445 _26447) = (term253 _26445 _26446 _26447)) = ((term253 _26445 _26446 _26447) = (term253 _26445 _26446 _26447)).
Proof. exact (MK_COMB (@lem1709177 _26445 _26446 _26447) (@lem1709193 _26445 _26446 _26447)). Qed.
Lemma lem1709196 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1709197 (x : Prop) : (x = x) = True.
Proof. exact (@lem1709196 Prop x). Qed.
Lemma lem1709198 (_26445 : real) (_26446 : real) (_26447 : real) : ((term253 _26445 _26446 _26447) = (term253 _26445 _26446 _26447)) = True.
Proof. exact (@lem1709197 (term253 _26445 _26446 _26447)). Qed.
Lemma lem1709199 (_26445 : real) (_26446 : real) (_26447 : real) : ((term184 _26446 _26445 _26447) = (term253 _26445 _26446 _26447)) = True.
Proof. exact (TRANS (@lem1709194 _26445 _26446 _26447) (@lem1709198 _26445 _26446 _26447)). Qed.
Lemma lem1709200 (_26445 : real) (_26446 : real) (_26447 : real) : True = ((term184 _26446 _26445 _26447) = (term253 _26445 _26446 _26447)).
Proof. exact (SYM (@lem1709199 _26445 _26446 _26447)). Qed.
Lemma lem1709201 (_26445 : real) (_26446 : real) (_26447 : real) : (term184 _26446 _26445 _26447) = (term253 _26445 _26446 _26447).
Proof. exact (EQ_MP (@lem1709200 _26445 _26446 _26447) (@lem0)). Qed.
Lemma lem1709202 (_26445 : real) (_26446 : real) (_26447 : real) (h1 : term90) : term253 _26445 _26446 _26447.
Proof. exact (EQ_MP (@lem1709201 _26445 _26446 _26447) (@lem1708724 _26446 _26445 _26447 h1)). Qed.
Lemma lem1709204 (b : Prop) (a : Prop) : (a \/ b) = (term216 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1709205 (_26446 : real) (_26445 : real) (_26447 : real) : (term253 _26445 _26446 _26447) = (term256 _26446 _26445 _26447).
Proof. exact (@lem1709204 (term167 _26445 _26446 _26447) (real_lt _26445 _26447)). Qed.
Lemma lem1709207 (a : Prop) (b : Prop) : (term219 a b) = (term220 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1709208 (_26445 : real) (_26446 : real) (_26447 : real) : (term257 _26445 _26446 _26447) = (term258 _26445 _26446 _26447).
Proof. exact (@lem1709207 (term185 _26445 _26446) (term91 _26446 _26447)). Qed.
Lemma lem1709210 (a : Prop) : (term223 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1709211 (_26445 : real) (_26446 : real) : (term259 _26445 _26446) = (real_le _26445 _26446).
Proof. exact (@lem1709210 (real_le _26445 _26446)). Qed.
Lemma lem1709212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1709213 (_26445 : real) (_26446 : real) : (term260 _26445 _26446) = (term261 _26445 _26446).
Proof. exact (MK_COMB (@lem1709212) (@lem1709211 _26445 _26446)). Qed.
Lemma lem1709215 (a : Prop) : (term223 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1709216 (_26446 : real) (_26447 : real) : (term107 _26446 _26447) = (real_lt _26446 _26447).
Proof. exact (@lem1709215 (real_lt _26446 _26447)). Qed.
Lemma lem1709217 (_26445 : real) (_26446 : real) (_26447 : real) : (term258 _26445 _26446 _26447) = (term172 _26445 _26446 _26447).
Proof. exact (MK_COMB (@lem1709213 _26445 _26446) (@lem1709216 _26446 _26447)). Qed.
Lemma lem1709218 (_26445 : real) (_26446 : real) (_26447 : real) : (term257 _26445 _26446 _26447) = (term172 _26445 _26446 _26447).
Proof. exact (TRANS (@lem1709208 _26445 _26446 _26447) (@lem1709217 _26445 _26446 _26447)). Qed.
Lemma lem1709219 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1709220 (_26445 : real) (_26446 : real) (_26447 : real) : (term262 _26445 _26446 _26447) = (term263 _26445 _26446 _26447).
Proof. exact (MK_COMB (@lem1709219) (@lem1709218 _26445 _26446 _26447)). Qed.
Lemma lem1709221 (_26445 : real) (_26447 : real) : (real_lt _26445 _26447) = (real_lt _26445 _26447).
Proof. exact (eq_refl (real_lt _26445 _26447)). Qed.
Lemma lem1709222 (_26446 : real) (_26445 : real) (_26447 : real) : (term256 _26446 _26445 _26447) = (term84 _26446 _26445 _26447).
Proof. exact (MK_COMB (@lem1709220 _26445 _26446 _26447) (@lem1709221 _26445 _26447)). Qed.
Lemma lem1709223 (_26446 : real) (_26445 : real) (_26447 : real) : (term253 _26445 _26446 _26447) = (term84 _26446 _26445 _26447).
Proof. exact (TRANS (@lem1709205 _26446 _26445 _26447) (@lem1709222 _26446 _26445 _26447)). Qed.
Lemma lem1709225 (x : real) (y : real) (h1 : term95) (h2 : term56) (h3 : term43 x) (h4 : term41 y) : term264 x y.
Proof. exact (conj (@lem1709123 x h1 h2 h3) (@lem1709130 y h4)). Qed.
Lemma lem1709227 (_26446 : real) (_26445 : real) (_26447 : real) (h1 : term90) : term84 _26446 _26445 _26447.
Proof. exact (EQ_MP (@lem1709223 _26446 _26445 _26447) (@lem1709202 _26445 _26446 _26447 h1)). Qed.
Lemma lem1709228 (x : real) (y : real) (h1 : term90) : term265 x y.
Proof. exact (@lem1709227 term194 (term82 x) y h1). Qed.
Lemma lem1709231 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term43 x) (h5 : term41 y) : term266 x y.
Proof. exact (@lem1709228 x y h1 (@lem1709225 x y h2 h3 h4 h5)). Qed.
Lemma lem1709232 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term43 x) (h5 : term41 y) : term267 x y.
Proof. exact (fun h0 : term268 x y => @lem1709231 x y h1 h2 h3 h4 h5). Qed.
Lemma lem1709234 (p : Prop) : (term197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1709235 (x : real) (y : real) : (term267 x y) = (term266 x y).
Proof. exact (@lem1709234 (term266 x y)). Qed.
Lemma lem1709236 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term43 x) (h5 : term41 y) : term266 x y.
Proof. exact (EQ_MP (@lem1709235 x y) (@lem1709232 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1709239 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1709241 (x : real) (_26444 : nat) (y : real) : (term103 x _26444 y) = (term269 x _26444 y).
Proof. exact (@lem1709239 (term96 x _26444 y)). Qed.
Lemma lem1709244 (_26444 : nat) (x : real) (y : real) (h1 : term49 x y) : term269 x _26444 y.
Proof. exact (EQ_MP (@lem1709241 x _26444 y) (@lem1708712 _26444 x y h1)). Qed.
Lemma lem1709245 (x : real) (y : real) (h1 : term49 x y) : term270 x y.
Proof. exact (@lem1709244 term271 x y h1). Qed.
Lemma lem1709248 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (@lem1709245 x y h4 (@lem1709236 x y h1 h2 h3 h5 h6)). Qed.
Lemma lem1709249 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : term272.
Proof. exact (fun h0 : ~ False => @lem1709248 x y h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1709251 (p : Prop) : (term197 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1709252 : term272 = False.
Proof. exact (@lem1709251 False). Qed.
Lemma lem1709253 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709252) (@lem1709249 x y h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1709254 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : (term43 x) = False.
Proof. exact (prop_ext (fun h7 : term43 x => @lem1709253 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708710 x h5)). Qed.
Lemma lem1709255 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709254 x y h1 h2 h3 h4 h5 h6) (@lem1708710 x h5)). Qed.
Lemma lem1709256 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : (term41 y) = False.
Proof. exact (prop_ext (fun h7 : term41 y => @lem1709255 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708706 y h6)). Qed.
Lemma lem1709257 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709256 x y h1 h2 h3 h4 h5 h6) (@lem1708706 y h6)). Qed.
Lemma lem1709258 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : (term43 x) = False.
Proof. exact (prop_ext (fun h7 : term43 x => @lem1709257 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708606 x h5)). Qed.
Lemma lem1709259 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709258 x y h1 h2 h3 h4 h5 h6) (@lem1708606 x h5)). Qed.
Lemma lem1709260 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : (term41 y) = False.
Proof. exact (prop_ext (fun h7 : term41 y => @lem1709259 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708598 y h6)). Qed.
Lemma lem1709261 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709260 x y h1 h2 h3 h4 h5 h6) (@lem1708598 y h6)). Qed.
Lemma lem1709262 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : term56 = False.
Proof. exact (prop_ext (fun h7 : term56 => @lem1709261 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708645 h3)). Qed.
Lemma lem1709263 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709262 x y h1 h2 h3 h4 h5 h6) (@lem1708645 h3)). Qed.
Lemma lem1709264 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : (term43 x) = False.
Proof. exact (prop_ext (fun h7 : term43 x => @lem1709263 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708606 x h5)). Qed.
Lemma lem1709265 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709264 x y h1 h2 h3 h4 h5 h6) (@lem1708606 x h5)). Qed.
Lemma lem1709266 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : (term41 y) = False.
Proof. exact (prop_ext (fun h7 : term41 y => @lem1709265 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708598 y h6)). Qed.
Lemma lem1709267 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709266 x y h1 h2 h3 h4 h5 h6) (@lem1708598 y h6)). Qed.
Lemma lem1709268 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : term56 = False.
Proof. exact (prop_ext (fun h7 : term56 => @lem1709267 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708592 h3)). Qed.
Lemma lem1709269 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709268 x y h1 h2 h3 h4 h5 h6) (@lem1708592 h3)). Qed.
Lemma lem1709270 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : (term43 x) = False.
Proof. exact (prop_ext (fun h7 : term43 x => @lem1709269 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708479 x h5)). Qed.
Lemma lem1709271 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709270 x y h1 h2 h3 h4 h5 h6) (@lem1708479 x h5)). Qed.
Lemma lem1709272 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : (term41 y) = False.
Proof. exact (prop_ext (fun h7 : term41 y => @lem1709271 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708455 y h6)). Qed.
Lemma lem1709273 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709272 x y h1 h2 h3 h4 h5 h6) (@lem1708455 y h6)). Qed.
Lemma lem1709274 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : term56 = False.
Proof. exact (prop_ext (fun h7 : term56 => @lem1709273 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708445 h3)). Qed.
Lemma lem1709275 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709274 x y h1 h2 h3 h4 h5 h6) (@lem1708445 h3)). Qed.
Lemma lem1709276 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : (term43 x) = False.
Proof. exact (prop_ext (fun h7 : term43 x => @lem1709275 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708040 x h5)). Qed.
Lemma lem1709277 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709276 x y h1 h2 h3 h4 h5 h6) (@lem1708040 x h5)). Qed.
Lemma lem1709278 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : (term41 y) = False.
Proof. exact (prop_ext (fun h7 : term41 y => @lem1709277 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1708028 y h6)). Qed.
Lemma lem1709279 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term56) (h4 : term49 x y) (h5 : term43 x) (h6 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709278 x y h1 h2 h3 h4 h5 h6) (@lem1708028 y h6)). Qed.
Lemma lem1709280 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term49 x y) (h4 : term43 x) (h5 : term41 y) : term54.
Proof. exact (fun h0 : term56 => @lem1709279 x y h1 h2 h0 h3 h4 h5). Qed.
Lemma lem1709281 : term54 = term55.
Proof. exact (@lem69 term56). Qed.
Lemma lem1709282 (x : real) (y : real) (h1 : term90) (h2 : term95) (h3 : term49 x y) (h4 : term43 x) (h5 : term41 y) : term55.
Proof. exact (EQ_MP (@lem1709281) (@lem1709280 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1709283 (x : real) (y : real) (h1 : term95) (h2 : term49 x y) (h3 : term43 x) (h4 : term41 y) : term59.
Proof. exact (fun h0 : term90 => @lem1709282 x y h0 h1 h2 h3 h4). Qed.
Lemma lem1709284 (x : real) (y : real) (h1 : term49 x y) (h2 : term43 x) (h3 : term41 y) : term62.
Proof. exact (fun h0 : term95 => @lem1709283 x y h0 h1 h2 h3). Qed.
Lemma lem1709285 (x : real) (y : real) (h1 : term43 x) (h2 : term41 y) : term65 x y.
Proof. exact (fun h0 : term49 x y => @lem1709284 x y h0 h1 h2). Qed.
Lemma lem1709286 (x : real) (y : real) (h1 : term41 y) : term68 x y.
Proof. exact (fun h0 : term43 x => @lem1709285 x y h0 h1). Qed.
Lemma lem1709287 (x : real) (y : real) (h1 : term41 y) : term71 x y.
Proof. exact (fun h0 : term45 x => @lem1709286 x y h1). Qed.
Lemma lem1709288 (x : real) (y : real) : term73 x y.
Proof. exact (fun h0 : term41 y => @lem1709287 x y h0). Qed.
Lemma lem1709293 (y : real) : term77 y.
Proof. exact (fun x : real => @lem1709288 x y). Qed.
Lemma lem1709298 : term81.
Proof. exact (fun y : real => @lem1709293 y). Qed.
Lemma lem1709299 : term80.
Proof. exact (EQ_MP (@lem1708015) (@lem1709298)). Qed.
Lemma lem1709300 (y : real) : term273 y.
Proof. exact (@lem1709299 y). Qed.
Lemma lem1709301 (y : real) : (term273 y) = (term76 y).
Proof. exact (eq_refl (term273 y)). Qed.
Lemma lem1709302 (y : real) : term76 y.
Proof. exact (EQ_MP (@lem1709301 y) (@lem1709300 y)). Qed.
Lemma lem1709303 (y : real) (x : real) : term274 y x.
Proof. exact (@lem1709302 y x). Qed.
Lemma lem1709304 (x : real) (y : real) : (term274 y x) = (term50 x y).
Proof. exact (eq_refl (term274 y x)). Qed.
Lemma lem1709305 (x : real) (y : real) : term50 x y.
Proof. exact (EQ_MP (@lem1709304 x y) (@lem1709303 y x)). Qed.
Lemma lem1709307 (x : real) (y : real) : term50 x y.
Proof. exact (@lem1707772 x y (@lem1709305 x y)). Qed.
Lemma lem1709308 (x : real) (y : real) (h1 : term41 y) : term70 x y.
Proof. exact (@lem1709307 x y (@lem1707752 y h1)). Qed.
Lemma lem1709309 (x : real) (y : real) (h1 : term45 x) (h2 : term41 y) : term67 x y.
Proof. exact (@lem1709308 x y h2 (@lem1707751 x h1)). Qed.
Lemma lem1709310 (x : real) (y : real) (h1 : term43 x) (h2 : term45 x) (h3 : term41 y) : term64 x y.
Proof. exact (@lem1709309 x y h2 h3 (@lem1707749 x h1)). Qed.
Lemma lem1709311 (x : real) (y : real) (h1 : term49 x y) (h2 : term43 x) (h3 : term45 x) (h4 : term41 y) : term61.
Proof. exact (@lem1709310 x y h2 h3 h4 (@lem1707757 x y h1)). Qed.
Lemma lem1709312 (x : real) (y : real) (h1 : term49 x y) (h2 : term43 x) (h3 : term45 x) (h4 : term41 y) : term58.
Proof. exact (@lem1709311 x y h1 h2 h3 h4 (@lem1376537)). Qed.
Lemma lem1709313 (x : real) (y : real) (h1 : term49 x y) (h2 : term43 x) (h3 : term45 x) (h4 : term41 y) : term54.
Proof. exact (@lem1709312 x y h1 h2 h3 h4 (@lem1371386)). Qed.
Lemma lem1709314 (x : real) (y : real) (h1 : term49 x y) (h2 : term43 x) (h3 : term45 x) (h4 : term41 y) : False.
Proof. exact (@lem1709313 x y h1 h2 h3 h4 (@lem1631005)). Qed.
Lemma lem1709315 (x : real) (y : real) (h1 : term49 x y) (h2 : term43 x) (h3 : term45 x) (h4 : term41 y) : (term49 x y) = False.
Proof. exact (prop_ext (fun h5 : term49 x y => @lem1709314 x y h1 h2 h3 h4) (fun h5 : False => @lem1707757 x y h1)). Qed.
Lemma lem1709316 (x : real) (y : real) (h1 : term49 x y) (h2 : term43 x) (h3 : term45 x) (h4 : term41 y) : False.
Proof. exact (EQ_MP (@lem1709315 x y h1 h2 h3 h4) (@lem1707757 x y h1)). Qed.
Lemma lem1709317 (x : real) (y : real) (h1 : term43 x) (h2 : term45 x) (h3 : term41 y) : term48 x y.
Proof. exact (fun h0 : term49 x y => @lem1709316 x y h0 h1 h2 h3). Qed.
Lemma lem1709318 (x : real) (y : real) (h1 : term43 x) (h2 : term45 x) (h3 : term41 y) : term47 x y.
Proof. exact (EQ_MP (@lem1707756 x y) (@lem1709317 x y h1 h2 h3)). Qed.
Lemma lem1709319 (x : real) (h1 : term275 x) : term275 x.
Proof. exact (h1). Qed.
Lemma lem1709320 (x : real) : term276 x.
Proof. exact (@lem1632194 x). Qed.
Lemma lem1709321 (x : real) : (term276 x) = (term277 x).
Proof. exact (eq_refl (term276 x)). Qed.
Lemma lem1709322 (x : real) : term277 x.
Proof. exact (EQ_MP (@lem1709321 x) (@lem1709320 x)). Qed.
Lemma lem1709323 (x : real) (y : real) : term278 x y.
Proof. exact (@lem1709322 x y). Qed.
Lemma lem1709324 (y : real) (x : real) : (term278 x y) = (term279 y x).
Proof. exact (eq_refl (term278 x y)). Qed.
Lemma lem1709325 (y : real) (x : real) : term279 y x.
Proof. exact (EQ_MP (@lem1709324 y x) (@lem1709323 x y)). Qed.
Lemma lem1709326 (x : real) (y : real) (h1 : term280 x y) : term280 x y.
Proof. exact (h1). Qed.
Lemma lem1709327 (x : real) (y : real) (h1 : term280 x y) : term281 y x.
Proof. exact (@lem1709325 y x (@lem1709326 x y h1)). Qed.
Lemma lem1709328 (y : real) (x : real) : (term281 y x) = ((term281 y x) = True).
Proof. exact (@lem7 (term281 y x)). Qed.
Lemma lem1709329 (x : real) (y : real) (h1 : term280 x y) : (term281 y x) = True.
Proof. exact (EQ_MP (@lem1709328 y x) (@lem1709327 x y h1)). Qed.
Lemma lem1709337 (x : real) : (term45 x) = ((term45 x) = True).
Proof. exact (@lem7 (term45 x)). Qed.
Lemma lem1709339 (x : real) : (term41 x) = ((term41 x) = True).
Proof. exact (@lem7 (term41 x)). Qed.
Lemma lem1709342 (y : real) (x : real) : term282 y x.
Proof. exact (fun h0 : term280 x y => @lem1709329 x y h0). Qed.
Lemma lem1709343 (x : real) : term283 x.
Proof. exact (@lem1709342 term284 x). Qed.
Lemma lem1709347 (x : real) (h1 : term41 x) : (term41 x) = True.
Proof. exact (EQ_MP (@lem1709339 x) (@lem1707748 x h1)). Qed.
Lemma lem1709348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1709349 (x : real) (h1 : term41 x) : (term285 x) = (and True).
Proof. exact (MK_COMB (@lem1709348) (@lem1709347 x h1)). Qed.
Lemma lem1709351 (x : real) (h1 : term45 x) : (term45 x) = True.
Proof. exact (EQ_MP (@lem1709337 x) (@lem1707751 x h1)). Qed.
Lemma lem1709352 (x : real) (h1 : term45 x) (h2 : term41 x) : (term286 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1709349 x h2) (@lem1709351 x h1)). Qed.
Lemma lem1709354 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1709355 : (True /\ True) = True.
Proof. exact (@lem1709354 True). Qed.
Lemma lem1709356 (x : real) (h1 : term45 x) (h2 : term41 x) : (term286 x) = True.
Proof. exact (TRANS (@lem1709352 x h1 h2) (@lem1709355)). Qed.
Lemma lem1709357 (x : real) (h1 : term45 x) (h2 : term41 x) : True = (term286 x).
Proof. exact (SYM (@lem1709356 x h1 h2)). Qed.
Lemma lem1709358 (x : real) (h1 : term45 x) (h2 : term41 x) : term286 x.
Proof. exact (EQ_MP (@lem1709357 x h1 h2) (@lem0)). Qed.
Lemma lem1709359 (x : real) (h1 : term45 x) (h2 : term41 x) : (term275 x) = True.
Proof. exact (@lem1709343 x (@lem1709358 x h1 h2)). Qed.
Lemma lem1709360 (x : real) (h1 : term45 x) (h2 : term41 x) : True = (term275 x).
Proof. exact (SYM (@lem1709359 x h1 h2)). Qed.
Lemma lem1709361 (x : real) (h1 : term45 x) (h2 : term41 x) : term275 x.
Proof. exact (EQ_MP (@lem1709360 x h1 h2) (@lem0)). Qed.
Lemma lem1709365 : term287 = term284.
Proof. exact (@lem1592014 (@lem1592030)). Qed.
Lemma lem1709366 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1709367 : term288 = term289.
Proof. exact (MK_COMB (@lem1709366) (@lem1709365)). Qed.
Lemma lem1709368 (x : real) : (real_inv x) = (real_inv x).
Proof. exact (eq_refl (real_inv x)). Qed.
Lemma lem1709369 (x : real) : (term275 x) = (term290 x).
Proof. exact (MK_COMB (@lem1709367) (@lem1709368 x)). Qed.
Lemma lem1709370 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1709371 (x : real) : (term291 x) = (term292 x).
Proof. exact (MK_COMB (@lem1709370) (@lem1709369 x)). Qed.
Lemma lem1709376 (x : real) (y : real) : (term47 x y) = (term47 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1709377 (x : real) (y : real) : (term293 x y) = (term294 x y).
Proof. exact (MK_COMB (@lem1709371 x) (@lem1709376 x y)). Qed.
Lemma lem1709380 (x : real) (y : real) : (term294 x y) = (term293 x y).
Proof. exact (SYM (@lem1709377 x y)). Qed.
Lemma lem1709381 (x : real) (h1 : term290 x) : term290 x.
Proof. exact (h1). Qed.
Lemma lem1709383 (x : real) : term29 x.
Proof. exact (EQ_MP (@lem1707733 x) (@lem1707732 x)). Qed.
Lemma lem1709384 (x : real) : term295 x.
Proof. exact (@lem1709383 (real_inv x)). Qed.
Lemma lem1709385 (x : real) (h1 : term290 x) : term296 x.
Proof. exact (@lem1709384 x (@lem1709381 x h1)). Qed.
Lemma lem1709386 (y : real) (x : real) (h1 : term290 x) : term297 x y.
Proof. exact (@lem1709385 x h1 (real_inv y)). Qed.
Lemma lem1709387 (y : real) (x : real) : (term297 x y) = (term298 y x).
Proof. exact (eq_refl (term297 x y)). Qed.
Lemma lem1709388 (y : real) (x : real) (h1 : term290 x) : term298 y x.
Proof. exact (EQ_MP (@lem1709387 y x) (@lem1709386 y x h1)). Qed.
Lemma lem1709390 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term16 A P Q.
Proof. exact (@lem1707716 A P Q (@lem7401 A P Q)). Qed.
Lemma lem1709391 (P : nat -> Prop) (Q : nat -> Prop) : term299 P Q.
Proof. exact (@lem1709390 nat P Q). Qed.
Lemma lem1709392 (x : real) (y : real) : term300 x y.
Proof. exact (@lem1709391 (term301 y x) (term97 x y)). Qed.
Lemma lem1709393 (y : real) (x : real) (n : nat) : (term302 y x n) = (term303 y x n).
Proof. exact (eq_refl (term302 y x n)). Qed.
Lemma lem1709394 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1709395 (y : real) (x : real) (n : nat) : (term304 y x n) = (term305 y x n).
Proof. exact (MK_COMB (@lem1709394) (@lem1709393 y x n)). Qed.
Lemma lem1709396 (x : real) (n : nat) (y : real) : (term101 x y n) = (term96 x n y).
Proof. exact (eq_refl (term101 x y n)). Qed.
Lemma lem1709397 (x : real) (n : nat) (y : real) : (term306 x y n) = (term307 x n y).
Proof. exact (MK_COMB (@lem1709395 y x n) (@lem1709396 x n y)). Qed.
Lemma lem1709398 (x : real) (y : real) : (term308 x y) = (term309 x y).
Proof. exact (fun_ext (fun n : nat => @lem1709397 x n y)). Qed.
Lemma lem1709399 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1709400 (x : real) (y : real) : (term310 x y) = (term311 x y).
Proof. exact (MK_COMB (@lem1709399) (@lem1709398 x y)). Qed.
Lemma lem1709401 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1709402 (x : real) (y : real) : (term312 x y) = (term313 x y).
Proof. exact (MK_COMB (@lem1709401) (@lem1709400 x y)). Qed.
Lemma lem1709403 (y : real) (x : real) (n : nat) : (term302 y x n) = (term303 y x n).
Proof. exact (eq_refl (term302 y x n)). Qed.
Lemma lem1709404 (y : real) (x : real) : (term314 y x) = (term301 y x).
Proof. exact (fun_ext (fun n : nat => @lem1709403 y x n)). Qed.
Lemma lem1709405 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1709406 (y : real) (x : real) : (term315 y x) = (term298 y x).
Proof. exact (MK_COMB (@lem1709405) (@lem1709404 y x)). Qed.
Lemma lem1709407 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1709408 (y : real) (x : real) : (term316 y x) = (term317 y x).
Proof. exact (MK_COMB (@lem1709407) (@lem1709406 y x)). Qed.
Lemma lem1709409 (x : real) (n : nat) (y : real) : (term101 x y n) = (term96 x n y).
Proof. exact (eq_refl (term101 x y n)). Qed.
Lemma lem1709410 (x : real) (y : real) : (term318 x y) = (term97 x y).
Proof. exact (fun_ext (fun n : nat => @lem1709409 x n y)). Qed.
Lemma lem1709411 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1709412 (x : real) (y : real) : (term319 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1709411) (@lem1709410 x y)). Qed.
Lemma lem1709413 (x : real) (y : real) : (term320 x y) = (term321 x y).
Proof. exact (MK_COMB (@lem1709408 y x) (@lem1709412 x y)). Qed.
Lemma lem1709414 (x : real) (y : real) : (term300 x y) = (term322 x y).
Proof. exact (MK_COMB (@lem1709402 x y) (@lem1709413 x y)). Qed.
Lemma lem1709415 (x : real) (y : real) : term322 x y.
Proof. exact (EQ_MP (@lem1709414 x y) (@lem1709392 x y)). Qed.
Lemma lem1709416 (y : real) (x : real) (n : nat) (h1 : term303 y x n) : term303 y x n.
Proof. exact (h1). Qed.
Lemma lem1709418 (x : real) : x = (term10 x).
Proof. exact (EQ_MP (@lem1707707 x) (@lem1707706 x)). Qed.
Lemma lem1709419 (y : real) : y = (term10 y).
Proof. exact (@lem1709418 y). Qed.
Lemma lem1709421 (x : real) : x = (term10 x).
Proof. exact (EQ_MP (@lem1707707 x) (@lem1707706 x)). Qed.
Lemma lem1709422 (x : real) (n : nat) : (real_pow x n) = (term323 x n).
Proof. exact (@lem1709421 (real_pow x n)). Qed.
Lemma lem1709423 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1709424 (x : real) (n : nat) : (term324 x n) = (term325 x n).
Proof. exact (MK_COMB (@lem1709423) (@lem1709422 x n)). Qed.
Lemma lem1709425 (x : real) (n : nat) (y : real) : (term96 x n y) = (term326 x n y).
Proof. exact (MK_COMB (@lem1709424 x n) (@lem1709419 y)). Qed.
Lemma lem1709426 (x : real) (n : nat) (y : real) : (term326 x n y) = (term96 x n y).
Proof. exact (SYM (@lem1709425 x n y)). Qed.
Lemma lem1709427 (x : real) : term276 x.
Proof. exact (@lem1632194 x). Qed.
Lemma lem1709428 (x : real) : (term276 x) = (term277 x).
Proof. exact (eq_refl (term276 x)). Qed.
Lemma lem1709429 (x : real) : term277 x.
Proof. exact (EQ_MP (@lem1709428 x) (@lem1709427 x)). Qed.
Lemma lem1709430 (x : real) (y : real) : term278 x y.
Proof. exact (@lem1709429 x y). Qed.
Lemma lem1709431 (y : real) (x : real) : (term278 x y) = (term279 y x).
Proof. exact (eq_refl (term278 x y)). Qed.
Lemma lem1709432 (y : real) (x : real) : term279 y x.
Proof. exact (EQ_MP (@lem1709431 y x) (@lem1709430 x y)). Qed.
Lemma lem1709433 (x : real) (y : real) (h1 : term280 x y) : term280 x y.
Proof. exact (h1). Qed.
Lemma lem1709434 (x : real) (y : real) (h1 : term280 x y) : term281 y x.
Proof. exact (@lem1709432 y x (@lem1709433 x y h1)). Qed.
Lemma lem1709435 (y : real) (x : real) : (term281 y x) = ((term281 y x) = True).
Proof. exact (@lem7 (term281 y x)). Qed.
Lemma lem1709436 (x : real) (y : real) (h1 : term280 x y) : (term281 y x) = True.
Proof. exact (EQ_MP (@lem1709435 y x) (@lem1709434 x y h1)). Qed.
Lemma lem1709442 (x : real) : term327 x.
Proof. exact (@lem1589984 x). Qed.
Lemma lem1709443 (x : real) : (term327 x) = (term328 x).
Proof. exact (eq_refl (term327 x)). Qed.
Lemma lem1709444 (x : real) : term328 x.
Proof. exact (EQ_MP (@lem1709443 x) (@lem1709442 x)). Qed.
Lemma lem1709445 (x : real) (h1 : term41 x) : term41 x.
Proof. exact (h1). Qed.
Lemma lem1709446 (x : real) (h1 : term41 x) : term329 x.
Proof. exact (@lem1709444 x (@lem1709445 x h1)). Qed.
Lemma lem1709447 (x : real) : (term329 x) = ((term329 x) = True).
Proof. exact (@lem7 (term329 x)). Qed.
Lemma lem1709448 (x : real) (h1 : term41 x) : (term329 x) = True.
Proof. exact (EQ_MP (@lem1709447 x) (@lem1709446 x h1)). Qed.
Lemma lem1709454 (x : real) : term330 x.
Proof. exact (@lem1707695 x). Qed.
Lemma lem1709455 (x : real) : (term330 x) = (term5 x).
Proof. exact (eq_refl (term330 x)). Qed.
Lemma lem1709456 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem1709455 x) (@lem1709454 x)). Qed.
Lemma lem1709457 (x : real) (n : nat) : term331 x n.
Proof. exact (@lem1709456 x n). Qed.
Lemma lem1709458 (x : real) (n : nat) : (term331 x n) = ((term1 x n) = (term0 x n)).
Proof. exact (eq_refl (term331 x n)). Qed.
Lemma lem1709460 (y : real) : (term41 y) = ((term41 y) = True).
Proof. exact (@lem7 (term41 y)). Qed.
Lemma lem1709466 (y : real) (x : real) (n : nat) : (term303 y x n) = ((term303 y x n) = True).
Proof. exact (@lem7 (term303 y x n)). Qed.
Lemma lem1709469 (y : real) (x : real) : term282 y x.
Proof. exact (fun h0 : term280 x y => @lem1709436 x y h0). Qed.
Lemma lem1709470 (x : real) (n : nat) (y : real) : term332 x n y.
Proof. exact (@lem1709469 (term1 x n) (real_inv y)). Qed.
Lemma lem1709474 (x : real) : term333 x.
Proof. exact (fun h0 : term41 x => @lem1709448 x h0). Qed.
Lemma lem1709475 (y : real) : term333 y.
Proof. exact (@lem1709474 y). Qed.
Lemma lem1709477 (y : real) (h1 : term41 y) : (term41 y) = True.
Proof. exact (EQ_MP (@lem1709460 y) (@lem1707752 y h1)). Qed.
Lemma lem1709478 (y : real) (h1 : term41 y) : True = (term41 y).
Proof. exact (SYM (@lem1709477 y h1)). Qed.
Lemma lem1709479 (y : real) (h1 : term41 y) : term41 y.
Proof. exact (EQ_MP (@lem1709478 y h1) (@lem0)). Qed.
Lemma lem1709480 (y : real) (h1 : term41 y) : (term329 y) = True.
Proof. exact (@lem1709475 y (@lem1709479 y h1)). Qed.
Lemma lem1709481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1709482 (y : real) (h1 : term41 y) : (term334 y) = (and True).
Proof. exact (MK_COMB (@lem1709481) (@lem1709480 y h1)). Qed.
Lemma lem1709491 (x : real) (n : nat) : (term1 x n) = (term0 x n).
Proof. exact (EQ_MP (@lem1709458 x n) (@lem1709457 x n)). Qed.
Lemma lem1709492 (y : real) : (term335 y) = (term335 y).
Proof. exact (eq_refl (term335 y)). Qed.
Lemma lem1709493 (y : real) (x : real) (n : nat) : (term336 y x n) = (term303 y x n).
Proof. exact (MK_COMB (@lem1709492 y) (@lem1709491 x n)). Qed.
Lemma lem1709495 (y : real) (x : real) (n : nat) (h1 : term303 y x n) : (term303 y x n) = True.
Proof. exact (EQ_MP (@lem1709466 y x n) (@lem1709416 y x n h1)). Qed.
Lemma lem1709496 (y : real) (x : real) (n : nat) (h1 : term303 y x n) : (term336 y x n) = True.
Proof. exact (TRANS (@lem1709493 y x n) (@lem1709495 y x n h1)). Qed.
Lemma lem1709497 (x : real) (n : nat) (y : real) (h1 : term303 y x n) (h2 : term41 y) : (term337 y x n) = (True /\ True).
Proof. exact (MK_COMB (@lem1709482 y h2) (@lem1709496 y x n h1)). Qed.
Lemma lem1709499 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1709500 : (True /\ True) = True.
Proof. exact (@lem1709499 True). Qed.
Lemma lem1709501 (x : real) (n : nat) (y : real) (h1 : term303 y x n) (h2 : term41 y) : (term337 y x n) = True.
Proof. exact (TRANS (@lem1709497 x n y h1 h2) (@lem1709500)). Qed.
Lemma lem1709502 (x : real) (n : nat) (y : real) (h1 : term303 y x n) (h2 : term41 y) : True = (term337 y x n).
Proof. exact (SYM (@lem1709501 x n y h1 h2)). Qed.
Lemma lem1709503 (x : real) (n : nat) (y : real) (h1 : term303 y x n) (h2 : term41 y) : term337 y x n.
Proof. exact (EQ_MP (@lem1709502 x n y h1 h2) (@lem0)). Qed.
Lemma lem1709504 (x : real) (n : nat) (y : real) (h1 : term303 y x n) (h2 : term41 y) : (term326 x n y) = True.
Proof. exact (@lem1709470 x n y (@lem1709503 x n y h1 h2)). Qed.
Lemma lem1709505 (x : real) (n : nat) (y : real) (h1 : term303 y x n) (h2 : term41 y) : True = (term326 x n y).
Proof. exact (SYM (@lem1709504 x n y h1 h2)). Qed.
Lemma lem1709506 (x : real) (n : nat) (y : real) (h1 : term303 y x n) (h2 : term41 y) : term326 x n y.
Proof. exact (EQ_MP (@lem1709505 x n y h1 h2) (@lem0)). Qed.
Lemma lem1709507 (x : real) (n : nat) (y : real) (h1 : term303 y x n) (h2 : term41 y) : term96 x n y.
Proof. exact (EQ_MP (@lem1709426 x n y) (@lem1709506 x n y h1 h2)). Qed.
Lemma lem1709508 (x : real) (n : nat) (y : real) (h1 : term41 y) : term307 x n y.
Proof. exact (fun h0 : term303 y x n => @lem1709507 x n y h0 h1). Qed.
Lemma lem1709513 (x : real) (y : real) (h1 : term41 y) : term311 x y.
Proof. exact (fun n : nat => @lem1709508 x n y h1). Qed.
Lemma lem1709514 (x : real) (y : real) (h1 : term41 y) : term321 x y.
Proof. exact (@lem1709415 x y (@lem1709513 x y h1)). Qed.
Lemma lem1709515 (y : real) (x : real) (h1 : term41 y) (h2 : term290 x) : term47 x y.
Proof. exact (@lem1709514 x y h1 (@lem1709388 y x h2)). Qed.
Lemma lem1709516 (x : real) (y : real) (h1 : term41 y) : term294 x y.
Proof. exact (fun h0 : term290 x => @lem1709515 y x h1 h0). Qed.
Lemma lem1709517 (x : real) (y : real) (h1 : term41 y) : term293 x y.
Proof. exact (EQ_MP (@lem1709380 x y) (@lem1709516 x y h1)). Qed.
Lemma lem1709518 (x : real) (y : real) (h1 : term275 x) (h2 : term41 y) : term47 x y.
Proof. exact (@lem1709517 x y h2 (@lem1709319 x h1)). Qed.
Lemma lem1709519 (x : real) (y : real) (h1 : term45 x) (h2 : term41 x) (h3 : term41 y) : (term275 x) = (term47 x y).
Proof. exact (prop_ext (fun h4 : term275 x => @lem1709518 x y h4 h3) (fun h4 : term47 x y => @lem1709361 x h1 h2)). Qed.
Lemma lem1709520 (x : real) (y : real) (h1 : term45 x) (h2 : term41 x) (h3 : term41 y) : term47 x y.
Proof. exact (EQ_MP (@lem1709519 x y h1 h2 h3) (@lem1709361 x h1 h2)). Qed.
Lemma lem1709521 (x : real) (y : real) (h1 : term45 x) (h2 : term41 y) : term47 x y.
Proof. exact (or_elim (@lem1707747 x) (fun h0 : term41 x => @lem1709520 x y h1 h0 h2) (fun h0 : term43 x => @lem1709318 x y h0 h1 h2)). Qed.
Lemma lem1709522 (y : real) (x : real) (h1 : term44 y x) : term45 x.
Proof. exact (proj2 (@lem1707750 y x h1)). Qed.
Lemma lem1709523 (y : real) (x : real) (h1 : term44 y x) : term41 y.
Proof. exact (proj1 (@lem1707750 y x h1)). Qed.
Lemma lem1709524 (x : real) (y : real) (h1 : term45 x) (h2 : term41 y) : (term45 x) = (term47 x y).
Proof. exact (prop_ext (fun h3 : term45 x => @lem1709521 x y h1 h2) (fun h3 : term47 x y => @lem1707751 x h1)). Qed.
Lemma lem1709525 (x : real) (y : real) (h1 : term45 x) (h2 : term41 y) : term47 x y.
Proof. exact (EQ_MP (@lem1709524 x y h1 h2) (@lem1707751 x h1)). Qed.
Lemma lem1709526 (x : real) (y : real) (h1 : term45 x) (h2 : term41 y) : (term41 y) = (term47 x y).
Proof. exact (prop_ext (fun h3 : term41 y => @lem1709525 x y h1 h2) (fun h3 : term47 x y => @lem1707752 y h2)). Qed.
Lemma lem1709527 (x : real) (y : real) (h1 : term45 x) (h2 : term41 y) : term47 x y.
Proof. exact (EQ_MP (@lem1709526 x y h1 h2) (@lem1707752 y h2)). Qed.
Lemma lem1709528 (x : real) (y : real) (h1 : term44 y x) (h2 : term41 y) : (term45 x) = (term47 x y).
Proof. exact (prop_ext (fun h3 : term45 x => @lem1709527 x y h3 h2) (fun h3 : term47 x y => @lem1709522 y x h1)). Qed.
Lemma lem1709529 (x : real) (y : real) (h1 : term44 y x) (h2 : term41 y) : term47 x y.
Proof. exact (EQ_MP (@lem1709528 x y h1 h2) (@lem1709522 y x h1)). Qed.
Lemma lem1709530 (y : real) (x : real) (h1 : term44 y x) : (term41 y) = (term47 x y).
Proof. exact (prop_ext (fun h2 : term41 y => @lem1709529 x y h1 h2) (fun h2 : term47 x y => @lem1709523 y x h1)). Qed.
Lemma lem1709531 (y : real) (x : real) (h1 : term44 y x) : term47 x y.
Proof. exact (EQ_MP (@lem1709530 y x h1) (@lem1709523 y x h1)). Qed.
Lemma lem1709532 (x : real) (y : real) : term338 x y.
Proof. exact (fun h0 : term44 y x => @lem1709531 y x h0). Qed.
Lemma lem1709537 (x : real) : term339 x.
Proof. exact (fun y : real => @lem1709532 x y). Qed.
Lemma lem1709542 : term340.
Proof. exact (fun x : real => @lem1709537 x). Qed.
