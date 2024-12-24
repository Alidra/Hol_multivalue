Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_UNION_OF_INTER_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_UNION_OF_INC_spec.
Require Import FINITE_UNION_OF_UNIONS_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import INTER_UNIONS_spec.
Require Import SIMPLE_IMAGE_spec.
Require Import UNION_OF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem4887667 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4887668 {A : Type'} (P : type686 A) (h1 : term0 A) : term1 A P.
Proof. exact (@lem4887667 A h1 P). Qed.
Lemma lem4887669 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem4887670 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem4887669 A P) (@lem4887668 A P h1)). Qed.
Lemma lem4887671 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term0 A) : term3 A P u.
Proof. exact (@lem4887670 A P h1 u). Qed.
Lemma lem4887672 {A : Type'} (P : type686 A) (u : type686 A) : (term3 A P u) = (term4 A P u).
Proof. exact (eq_refl (term3 A P u)). Qed.
Lemma lem4887673 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term0 A) : term4 A P u.
Proof. exact (EQ_MP (@lem4887672 A P u) (@lem4887671 A P u h1)). Qed.
Lemma lem4887674 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term5 A u P) : term5 A u P.
Proof. exact (h1). Qed.
Lemma lem4887675 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term0 A) (h2 : term5 A u P) : term6 A P u.
Proof. exact (@lem4887673 A P u h1 (@lem4887674 A u P h2)). Qed.
Lemma lem4887676 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term5 A u P) : term7 A P u.
Proof. exact (fun h0 : term0 A => @lem4887675 A u P h0 h1). Qed.
Lemma lem4887677 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4887678 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term0 A) (h2 : term5 A u P) : term6 A P u.
Proof. exact (@lem4887676 A u P h2 (@lem4887677 A h1)). Qed.
Lemma lem4887679 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term0 A) : term4 A P u.
Proof. exact (fun h0 : term5 A u P => @lem4887678 A u P h1 h0). Qed.
Lemma lem4887680 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (fun u : type686 A => @lem4887679 A P u h1). Qed.
Lemma lem4887681 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : type686 A => @lem4887680 A P h1). Qed.
Lemma lem4887682 {A : Type'} : term8 A.
Proof. exact (fun h0 : term0 A => @lem4887681 A h0). Qed.
Lemma lem4887683 {A : Type'} : term0 A.
Proof. exact (@lem4887682 A (@lem4887037 A)). Qed.
Lemma lem4887684 {A : Type'} (P : type686 A) : term1 A P.
Proof. exact (@lem4887683 A P). Qed.
Lemma lem4887685 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem4887686 {A : Type'} (P : type686 A) : term2 A P.
Proof. exact (EQ_MP (@lem4887685 A P) (@lem4887684 A P)). Qed.
Lemma lem4887687 {A : Type'} (P : type686 A) (u : type686 A) : term3 A P u.
Proof. exact (@lem4887686 A P u). Qed.
Lemma lem4887688 {A : Type'} (P : type686 A) (u : type686 A) : (term3 A P u) = (term4 A P u).
Proof. exact (eq_refl (term3 A P u)). Qed.
Lemma lem4887690 {A : Type'} (P : type180 A) : term9 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4887691 {A : Type'} (P : type180 A) : (term9 A P) = (term10 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem4887692 {A : Type'} (P : type180 A) : term10 A P.
Proof. exact (EQ_MP (@lem4887691 A P) (@lem4887690 A P)). Qed.
Lemma lem4887693 {A : Type'} (P : type180 A) (Q : type686 A) : term11 A P Q.
Proof. exact (@lem4887692 A P Q). Qed.
Lemma lem4887694 {A : Type'} (P : type180 A) (Q : type686 A) : (term11 A P Q) = ((@UNION_OF A P Q) = (term12 A P Q)).
Proof. exact (eq_refl (term11 A P Q)). Qed.
Lemma lem4887696 (t1 : Prop) : term13 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4887697 (t1 : Prop) : (term13 t1) = (term14 t1).
Proof. exact (eq_refl (term13 t1)). Qed.
Lemma lem4887698 (t1 : Prop) : term14 t1.
Proof. exact (EQ_MP (@lem4887697 t1) (@lem4887696 t1)). Qed.
Lemma lem4887699 (t1 : Prop) (t2 : Prop) : term15 t1 t2.
Proof. exact (@lem4887698 t1 t2). Qed.
Lemma lem4887700 (t1 : Prop) (t2 : Prop) : (term15 t1 t2) = (term16 t1 t2).
Proof. exact (eq_refl (term15 t1 t2)). Qed.
Lemma lem4887701 (t1 : Prop) (t2 : Prop) : term16 t1 t2.
Proof. exact (EQ_MP (@lem4887700 t1 t2) (@lem4887699 t1 t2)). Qed.
Lemma lem4887702 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term17 t1 t2 t3.
Proof. exact (@lem4887701 t1 t2 t3). Qed.
Lemma lem4887703 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = ((term18 t1 t2 t3) = (term19 t1 t2 t3)).
Proof. exact (eq_refl (term17 t1 t2 t3)). Qed.
Lemma lem4887704 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term18 t1 t2 t3) = (term19 t1 t2 t3).
Proof. exact (EQ_MP (@lem4887703 t1 t2 t3) (@lem4887702 t1 t2 t3)). Qed.
Lemma lem4887705 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term19 t1 t2 t3) = (term18 t1 t2 t3).
Proof. exact (SYM (@lem4887704 t1 t2 t3)). Qed.
Lemma lem4887707 (p : Prop) : p = (term20 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4887708 {A : Type'} (P : type686 A) : (term21 A P) = (term22 A P).
Proof. exact (@lem4887707 (term21 A P)). Qed.
Lemma lem4887709 {A : Type'} (P : type686 A) : (term22 A P) = (term21 A P).
Proof. exact (SYM (@lem4887708 A P)). Qed.
Lemma lem4887710 {A : Type'} (P : type686 A) (h1 : term23 A P) : term23 A P.
Proof. exact (h1). Qed.
Lemma lem4887711 {A : Type'} : term24 A.
Proof. exact (@lem4876798 A). Qed.
Lemma lem4887715 {A : Type'} (P : type686 A) (h1 : term25 A P) : term25 A P.
Proof. exact (h1). Qed.
Lemma lem4887716 {A : Type'} (P : type686 A) : term26 A P.
Proof. exact (fun h0 : term25 A P => @lem4887715 A P h0). Qed.
Lemma lem4887717 {A : Type'} (P : type686 A) (h1 : term26 A P) : term26 A P.
Proof. exact (h1). Qed.
Lemma lem4887718 {A : Type'} (P : type686 A) (h1 : term25 A P) : term25 A P.
Proof. exact (h1). Qed.
Lemma lem4887719 {A : Type'} (P : type686 A) (h1 : term25 A P) (h2 : term26 A P) : term25 A P.
Proof. exact (@lem4887717 A P h2 (@lem4887718 A P h1)). Qed.
Lemma lem4887720 {A : Type'} (P : type686 A) (h1 : term25 A P) : term27 A P.
Proof. exact (fun h0 : term26 A P => @lem4887719 A P h1 h0). Qed.
Lemma lem4887721 {A : Type'} (P : type686 A) (h1 : term26 A P) : term26 A P.
Proof. exact (h1). Qed.
Lemma lem4887722 {A : Type'} (P : type686 A) (h1 : term25 A P) (h2 : term26 A P) : term25 A P.
Proof. exact (@lem4887720 A P h1 (@lem4887721 A P h2)). Qed.
Lemma lem4887723 {A : Type'} (P : type686 A) (h1 : term26 A P) : term26 A P.
Proof. exact (fun h0 : term25 A P => @lem4887722 A P h0 h1). Qed.
Lemma lem4887724 {A : Type'} (P : type686 A) : term28 A P.
Proof. exact (fun h0 : term26 A P => @lem4887723 A P h0). Qed.
Lemma lem4887727 {A : Type'} (P : type686 A) : term26 A P.
Proof. exact (@lem4887724 A P (@lem4887716 A P)). Qed.
Lemma lem4887728 {A : Type'} (P : type686 A) : term26 A P.
Proof. exact (@lem4887727 A P). Qed.
Lemma lem4887762 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4887763 {A : Type'} : (term29 A) = (term30 A).
Proof. exact (@lem4887762 (term24 A)). Qed.
Lemma lem4887774 {A : Type'} (P : type686 A) : (term31 A P) = (term31 A P).
Proof. exact (eq_refl (term31 A P)). Qed.
Lemma lem4887775 {A : Type'} (P : type686 A) : (term25 A P) = (term32 A P).
Proof. exact (MK_COMB (@lem4887774 A P) (@lem4887763 A)). Qed.
Lemma lem4887778 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4887775 A P)). Qed.
Lemma lem4887779 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4887788 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (MK_COMB (@lem4887779 A) (@lem4887778 A)). Qed.
Lemma lem4887793 {A : Type'} (P : type686 A) (s : A -> Prop) : (term37 A P s) = (term37 A P s).
Proof. exact (eq_refl (term37 A P s)). Qed.
Lemma lem4887794 {A : Type'} (P : type686 A) : (term38 A P) = (term38 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4887793 A P s)). Qed.
Lemma lem4887795 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4887796 {A : Type'} (P : type686 A) : (term39 A P) = (term39 A P).
Proof. exact (MK_COMB (@lem4887795 A) (@lem4887794 A P)). Qed.
Lemma lem4887797 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4887796 A P)). Qed.
Lemma lem4887798 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4887799 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (MK_COMB (@lem4887798 A) (@lem4887797 A)). Qed.
Lemma lem4887800 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4887801 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (MK_COMB (@lem4887800) (@lem4887799 A)). Qed.
Lemma lem4887810 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term41 A P s t) = (term41 A P s t).
Proof. exact (eq_refl (term41 A P s t)). Qed.
Lemma lem4887811 {A : Type'} (P : type686 A) (s : A -> Prop) : (term42 A P s) = (term42 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4887810 A P s t)). Qed.
Lemma lem4887812 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4887813 {A : Type'} (P : type686 A) (s : A -> Prop) : (term43 A P s) = (term43 A P s).
Proof. exact (MK_COMB (@lem4887812 A) (@lem4887811 A P s)). Qed.
Lemma lem4887814 {A : Type'} (P : type686 A) : (term44 A P) = (term44 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4887813 A P s)). Qed.
Lemma lem4887815 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4887816 {A : Type'} (P : type686 A) : (term45 A P) = (term45 A P).
Proof. exact (MK_COMB (@lem4887815 A) (@lem4887814 A P)). Qed.
Lemma lem4887825 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term46 A P s t) = (term46 A P s t).
Proof. exact (eq_refl (term46 A P s t)). Qed.
Lemma lem4887826 {A : Type'} (P : type686 A) (s : A -> Prop) : (term47 A P s) = (term47 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4887825 A P s t)). Qed.
Lemma lem4887827 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4887828 {A : Type'} (P : type686 A) (s : A -> Prop) : (term48 A P s) = (term48 A P s).
Proof. exact (MK_COMB (@lem4887827 A) (@lem4887826 A P s)). Qed.
Lemma lem4887829 {A : Type'} (P : type686 A) : (term49 A P) = (term49 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4887828 A P s)). Qed.
Lemma lem4887830 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4887831 {A : Type'} (P : type686 A) : (term50 A P) = (term50 A P).
Proof. exact (MK_COMB (@lem4887830 A) (@lem4887829 A P)). Qed.
Lemma lem4887832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4887833 {A : Type'} (P : type686 A) : (term51 A P) = (term51 A P).
Proof. exact (MK_COMB (@lem4887832) (@lem4887831 A P)). Qed.
Lemma lem4887834 {A : Type'} (P : type686 A) : (term21 A P) = (term21 A P).
Proof. exact (MK_COMB (@lem4887833 A P) (@lem4887816 A P)). Qed.
Lemma lem4887835 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4887836 {A : Type'} (P : type686 A) : (term23 A P) = (term23 A P).
Proof. exact (MK_COMB (@lem4887835) (@lem4887834 A P)). Qed.
Lemma lem4887837 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4887838 {A : Type'} (P : type686 A) : (term31 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem4887837) (@lem4887836 A P)). Qed.
Lemma lem4887839 {A : Type'} (P : type686 A) : (term32 A P) = (term32 A P).
Proof. exact (MK_COMB (@lem4887838 A P) (@lem4887801 A)). Qed.
Lemma lem4887840 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4887839 A P)). Qed.
Lemma lem4887841 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4887842 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem4887841 A) (@lem4887840 A)). Qed.
Lemma lem4887901 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (TRANS (@lem4887788 A) (@lem4887842 A)). Qed.
Lemma lem4887902 {A : Type'} : (term36 A) = (term35 A).
Proof. exact (SYM (@lem4887901 A)). Qed.
Lemma lem4887903 {A : Type'} (P : type686 A) (h1 : term23 A P) : term23 A P.
Proof. exact (h1). Qed.
Lemma lem4887904 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem4887911 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term52 A s P t) = (term53 A s P t).
Proof. exact (@lem17045 (@UNION_OF A (@FINITE (A -> Prop)) P s) (@UNION_OF A (@FINITE (A -> Prop)) P t)). Qed.
Lemma lem4887912 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term54 A P s t).
Proof. exact (eq_refl (term54 A P s t)). Qed.
Lemma lem4887913 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4887914 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term55 A s P t) = (term56 A s P t).
Proof. exact (MK_COMB (@lem4887913) (@lem4887911 A s P t)). Qed.
Lemma lem4887915 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term57 A P s t) = (term58 A P s t).
Proof. exact (MK_COMB (@lem4887914 A s P t) (@lem4887912 A P s t)). Qed.
Lemma lem4887916 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term46 A P s t) = (term57 A P s t).
Proof. exact (@lem17265 (term59 A s P t) (term54 A P s t)). Qed.
Lemma lem4887917 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term46 A P s t) = (term58 A P s t).
Proof. exact (TRANS (@lem4887916 A P s t) (@lem4887915 A P s t)). Qed.
Lemma lem4887918 {A : Type'} (P : type686 A) (s : A -> Prop) : (term47 A P s) = (term60 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4887917 A P s t)). Qed.
Lemma lem4887919 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4887920 {A : Type'} (P : type686 A) (s : A -> Prop) : (term48 A P s) = (term61 A P s).
Proof. exact (MK_COMB (@lem4887919 A) (@lem4887918 A P s)). Qed.
Lemma lem4887921 {A : Type'} (P : type686 A) : (term49 A P) = (term62 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4887920 A P s)). Qed.
Lemma lem4887922 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4887923 {A : Type'} (P : type686 A) : (term50 A P) = (term63 A P).
Proof. exact (MK_COMB (@lem4887922 A) (@lem4887921 A P)). Qed.
Lemma lem4887934 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term64 A P s t) = (term65 A P s t).
Proof. exact (@lem17362 (term66 A s P t) (term54 A P s t)). Qed.
Lemma lem4887935 {A : Type'} (P : type686 A) : (term67 A P) = (term68 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4887936 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term70 A P s).
Proof. exact (@lem4887935 A (term42 A P s)). Qed.
Lemma lem4887937 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term71 A P s t) = (term41 A P s t).
Proof. exact (eq_refl (term71 A P s t)). Qed.
Lemma lem4887938 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4887939 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term72 A P s t) = (term64 A P s t).
Proof. exact (MK_COMB (@lem4887938) (@lem4887937 A P s t)). Qed.
Lemma lem4887940 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term72 A P s t) = (term65 A P s t).
Proof. exact (TRANS (@lem4887939 A P s t) (@lem4887934 A P s t)). Qed.
Lemma lem4887941 {A : Type'} (P : type686 A) (s : A -> Prop) : (term73 A P s) = (term74 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4887940 A P s t)). Qed.
Lemma lem4887942 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4887943 {A : Type'} (P : type686 A) (s : A -> Prop) : (term70 A P s) = (term75 A P s).
Proof. exact (MK_COMB (@lem4887942 A) (@lem4887941 A P s)). Qed.
Lemma lem4887944 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term75 A P s).
Proof. exact (TRANS (@lem4887936 A P s) (@lem4887943 A P s)). Qed.
Lemma lem4887945 {A : Type'} (P : type686 A) : (term67 A P) = (term68 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4887946 {A : Type'} (P : type686 A) : (term76 A P) = (term77 A P).
Proof. exact (@lem4887945 A (term44 A P)). Qed.
Lemma lem4887947 {A : Type'} (P : type686 A) (s : A -> Prop) : (term78 A P s) = (term43 A P s).
Proof. exact (eq_refl (term78 A P s)). Qed.
Lemma lem4887948 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4887949 {A : Type'} (P : type686 A) (s : A -> Prop) : (term79 A P s) = (term69 A P s).
Proof. exact (MK_COMB (@lem4887948) (@lem4887947 A P s)). Qed.
Lemma lem4887950 {A : Type'} (P : type686 A) (s : A -> Prop) : (term79 A P s) = (term75 A P s).
Proof. exact (TRANS (@lem4887949 A P s) (@lem4887944 A P s)). Qed.
Lemma lem4887951 {A : Type'} (P : type686 A) : (term80 A P) = (term81 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4887950 A P s)). Qed.
Lemma lem4887952 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4887953 {A : Type'} (P : type686 A) : (term77 A P) = (term82 A P).
Proof. exact (MK_COMB (@lem4887952 A) (@lem4887951 A P)). Qed.
Lemma lem4887954 {A : Type'} (P : type686 A) : (term76 A P) = (term82 A P).
Proof. exact (TRANS (@lem4887946 A P) (@lem4887953 A P)). Qed.
Lemma lem4887955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887956 {A : Type'} (P : type686 A) : (term83 A P) = (term84 A P).
Proof. exact (MK_COMB (@lem4887955) (@lem4887923 A P)). Qed.
Lemma lem4887957 {A : Type'} (P : type686 A) : (term85 A P) = (term86 A P).
Proof. exact (MK_COMB (@lem4887956 A P) (@lem4887954 A P)). Qed.
Lemma lem4887958 {A : Type'} (P : type686 A) : (term23 A P) = (term85 A P).
Proof. exact (@lem17362 (term50 A P) (term45 A P)). Qed.
Lemma lem4887959 {A : Type'} (P : type686 A) : (term23 A P) = (term86 A P).
Proof. exact (TRANS (@lem4887958 A P) (@lem4887957 A P)). Qed.
Lemma lem4888066 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4888067 {A : Type'} (P : Prop) (Q : type686 A) : (term89 A P Q) = (term90 A P Q).
Proof. exact (@lem4888066 (A -> Prop) P Q). Qed.
Lemma lem4888068 {A : Type'} (P : type686 A) : (term91 A P) = (term92 A P).
Proof. exact (@lem4888067 A (term63 A P) (term81 A P)). Qed.
Lemma lem4888069 {A : Type'} (P : type686 A) (s : A -> Prop) : (term93 A P s) = (term75 A P s).
Proof. exact (eq_refl (term93 A P s)). Qed.
Lemma lem4888070 {A : Type'} (P : type686 A) : (term94 A P) = (term81 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4888069 A P s)). Qed.
Lemma lem4888071 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4888072 {A : Type'} (P : type686 A) : (term95 A P) = (term82 A P).
Proof. exact (MK_COMB (@lem4888071 A) (@lem4888070 A P)). Qed.
Lemma lem4888073 {A : Type'} (P : type686 A) : (term84 A P) = (term84 A P).
Proof. exact (eq_refl (term84 A P)). Qed.
Lemma lem4888074 {A : Type'} (P : type686 A) : (term91 A P) = (term86 A P).
Proof. exact (MK_COMB (@lem4888073 A P) (@lem4888072 A P)). Qed.
Lemma lem4888075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4888076 {A : Type'} (P : type686 A) : (term96 A P) = (term97 A P).
Proof. exact (MK_COMB (@lem4888075) (@lem4888074 A P)). Qed.
Lemma lem4888077 {A : Type'} (P : type686 A) (s : A -> Prop) : (term93 A P s) = (term75 A P s).
Proof. exact (eq_refl (term93 A P s)). Qed.
Lemma lem4888078 {A : Type'} (P : type686 A) : (term84 A P) = (term84 A P).
Proof. exact (eq_refl (term84 A P)). Qed.
Lemma lem4888079 {A : Type'} (P : type686 A) (s : A -> Prop) : (term98 A P s) = (term99 A P s).
Proof. exact (MK_COMB (@lem4888078 A P) (@lem4888077 A P s)). Qed.
Lemma lem4888080 {A : Type'} (P : type686 A) : (term100 A P) = (term101 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4888079 A P s)). Qed.
Lemma lem4888081 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4888082 {A : Type'} (P : type686 A) : (term92 A P) = (term102 A P).
Proof. exact (MK_COMB (@lem4888081 A) (@lem4888080 A P)). Qed.
Lemma lem4888083 {A : Type'} (P : type686 A) : ((term91 A P) = (term92 A P)) = ((term86 A P) = (term102 A P)).
Proof. exact (MK_COMB (@lem4888076 A P) (@lem4888082 A P)). Qed.
Lemma lem4888084 {A : Type'} (P : type686 A) : (term86 A P) = (term102 A P).
Proof. exact (EQ_MP (@lem4888083 A P) (@lem4888068 A P)). Qed.
Lemma lem4888086 {A : Type'} (P : Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4888087 {A : Type'} (P : Prop) (Q : type686 A) : (term89 A P Q) = (term90 A P Q).
Proof. exact (@lem4888086 (A -> Prop) P Q). Qed.
Lemma lem4888088 {A : Type'} (P : type686 A) (s : A -> Prop) : (term103 A P s) = (term104 A P s).
Proof. exact (@lem4888087 A (term63 A P) (term74 A P s)). Qed.
Lemma lem4888089 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term105 A P s t) = (term65 A P s t).
Proof. exact (eq_refl (term105 A P s t)). Qed.
Lemma lem4888090 {A : Type'} (P : type686 A) (s : A -> Prop) : (term106 A P s) = (term74 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4888089 A P s t)). Qed.
Lemma lem4888091 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4888092 {A : Type'} (P : type686 A) (s : A -> Prop) : (term107 A P s) = (term75 A P s).
Proof. exact (MK_COMB (@lem4888091 A) (@lem4888090 A P s)). Qed.
Lemma lem4888093 {A : Type'} (P : type686 A) : (term84 A P) = (term84 A P).
Proof. exact (eq_refl (term84 A P)). Qed.
Lemma lem4888094 {A : Type'} (P : type686 A) (s : A -> Prop) : (term103 A P s) = (term99 A P s).
Proof. exact (MK_COMB (@lem4888093 A P) (@lem4888092 A P s)). Qed.
Lemma lem4888095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4888096 {A : Type'} (P : type686 A) (s : A -> Prop) : (term108 A P s) = (term109 A P s).
Proof. exact (MK_COMB (@lem4888095) (@lem4888094 A P s)). Qed.
Lemma lem4888097 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term105 A P s t) = (term65 A P s t).
Proof. exact (eq_refl (term105 A P s t)). Qed.
Lemma lem4888098 {A : Type'} (P : type686 A) : (term84 A P) = (term84 A P).
Proof. exact (eq_refl (term84 A P)). Qed.
Lemma lem4888099 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term110 A P s t) = (term111 A P s t).
Proof. exact (MK_COMB (@lem4888098 A P) (@lem4888097 A P s t)). Qed.
Lemma lem4888100 {A : Type'} (P : type686 A) (s : A -> Prop) : (term112 A P s) = (term113 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4888099 A P s t)). Qed.
Lemma lem4888101 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4888102 {A : Type'} (P : type686 A) (s : A -> Prop) : (term104 A P s) = (term114 A P s).
Proof. exact (MK_COMB (@lem4888101 A) (@lem4888100 A P s)). Qed.
Lemma lem4888103 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term103 A P s) = (term104 A P s)) = ((term99 A P s) = (term114 A P s)).
Proof. exact (MK_COMB (@lem4888096 A P s) (@lem4888102 A P s)). Qed.
Lemma lem4888104 {A : Type'} (P : type686 A) (s : A -> Prop) : (term99 A P s) = (term114 A P s).
Proof. exact (EQ_MP (@lem4888103 A P s) (@lem4888088 A P s)). Qed.
Lemma lem4888105 {A : Type'} (P : type686 A) : (term101 A P) = (term115 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4888104 A P s)). Qed.
Lemma lem4888106 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4888107 {A : Type'} (P : type686 A) : (term102 A P) = (term116 A P).
Proof. exact (MK_COMB (@lem4888106 A) (@lem4888105 A P)). Qed.
Lemma lem4888109 {A : Type'} (P : type686 A) : (term86 A P) = (term116 A P).
Proof. exact (TRANS (@lem4888084 A P) (@lem4888107 A P)). Qed.
Lemma lem4888110 {A : Type'} (P : type686 A) : (term23 A P) = (term116 A P).
Proof. exact (TRANS (@lem4887959 A P) (@lem4888109 A P)). Qed.
Lemma lem4888111 {A : Type'} (P : type686 A) (h1 : term23 A P) : term116 A P.
Proof. exact (EQ_MP (@lem4888110 A P) (@lem4887903 A P h1)). Qed.
Lemma lem4888118 {A : Type'} (P : type686 A) (s : A -> Prop) : (term37 A P s) = (term117 A P s).
Proof. exact (@lem17265 (P s) (@UNION_OF A (@FINITE (A -> Prop)) P s)). Qed.
Lemma lem4888119 {A : Type'} (P : type686 A) : (term38 A P) = (term118 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4888118 A P s)). Qed.
Lemma lem4888120 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4888121 {A : Type'} (P : type686 A) : (term39 A P) = (term119 A P).
Proof. exact (MK_COMB (@lem4888120 A) (@lem4888119 A P)). Qed.
Lemma lem4888122 {A : Type'} : (term40 A) = (term120 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4888121 A P)). Qed.
Lemma lem4888123 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4888180 {A : Type'} : (term24 A) = (term121 A).
Proof. exact (MK_COMB (@lem4888123 A) (@lem4888122 A)). Qed.
Lemma lem4888181 {A : Type'} (h1 : term24 A) : term121 A.
Proof. exact (EQ_MP (@lem4888180 A) (@lem4887904 A h1)). Qed.
Lemma lem4888182 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term114 A P s) : term114 A P s.
Proof. exact (h1). Qed.
Lemma lem4888183 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term111 A P s t.
Proof. exact (h1). Qed.
Lemma lem4888192 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888193 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4888192 (type180 A) (type174 A) f x). Qed.
Lemma lem4888194 {A : Type'} : (@UNION_OF A (@FINITE (A -> Prop))) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))).
Proof. exact (@lem4888193 A (@UNION_OF A) (@FINITE (A -> Prop))). Qed.
Lemma lem4888195 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4888196 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P).
Proof. exact (MK_COMB (@lem4888194 A) (@lem4888195 A P)). Qed.
Lemma lem4888198 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888199 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4888198 (type686 A) (type686 A) f x). Qed.
Lemma lem4888200 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P) = (term122 A P).
Proof. exact (@lem4888199 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))) P). Qed.
Lemma lem4888201 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term122 A P).
Proof. exact (TRANS (@lem4888196 A P) (@lem4888200 A P)). Qed.
Lemma lem4888202 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4888203 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term123 A P s).
Proof. exact (MK_COMB (@lem4888201 A P) (@lem4888202 A s)). Qed.
Lemma lem4888205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888206 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4888205 (A -> Prop) Prop f x). Qed.
Lemma lem4888207 {A : Type'} (P : type686 A) (s : A -> Prop) : (term123 A P s) = (term124 A P s).
Proof. exact (@lem4888206 A (term122 A P) s). Qed.
Lemma lem4888209 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term124 A P s).
Proof. exact (TRANS (@lem4888203 A P s) (@lem4888207 A P s)). Qed.
Lemma lem4888210 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4888215 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888216 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4888215 (A -> Prop) Prop f x). Qed.
Lemma lem4888218 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4888216 A P s). Qed.
Lemma lem4888219 {A : Type'} (P : type686 A) (s : A -> Prop) : (term125 A P s) = (term126 A P s).
Proof. exact (MK_COMB (@lem4888210) (@lem4888218 A P s)). Qed.
Lemma lem4888220 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4888221 {A : Type'} (P : type686 A) (s : A -> Prop) : (term127 A P s) = (term128 A P s).
Proof. exact (MK_COMB (@lem4888220) (@lem4888219 A P s)). Qed.
Lemma lem4888222 {A : Type'} (P : type686 A) (s : A -> Prop) : (term117 A P s) = (term129 A P s).
Proof. exact (MK_COMB (@lem4888221 A P s) (@lem4888209 A P s)). Qed.
Lemma lem4888223 {A : Type'} (P : type686 A) : (term118 A P) = (term130 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4888222 A P s)). Qed.
Lemma lem4888224 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4888225 {A : Type'} (P : type686 A) : (term119 A P) = (term131 A P).
Proof. exact (MK_COMB (@lem4888224 A) (@lem4888223 A P)). Qed.
Lemma lem4888226 {A : Type'} : (term120 A) = (term132 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4888225 A P)). Qed.
Lemma lem4888227 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4888228 {A : Type'} : (term121 A) = (term133 A).
Proof. exact (MK_COMB (@lem4888227 A) (@lem4888226 A)). Qed.
Lemma lem4888229 {A : Type'} (h1 : term24 A) : term133 A.
Proof. exact (EQ_MP (@lem4888228 A) (@lem4888181 A h1)). Qed.
Lemma lem4888230 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4888240 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888241 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4888240 (A -> Prop) (type672 A) f x). Qed.
Lemma lem4888242 {A : Type'} (s : A -> Prop) : (@INTER A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s).
Proof. exact (@lem4888241 A (@INTER A) s). Qed.
Lemma lem4888243 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4888244 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t).
Proof. exact (MK_COMB (@lem4888242 A s) (@lem4888243 A t)). Qed.
Lemma lem4888246 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888247 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4888246 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4888248 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t) = (term134 A s t).
Proof. exact (@lem4888247 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s) t). Qed.
Lemma lem4888250 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term134 A s t).
Proof. exact (TRANS (@lem4888244 A s t) (@lem4888248 A s t)). Qed.
Lemma lem4888252 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@UNION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (eq_refl (@UNION_OF A (@FINITE (A -> Prop)) P)). Qed.
Lemma lem4888253 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term135 A P s t).
Proof. exact (MK_COMB (@lem4888252 A P) (@lem4888250 A s t)). Qed.
Lemma lem4888255 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888256 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4888255 (type180 A) (type174 A) f x). Qed.
Lemma lem4888257 {A : Type'} : (@UNION_OF A (@FINITE (A -> Prop))) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))).
Proof. exact (@lem4888256 A (@UNION_OF A) (@FINITE (A -> Prop))). Qed.
Lemma lem4888258 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4888259 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P).
Proof. exact (MK_COMB (@lem4888257 A) (@lem4888258 A P)). Qed.
Lemma lem4888261 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888262 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4888261 (type686 A) (type686 A) f x). Qed.
Lemma lem4888263 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P) = (term122 A P).
Proof. exact (@lem4888262 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))) P). Qed.
Lemma lem4888264 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term122 A P).
Proof. exact (TRANS (@lem4888259 A P) (@lem4888263 A P)). Qed.
Lemma lem4888265 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term134 A s t) = (term134 A s t).
Proof. exact (eq_refl (term134 A s t)). Qed.
Lemma lem4888266 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term135 A P s t) = (term136 A P s t).
Proof. exact (MK_COMB (@lem4888264 A P) (@lem4888265 A s t)). Qed.
Lemma lem4888268 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888269 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4888268 (A -> Prop) Prop f x). Qed.
Lemma lem4888270 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term136 A P s t) = (term137 A P s t).
Proof. exact (@lem4888269 A (term122 A P) (term134 A s t)). Qed.
Lemma lem4888271 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term135 A P s t) = (term137 A P s t).
Proof. exact (TRANS (@lem4888266 A P s t) (@lem4888270 A P s t)). Qed.
Lemma lem4888272 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term137 A P s t).
Proof. exact (TRANS (@lem4888253 A P s t) (@lem4888271 A P s t)). Qed.
Lemma lem4888273 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term138 A P s t) = (term139 A P s t).
Proof. exact (MK_COMB (@lem4888230) (@lem4888272 A P s t)). Qed.
Lemma lem4888278 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888279 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4888278 (A -> Prop) Prop f x). Qed.
Lemma lem4888281 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4888279 A P t). Qed.
Lemma lem4888286 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888287 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4888286 (A -> Prop) Prop f x). Qed.
Lemma lem4888289 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4888287 A P s). Qed.
Lemma lem4888290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4888291 {A : Type'} (P : type686 A) (s : A -> Prop) : (term140 A P s) = (term141 A P s).
Proof. exact (MK_COMB (@lem4888290) (@lem4888289 A P s)). Qed.
Lemma lem4888292 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term66 A s P t) = (term142 A s P t).
Proof. exact (MK_COMB (@lem4888291 A P s) (@lem4888281 A P t)). Qed.
Lemma lem4888293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4888294 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term143 A s P t) = (term144 A s P t).
Proof. exact (MK_COMB (@lem4888293) (@lem4888292 A s P t)). Qed.
Lemma lem4888295 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term65 A P s t) = (term145 A P s t).
Proof. exact (MK_COMB (@lem4888294 A s P t) (@lem4888273 A P s t)). Qed.
Lemma lem4888305 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888306 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4888305 (A -> Prop) (type672 A) f x). Qed.
Lemma lem4888307 {A : Type'} (s : A -> Prop) : (@INTER A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s).
Proof. exact (@lem4888306 A (@INTER A) s). Qed.
Lemma lem4888308 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4888309 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t).
Proof. exact (MK_COMB (@lem4888307 A s) (@lem4888308 A t)). Qed.
Lemma lem4888311 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888312 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4888311 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4888313 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t) = (term134 A s t).
Proof. exact (@lem4888312 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s) t). Qed.
Lemma lem4888315 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term134 A s t).
Proof. exact (TRANS (@lem4888309 A s t) (@lem4888313 A s t)). Qed.
Lemma lem4888317 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@UNION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (eq_refl (@UNION_OF A (@FINITE (A -> Prop)) P)). Qed.
Lemma lem4888318 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term135 A P s t).
Proof. exact (MK_COMB (@lem4888317 A P) (@lem4888315 A s t)). Qed.
Lemma lem4888320 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888321 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4888320 (type180 A) (type174 A) f x). Qed.
Lemma lem4888322 {A : Type'} : (@UNION_OF A (@FINITE (A -> Prop))) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))).
Proof. exact (@lem4888321 A (@UNION_OF A) (@FINITE (A -> Prop))). Qed.
Lemma lem4888323 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4888324 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P).
Proof. exact (MK_COMB (@lem4888322 A) (@lem4888323 A P)). Qed.
Lemma lem4888326 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888327 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4888326 (type686 A) (type686 A) f x). Qed.
Lemma lem4888328 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P) = (term122 A P).
Proof. exact (@lem4888327 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))) P). Qed.
Lemma lem4888329 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term122 A P).
Proof. exact (TRANS (@lem4888324 A P) (@lem4888328 A P)). Qed.
Lemma lem4888330 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term134 A s t) = (term134 A s t).
Proof. exact (eq_refl (term134 A s t)). Qed.
Lemma lem4888331 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term135 A P s t) = (term136 A P s t).
Proof. exact (MK_COMB (@lem4888329 A P) (@lem4888330 A s t)). Qed.
Lemma lem4888333 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888334 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4888333 (A -> Prop) Prop f x). Qed.
Lemma lem4888335 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term136 A P s t) = (term137 A P s t).
Proof. exact (@lem4888334 A (term122 A P) (term134 A s t)). Qed.
Lemma lem4888336 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term135 A P s t) = (term137 A P s t).
Proof. exact (TRANS (@lem4888331 A P s t) (@lem4888335 A P s t)). Qed.
Lemma lem4888337 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term137 A P s t).
Proof. exact (TRANS (@lem4888318 A P s t) (@lem4888336 A P s t)). Qed.
Lemma lem4888338 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4888347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888348 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4888347 (type180 A) (type174 A) f x). Qed.
Lemma lem4888349 {A : Type'} : (@UNION_OF A (@FINITE (A -> Prop))) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))).
Proof. exact (@lem4888348 A (@UNION_OF A) (@FINITE (A -> Prop))). Qed.
Lemma lem4888350 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4888351 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P).
Proof. exact (MK_COMB (@lem4888349 A) (@lem4888350 A P)). Qed.
Lemma lem4888353 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888354 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4888353 (type686 A) (type686 A) f x). Qed.
Lemma lem4888355 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P) = (term122 A P).
Proof. exact (@lem4888354 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))) P). Qed.
Lemma lem4888356 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term122 A P).
Proof. exact (TRANS (@lem4888351 A P) (@lem4888355 A P)). Qed.
Lemma lem4888357 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4888358 {A : Type'} (P : type686 A) (t : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P t) = (term123 A P t).
Proof. exact (MK_COMB (@lem4888356 A P) (@lem4888357 A t)). Qed.
Lemma lem4888360 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888361 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4888360 (A -> Prop) Prop f x). Qed.
Lemma lem4888362 {A : Type'} (P : type686 A) (t : A -> Prop) : (term123 A P t) = (term124 A P t).
Proof. exact (@lem4888361 A (term122 A P) t). Qed.
Lemma lem4888364 {A : Type'} (P : type686 A) (t : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P t) = (term124 A P t).
Proof. exact (TRANS (@lem4888358 A P t) (@lem4888362 A P t)). Qed.
Lemma lem4888365 {A : Type'} (P : type686 A) (t : A -> Prop) : (term146 A P t) = (term147 A P t).
Proof. exact (MK_COMB (@lem4888338) (@lem4888364 A P t)). Qed.
Lemma lem4888366 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4888375 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888376 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4888375 (type180 A) (type174 A) f x). Qed.
Lemma lem4888377 {A : Type'} : (@UNION_OF A (@FINITE (A -> Prop))) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))).
Proof. exact (@lem4888376 A (@UNION_OF A) (@FINITE (A -> Prop))). Qed.
Lemma lem4888378 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4888379 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P).
Proof. exact (MK_COMB (@lem4888377 A) (@lem4888378 A P)). Qed.
Lemma lem4888381 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888382 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4888381 (type686 A) (type686 A) f x). Qed.
Lemma lem4888383 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop)) P) = (term122 A P).
Proof. exact (@lem4888382 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@FINITE (A -> Prop))) P). Qed.
Lemma lem4888384 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term122 A P).
Proof. exact (TRANS (@lem4888379 A P) (@lem4888383 A P)). Qed.
Lemma lem4888385 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4888386 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term123 A P s).
Proof. exact (MK_COMB (@lem4888384 A P) (@lem4888385 A s)). Qed.
Lemma lem4888388 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4888389 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4888388 (A -> Prop) Prop f x). Qed.
Lemma lem4888390 {A : Type'} (P : type686 A) (s : A -> Prop) : (term123 A P s) = (term124 A P s).
Proof. exact (@lem4888389 A (term122 A P) s). Qed.
Lemma lem4888392 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term124 A P s).
Proof. exact (TRANS (@lem4888386 A P s) (@lem4888390 A P s)). Qed.
Lemma lem4888393 {A : Type'} (P : type686 A) (s : A -> Prop) : (term146 A P s) = (term147 A P s).
Proof. exact (MK_COMB (@lem4888366) (@lem4888392 A P s)). Qed.
Lemma lem4888394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4888395 {A : Type'} (P : type686 A) (s : A -> Prop) : (term148 A P s) = (term149 A P s).
Proof. exact (MK_COMB (@lem4888394) (@lem4888393 A P s)). Qed.
Lemma lem4888396 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term53 A s P t) = (term150 A s P t).
Proof. exact (MK_COMB (@lem4888395 A P s) (@lem4888365 A P t)). Qed.
Lemma lem4888397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4888398 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term56 A s P t) = (term151 A s P t).
Proof. exact (MK_COMB (@lem4888397) (@lem4888396 A s P t)). Qed.
Lemma lem4888399 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term58 A P s t) = (term152 A P s t).
Proof. exact (MK_COMB (@lem4888398 A s P t) (@lem4888337 A P s t)). Qed.
Lemma lem4888400 {A : Type'} (P : type686 A) (s : A -> Prop) : (term60 A P s) = (term153 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4888399 A P s t)). Qed.
Lemma lem4888401 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4888402 {A : Type'} (P : type686 A) (s : A -> Prop) : (term61 A P s) = (term154 A P s).
Proof. exact (MK_COMB (@lem4888401 A) (@lem4888400 A P s)). Qed.
Lemma lem4888403 {A : Type'} (P : type686 A) : (term62 A P) = (term155 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4888402 A P s)). Qed.
Lemma lem4888404 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4888405 {A : Type'} (P : type686 A) : (term63 A P) = (term156 A P).
Proof. exact (MK_COMB (@lem4888404 A) (@lem4888403 A P)). Qed.
Lemma lem4888406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4888407 {A : Type'} (P : type686 A) : (term84 A P) = (term157 A P).
Proof. exact (MK_COMB (@lem4888406) (@lem4888405 A P)). Qed.
Lemma lem4888408 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term111 A P s t) = (term158 A P s t).
Proof. exact (MK_COMB (@lem4888407 A P) (@lem4888295 A P s t)). Qed.
Lemma lem4888409 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term158 A P s t.
Proof. exact (EQ_MP (@lem4888408 A P s t) (@lem4888183 A P s t h1)). Qed.
Lemma lem4888410 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term145 A P s t.
Proof. exact (proj2 (@lem4888409 A P s t h1)). Qed.
Lemma lem4888411 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term156 A P.
Proof. exact (proj1 (@lem4888409 A P s t h1)). Qed.
Lemma lem4888413 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term142 A s P t.
Proof. exact (proj1 (@lem4888410 A P s t h1)). Qed.
Lemma lem4888423 {A : Type'} (P : type686 A) (s : A -> Prop) : (term129 A P s) = (term129 A P s).
Proof. exact (eq_refl (term129 A P s)). Qed.
Lemma lem4888424 {A : Type'} (P : type686 A) : (term130 A P) = (term130 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4888423 A P s)). Qed.
Lemma lem4888425 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4888426 {A : Type'} (P : type686 A) : (term131 A P) = (term131 A P).
Proof. exact (MK_COMB (@lem4888425 A) (@lem4888424 A P)). Qed.
Lemma lem4888427 {A : Type'} : (term132 A) = (term132 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4888426 A P)). Qed.
Lemma lem4888428 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4888430 {A : Type'} : (term133 A) = (term133 A).
Proof. exact (MK_COMB (@lem4888428 A) (@lem4888427 A)). Qed.
Lemma lem4888431 {A : Type'} (h1 : term24 A) : term133 A.
Proof. exact (EQ_MP (@lem4888430 A) (@lem4888229 A h1)). Qed.
Lemma lem4888445 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term152 A P s t) = (term152 A P s t).
Proof. exact (eq_refl (term152 A P s t)). Qed.
Lemma lem4888446 {A : Type'} (P : type686 A) (s : A -> Prop) : (term153 A P s) = (term153 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4888445 A P s t)). Qed.
Lemma lem4888447 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4888448 {A : Type'} (P : type686 A) (s : A -> Prop) : (term154 A P s) = (term154 A P s).
Proof. exact (MK_COMB (@lem4888447 A) (@lem4888446 A P s)). Qed.
Lemma lem4888449 {A : Type'} (P : type686 A) : (term155 A P) = (term155 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4888448 A P s)). Qed.
Lemma lem4888450 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4888452 {A : Type'} (P : type686 A) : (term156 A P) = (term156 A P).
Proof. exact (MK_COMB (@lem4888450 A) (@lem4888449 A P)). Qed.
Lemma lem4888453 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term156 A P.
Proof. exact (EQ_MP (@lem4888452 A P) (@lem4888411 A P s t h1)). Qed.
Lemma lem4888466 {A : Type'} (_60399 : type686 A) (h1 : term24 A) : term159 A _60399.
Proof. exact (@lem4888431 A h1 _60399). Qed.
Lemma lem4888467 {A : Type'} (_60399 : type686 A) : (term159 A _60399) = (term131 A _60399).
Proof. exact (eq_refl (term159 A _60399)). Qed.
Lemma lem4888468 {A : Type'} (_60399 : type686 A) (h1 : term24 A) : term131 A _60399.
Proof. exact (EQ_MP (@lem4888467 A _60399) (@lem4888466 A _60399 h1)). Qed.
Lemma lem4888469 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) (h1 : term24 A) : term160 A _60399 _60400.
Proof. exact (@lem4888468 A _60399 h1 _60400). Qed.
Lemma lem4888470 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : (term160 A _60399 _60400) = (term129 A _60399 _60400).
Proof. exact (eq_refl (term160 A _60399 _60400)). Qed.
Lemma lem4888472 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term161 A P _60401.
Proof. exact (@lem4888453 A P s t h1 _60401). Qed.
Lemma lem4888473 {A : Type'} (P : type686 A) (_60401 : A -> Prop) : (term161 A P _60401) = (term154 A P _60401).
Proof. exact (eq_refl (term161 A P _60401)). Qed.
Lemma lem4888474 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term154 A P _60401.
Proof. exact (EQ_MP (@lem4888473 A P _60401) (@lem4888472 A _60401 P s t h1)). Qed.
Lemma lem4888475 {A : Type'} (_60401 : A -> Prop) (_60402 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term162 A P _60401 _60402.
Proof. exact (@lem4888474 A _60401 P s t h1 _60402). Qed.
Lemma lem4888476 {A : Type'} (P : type686 A) (_60401 : A -> Prop) (_60402 : A -> Prop) : (term162 A P _60401 _60402) = (term152 A P _60401 _60402).
Proof. exact (eq_refl (term162 A P _60401 _60402)). Qed.
Lemma lem4888477 {A : Type'} (_60401 : A -> Prop) (_60402 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term152 A P _60401 _60402.
Proof. exact (EQ_MP (@lem4888476 A P _60401 _60402) (@lem4888475 A _60401 _60402 P s t h1)). Qed.
Lemma lem4888483 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) (h1 : term24 A) : term129 A _60399 _60400.
Proof. exact (EQ_MP (@lem4888470 A _60399 _60400) (@lem4888469 A _60399 _60400 h1)). Qed.
Lemma lem4888494 {A : Type'} (P : type686 A) (_60401 : A -> Prop) (_60402 : A -> Prop) : (term152 A P _60401 _60402) = (term163 A P _60401 _60402).
Proof. exact (@lem4887705 (term147 A P _60401) (term147 A P _60402) (term137 A P _60401 _60402)). Qed.
Lemma lem4888495 {A : Type'} (_60401 : A -> Prop) (_60402 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term163 A P _60401 _60402.
Proof. exact (EQ_MP (@lem4888494 A P _60401 _60402) (@lem4888477 A _60401 _60402 P s t h1)). Qed.
Lemma lem4888497 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term139 A P s t.
Proof. exact (proj2 (@lem4888410 A P s t h1)). Qed.
Lemma lem4888503 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : @I ((A -> Prop) -> Prop) P s.
Proof. exact (proj1 (@lem4888413 A P s t h1)). Qed.
Lemma lem4888504 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term164 A P s.
Proof. exact (fun h0 : term126 A P s => @lem4888503 A P s t h1). Qed.
Lemma lem4888506 (p : Prop) : (term165 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4888507 {A : Type'} (P : type686 A) (s : A -> Prop) : (term164 A P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4888506 (@I ((A -> Prop) -> Prop) P s)). Qed.
Lemma lem4888508 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : @I ((A -> Prop) -> Prop) P s.
Proof. exact (EQ_MP (@lem4888507 A P s) (@lem4888504 A P s t h1)). Qed.
Lemma lem4888514 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4888515 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : (term129 A _60399 _60400) = (term166 A _60399 _60400).
Proof. exact (@lem4888514 (term124 A _60399 _60400) (term126 A _60399 _60400)). Qed.
Lemma lem4888521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4888522 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : (term167 A _60399 _60400) = (term168 A _60399 _60400).
Proof. exact (MK_COMB (@lem4888521) (@lem4888515 A _60399 _60400)). Qed.
Lemma lem4888528 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : (term166 A _60399 _60400) = (term166 A _60399 _60400).
Proof. exact (eq_refl (term166 A _60399 _60400)). Qed.
Lemma lem4888529 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : ((term129 A _60399 _60400) = (term166 A _60399 _60400)) = ((term166 A _60399 _60400) = (term166 A _60399 _60400)).
Proof. exact (MK_COMB (@lem4888522 A _60399 _60400) (@lem4888528 A _60399 _60400)). Qed.
Lemma lem4888531 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4888532 (x : Prop) : (x = x) = True.
Proof. exact (@lem4888531 Prop x). Qed.
Lemma lem4888533 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : ((term166 A _60399 _60400) = (term166 A _60399 _60400)) = True.
Proof. exact (@lem4888532 (term166 A _60399 _60400)). Qed.
Lemma lem4888534 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : ((term129 A _60399 _60400) = (term166 A _60399 _60400)) = True.
Proof. exact (TRANS (@lem4888529 A _60399 _60400) (@lem4888533 A _60399 _60400)). Qed.
Lemma lem4888535 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : True = ((term129 A _60399 _60400) = (term166 A _60399 _60400)).
Proof. exact (SYM (@lem4888534 A _60399 _60400)). Qed.
Lemma lem4888536 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : (term129 A _60399 _60400) = (term166 A _60399 _60400).
Proof. exact (EQ_MP (@lem4888535 A _60399 _60400) (@lem0)). Qed.
Lemma lem4888537 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) (h1 : term24 A) : term166 A _60399 _60400.
Proof. exact (EQ_MP (@lem4888536 A _60399 _60400) (@lem4888483 A _60399 _60400 h1)). Qed.
Lemma lem4888539 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4888540 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : (term166 A _60399 _60400) = (term170 A _60399 _60400).
Proof. exact (@lem4888539 (term126 A _60399 _60400) (term124 A _60399 _60400)). Qed.
Lemma lem4888542 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4888543 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : (term172 A _60399 _60400) = (@I ((A -> Prop) -> Prop) _60399 _60400).
Proof. exact (@lem4888542 (@I ((A -> Prop) -> Prop) _60399 _60400)). Qed.
Lemma lem4888544 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4888545 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : (term173 A _60399 _60400) = (term174 A _60399 _60400).
Proof. exact (MK_COMB (@lem4888544) (@lem4888543 A _60399 _60400)). Qed.
Lemma lem4888546 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : (term124 A _60399 _60400) = (term124 A _60399 _60400).
Proof. exact (eq_refl (term124 A _60399 _60400)). Qed.
Lemma lem4888547 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : (term170 A _60399 _60400) = (term175 A _60399 _60400).
Proof. exact (MK_COMB (@lem4888545 A _60399 _60400) (@lem4888546 A _60399 _60400)). Qed.
Lemma lem4888548 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) : (term166 A _60399 _60400) = (term175 A _60399 _60400).
Proof. exact (TRANS (@lem4888540 A _60399 _60400) (@lem4888547 A _60399 _60400)). Qed.
Lemma lem4888551 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) (h1 : term24 A) : term175 A _60399 _60400.
Proof. exact (EQ_MP (@lem4888548 A _60399 _60400) (@lem4888537 A _60399 _60400 h1)). Qed.
Lemma lem4888552 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) (h1 : term24 A) : term175 A _60399 _60400.
Proof. exact (@lem4888551 A _60399 _60400 h1). Qed.
Lemma lem4888553 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term24 A) : term175 A P s.
Proof. exact (@lem4888552 A P s h1). Qed.
Lemma lem4888556 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term124 A P s.
Proof. exact (@lem4888553 A P s h1 (@lem4888508 A P s t h2)). Qed.
Lemma lem4888557 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term176 A P s.
Proof. exact (fun h0 : term147 A P s => @lem4888556 A P s t h1 h2). Qed.
Lemma lem4888559 (p : Prop) : (term165 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4888560 {A : Type'} (P : type686 A) (s : A -> Prop) : (term176 A P s) = (term124 A P s).
Proof. exact (@lem4888559 (term124 A P s)). Qed.
Lemma lem4888561 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term124 A P s.
Proof. exact (EQ_MP (@lem4888560 A P s) (@lem4888557 A P s t h1 h2)). Qed.
Lemma lem4888563 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (proj2 (@lem4888413 A P s t h1)). Qed.
Lemma lem4888564 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term164 A P t.
Proof. exact (fun h0 : term126 A P t => @lem4888563 A P s t h1). Qed.
Lemma lem4888566 (p : Prop) : (term165 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4888567 {A : Type'} (P : type686 A) (t : A -> Prop) : (term164 A P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4888566 (@I ((A -> Prop) -> Prop) P t)). Qed.
Lemma lem4888568 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (EQ_MP (@lem4888567 A P t) (@lem4888564 A P s t h1)). Qed.
Lemma lem4888570 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) (h1 : term24 A) : term175 A _60399 _60400.
Proof. exact (EQ_MP (@lem4888548 A _60399 _60400) (@lem4888537 A _60399 _60400 h1)). Qed.
Lemma lem4888571 {A : Type'} (_60399 : type686 A) (_60400 : A -> Prop) (h1 : term24 A) : term175 A _60399 _60400.
Proof. exact (@lem4888570 A _60399 _60400 h1). Qed.
Lemma lem4888572 {A : Type'} (P : type686 A) (t : A -> Prop) (h1 : term24 A) : term175 A P t.
Proof. exact (@lem4888571 A P t h1). Qed.
Lemma lem4888575 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term124 A P t.
Proof. exact (@lem4888572 A P t h1 (@lem4888568 A P s t h2)). Qed.
Lemma lem4888576 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term176 A P t.
Proof. exact (fun h0 : term147 A P t => @lem4888575 A P s t h1 h2). Qed.
Lemma lem4888578 (p : Prop) : (term165 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4888579 {A : Type'} (P : type686 A) (t : A -> Prop) : (term176 A P t) = (term124 A P t).
Proof. exact (@lem4888578 (term124 A P t)). Qed.
Lemma lem4888580 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term124 A P t.
Proof. exact (EQ_MP (@lem4888579 A P t) (@lem4888576 A P s t h1 h2)). Qed.
Lemma lem4888596 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4888597 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : (term177 A P _60401 _60402) = (term178 A _60401 P _60402).
Proof. exact (@lem4888596 (term137 A P _60401 _60402) (term147 A P _60402)). Qed.
Lemma lem4888603 {A : Type'} (P : type686 A) (_60401 : A -> Prop) : (term149 A P _60401) = (term149 A P _60401).
Proof. exact (eq_refl (term149 A P _60401)). Qed.
Lemma lem4888604 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : (term163 A P _60401 _60402) = (term179 A _60401 P _60402).
Proof. exact (MK_COMB (@lem4888603 A P _60401) (@lem4888597 A _60401 P _60402)). Qed.
Lemma lem4888608 (q : Prop) (p : Prop) (r : Prop) : (term18 p q r) = (term18 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4888609 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : (term179 A _60401 P _60402) = (term180 A _60401 P _60402).
Proof. exact (@lem4888608 (term137 A P _60401 _60402) (term147 A P _60401) (term147 A P _60402)). Qed.
Lemma lem4888625 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : (term163 A P _60401 _60402) = (term180 A _60401 P _60402).
Proof. exact (TRANS (@lem4888604 A _60401 P _60402) (@lem4888609 A _60401 P _60402)). Qed.
Lemma lem4888626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4888627 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : (term181 A P _60401 _60402) = (term182 A _60401 P _60402).
Proof. exact (MK_COMB (@lem4888626) (@lem4888625 A _60401 P _60402)). Qed.
Lemma lem4888643 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : (term180 A _60401 P _60402) = (term180 A _60401 P _60402).
Proof. exact (eq_refl (term180 A _60401 P _60402)). Qed.
Lemma lem4888644 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : ((term163 A P _60401 _60402) = (term180 A _60401 P _60402)) = ((term180 A _60401 P _60402) = (term180 A _60401 P _60402)).
Proof. exact (MK_COMB (@lem4888627 A _60401 P _60402) (@lem4888643 A _60401 P _60402)). Qed.
Lemma lem4888646 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4888647 (x : Prop) : (x = x) = True.
Proof. exact (@lem4888646 Prop x). Qed.
Lemma lem4888648 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : ((term180 A _60401 P _60402) = (term180 A _60401 P _60402)) = True.
Proof. exact (@lem4888647 (term180 A _60401 P _60402)). Qed.
Lemma lem4888649 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : ((term163 A P _60401 _60402) = (term180 A _60401 P _60402)) = True.
Proof. exact (TRANS (@lem4888644 A _60401 P _60402) (@lem4888648 A _60401 P _60402)). Qed.
Lemma lem4888650 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : True = ((term163 A P _60401 _60402) = (term180 A _60401 P _60402)).
Proof. exact (SYM (@lem4888649 A _60401 P _60402)). Qed.
Lemma lem4888651 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : (term163 A P _60401 _60402) = (term180 A _60401 P _60402).
Proof. exact (EQ_MP (@lem4888650 A _60401 P _60402) (@lem0)). Qed.
Lemma lem4888652 {A : Type'} (_60401 : A -> Prop) (_60402 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term180 A _60401 P _60402.
Proof. exact (EQ_MP (@lem4888651 A _60401 P _60402) (@lem4888495 A _60401 _60402 P s t h1)). Qed.
Lemma lem4888654 (b : Prop) (a : Prop) : (a \/ b) = (term169 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4888655 {A : Type'} (P : type686 A) (_60401 : A -> Prop) (_60402 : A -> Prop) : (term180 A _60401 P _60402) = (term183 A P _60401 _60402).
Proof. exact (@lem4888654 (term150 A _60401 P _60402) (term137 A P _60401 _60402)). Qed.
Lemma lem4888657 (a : Prop) (b : Prop) : (term184 a b) = (term185 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4888658 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : (term186 A _60401 P _60402) = (term187 A _60401 P _60402).
Proof. exact (@lem4888657 (term147 A P _60401) (term147 A P _60402)). Qed.
Lemma lem4888660 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4888661 {A : Type'} (P : type686 A) (_60401 : A -> Prop) : (term188 A P _60401) = (term124 A P _60401).
Proof. exact (@lem4888660 (term124 A P _60401)). Qed.
Lemma lem4888662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4888663 {A : Type'} (P : type686 A) (_60401 : A -> Prop) : (term189 A P _60401) = (term190 A P _60401).
Proof. exact (MK_COMB (@lem4888662) (@lem4888661 A P _60401)). Qed.
Lemma lem4888665 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4888666 {A : Type'} (P : type686 A) (_60402 : A -> Prop) : (term188 A P _60402) = (term124 A P _60402).
Proof. exact (@lem4888665 (term124 A P _60402)). Qed.
Lemma lem4888667 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : (term187 A _60401 P _60402) = (term191 A _60401 P _60402).
Proof. exact (MK_COMB (@lem4888663 A P _60401) (@lem4888666 A P _60402)). Qed.
Lemma lem4888668 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : (term186 A _60401 P _60402) = (term191 A _60401 P _60402).
Proof. exact (TRANS (@lem4888658 A _60401 P _60402) (@lem4888667 A _60401 P _60402)). Qed.
Lemma lem4888669 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4888670 {A : Type'} (_60401 : A -> Prop) (P : type686 A) (_60402 : A -> Prop) : (term192 A _60401 P _60402) = (term193 A _60401 P _60402).
Proof. exact (MK_COMB (@lem4888669) (@lem4888668 A _60401 P _60402)). Qed.
Lemma lem4888671 {A : Type'} (P : type686 A) (_60401 : A -> Prop) (_60402 : A -> Prop) : (term137 A P _60401 _60402) = (term137 A P _60401 _60402).
Proof. exact (eq_refl (term137 A P _60401 _60402)). Qed.
Lemma lem4888672 {A : Type'} (P : type686 A) (_60401 : A -> Prop) (_60402 : A -> Prop) : (term183 A P _60401 _60402) = (term194 A P _60401 _60402).
Proof. exact (MK_COMB (@lem4888670 A _60401 P _60402) (@lem4888671 A P _60401 _60402)). Qed.
Lemma lem4888673 {A : Type'} (P : type686 A) (_60401 : A -> Prop) (_60402 : A -> Prop) : (term180 A _60401 P _60402) = (term194 A P _60401 _60402).
Proof. exact (TRANS (@lem4888655 A P _60401 _60402) (@lem4888672 A P _60401 _60402)). Qed.
Lemma lem4888675 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term191 A s P t.
Proof. exact (conj (@lem4888561 A P s t h1 h2) (@lem4888580 A P s t h1 h2)). Qed.
Lemma lem4888677 {A : Type'} (_60401 : A -> Prop) (_60402 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term194 A P _60401 _60402.
Proof. exact (EQ_MP (@lem4888673 A P _60401 _60402) (@lem4888652 A _60401 _60402 P s t h1)). Qed.
Lemma lem4888678 {A : Type'} (_60401 : A -> Prop) (_60402 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term194 A P _60401 _60402.
Proof. exact (@lem4888677 A _60401 _60402 P s t h1). Qed.
Lemma lem4888679 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term194 A P s t.
Proof. exact (@lem4888678 A s t P s t h1). Qed.
Lemma lem4888682 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term137 A P s t.
Proof. exact (@lem4888679 A P s t h2 (@lem4888675 A P s t h1 h2)). Qed.
Lemma lem4888683 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term195 A P s t.
Proof. exact (fun h0 : term139 A P s t => @lem4888682 A P s t h1 h2). Qed.
Lemma lem4888685 (p : Prop) : (term165 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4888686 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term195 A P s t) = (term137 A P s t).
Proof. exact (@lem4888685 (term137 A P s t)). Qed.
Lemma lem4888687 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term137 A P s t.
Proof. exact (EQ_MP (@lem4888686 A P s t) (@lem4888683 A P s t h1 h2)). Qed.
Lemma lem4888690 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4888692 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term139 A P s t) = (term196 A P s t).
Proof. exact (@lem4888690 (term137 A P s t)). Qed.
Lemma lem4888695 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term111 A P s t) : term196 A P s t.
Proof. exact (EQ_MP (@lem4888692 A P s t) (@lem4888497 A P s t h1)). Qed.
Lemma lem4888698 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : False.
Proof. exact (@lem4888695 A P s t h2 (@lem4888687 A P s t h1 h2)). Qed.
Lemma lem4888699 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : term197.
Proof. exact (fun h0 : ~ False => @lem4888698 A P s t h1 h2). Qed.
Lemma lem4888701 (p : Prop) : (term165 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4888702 : term197 = False.
Proof. exact (@lem4888701 False). Qed.
Lemma lem4888703 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term24 A) (h2 : term111 A P s t) : False.
Proof. exact (EQ_MP (@lem4888702) (@lem4888699 A P s t h1 h2)). Qed.
Lemma lem4888704 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term24 A) (h2 : term114 A P s) : False.
Proof. exact (ex_elim (@lem4888182 A P s h2) (fun t : A -> Prop => fun h0 : term113 A P s t => @lem4888703 A P s t h1 h0)). Qed.
Lemma lem4888705 {A : Type'} (P : type686 A) (h1 : term24 A) (h2 : term23 A P) : False.
Proof. exact (ex_elim (@lem4888111 A P h2) (fun s : A -> Prop => fun h0 : term115 A P s => @lem4888704 A P s h1 h0)). Qed.
Lemma lem4888706 {A : Type'} (P : type686 A) (h1 : term23 A P) : term29 A.
Proof. exact (fun h0 : term24 A => @lem4888705 A P h0 h1). Qed.
Lemma lem4888707 {A : Type'} : (term29 A) = (term30 A).
Proof. exact (@lem69 (term24 A)). Qed.
Lemma lem4888708 {A : Type'} (P : type686 A) (h1 : term23 A P) : term30 A.
Proof. exact (EQ_MP (@lem4888707 A) (@lem4888706 A P h1)). Qed.
Lemma lem4888709 {A : Type'} (P : type686 A) : term32 A P.
Proof. exact (fun h0 : term23 A P => @lem4888708 A P h0). Qed.
Lemma lem4888714 {A : Type'} : term36 A.
Proof. exact (fun P : type686 A => @lem4888709 A P). Qed.
Lemma lem4888715 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem4887902 A) (@lem4888714 A)). Qed.
Lemma lem4888716 {A : Type'} (P : type686 A) : term198 A P.
Proof. exact (@lem4888715 A P). Qed.
Lemma lem4888717 {A : Type'} (P : type686 A) : (term198 A P) = (term25 A P).
Proof. exact (eq_refl (term198 A P)). Qed.
Lemma lem4888718 {A : Type'} (P : type686 A) : term25 A P.
Proof. exact (EQ_MP (@lem4888717 A P) (@lem4888716 A P)). Qed.
Lemma lem4888720 {A : Type'} (P : type686 A) : term25 A P.
Proof. exact (@lem4887728 A P (@lem4888718 A P)). Qed.
Lemma lem4888721 {A : Type'} (P : type686 A) (h1 : term23 A P) : term29 A.
Proof. exact (@lem4888720 A P (@lem4887710 A P h1)). Qed.
Lemma lem4888722 {A : Type'} (P : type686 A) (h1 : term23 A P) : False.
Proof. exact (@lem4888721 A P h1 (@lem4887711 A)). Qed.
Lemma lem4888723 {A : Type'} (P : type686 A) (h1 : term23 A P) : (term23 A P) = False.
Proof. exact (prop_ext (fun h2 : term23 A P => @lem4888722 A P h1) (fun h2 : False => @lem4887710 A P h1)). Qed.
Lemma lem4888724 {A : Type'} (P : type686 A) (h1 : term23 A P) : False.
Proof. exact (EQ_MP (@lem4888723 A P h1) (@lem4887710 A P h1)). Qed.
Lemma lem4888725 {A : Type'} (P : type686 A) : term22 A P.
Proof. exact (fun h0 : term23 A P => @lem4888724 A P h0). Qed.
Lemma lem4888726 {A : Type'} (P : type686 A) : term21 A P.
Proof. exact (EQ_MP (@lem4887709 A P) (@lem4888725 A P)). Qed.
Lemma lem4888727 {A : Type'} (P : type686 A) (h1 : term45 A P) : term45 A P.
Proof. exact (h1). Qed.
Lemma lem4888729 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term12 A P Q).
Proof. exact (EQ_MP (@lem4887694 A P Q) (@lem4887693 A P Q)). Qed.
Lemma lem4888730 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term12 A P Q).
Proof. exact (@lem4888729 A P Q). Qed.
Lemma lem4888731 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term199 A P).
Proof. exact (@lem4888730 A (@FINITE (A -> Prop)) P). Qed.
Lemma lem4888732 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4888733 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P s) = (term200 A P s).
Proof. exact (MK_COMB (@lem4888731 A P) (@lem4888732 A s)). Qed.
Lemma lem4888734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4888735 {A : Type'} (P : type686 A) (s : A -> Prop) : (term201 A P s) = (term202 A P s).
Proof. exact (MK_COMB (@lem4888734) (@lem4888733 A P s)). Qed.
Lemma lem4888737 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term12 A P Q).
Proof. exact (EQ_MP (@lem4887694 A P Q) (@lem4887693 A P Q)). Qed.
Lemma lem4888738 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term12 A P Q).
Proof. exact (@lem4888737 A P Q). Qed.
Lemma lem4888739 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (term199 A P).
Proof. exact (@lem4888738 A (@FINITE (A -> Prop)) P). Qed.
Lemma lem4888740 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4888741 {A : Type'} (P : type686 A) (t : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P t) = (term200 A P t).
Proof. exact (MK_COMB (@lem4888739 A P) (@lem4888740 A t)). Qed.
Lemma lem4888742 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term59 A s P t) = (term203 A s P t).
Proof. exact (MK_COMB (@lem4888735 A P s) (@lem4888741 A P t)). Qed.
Lemma lem4888743 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4888744 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term204 A s P t) = (term205 A s P t).
Proof. exact (MK_COMB (@lem4888743) (@lem4888742 A s P t)). Qed.
Lemma lem4888745 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term54 A P s t).
Proof. exact (eq_refl (term54 A P s t)). Qed.
Lemma lem4888746 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term46 A P s t) = (term206 A P s t).
Proof. exact (MK_COMB (@lem4888744 A s P t) (@lem4888745 A P s t)). Qed.
Lemma lem4888747 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term206 A P s t) = (term46 A P s t).
Proof. exact (SYM (@lem4888746 A P s t)). Qed.
Lemma lem4888753 {A B : Type'} (f : A -> B) (y : A) : (term207 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4888754 {A : Type'} (f : type686 A) (y : A -> Prop) : (term208 A f y) = (f y).
Proof. exact (@lem4888753 (A -> Prop) Prop f y). Qed.
Lemma lem4888755 {A : Type'} (P : type686 A) (s : A -> Prop) : (term209 A P s) = (term200 A P s).
Proof. exact (@lem4888754 A (term199 A P) s). Qed.
Lemma lem4888756 {A : Type'} (P : type686 A) (s : A -> Prop) : (term200 A P s) = (term210 A P s).
Proof. exact (eq_refl (term200 A P s)). Qed.
Lemma lem4888757 {A : Type'} (P : type686 A) : (term211 A P) = (term199 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4888756 A P s)). Qed.
Lemma lem4888758 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4888759 {A : Type'} (P : type686 A) (s : A -> Prop) : (term209 A P s) = (term200 A P s).
Proof. exact (MK_COMB (@lem4888757 A P) (@lem4888758 A s)). Qed.
Lemma lem4888760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4888761 {A : Type'} (P : type686 A) (s : A -> Prop) : (term212 A P s) = (term213 A P s).
Proof. exact (MK_COMB (@lem4888760) (@lem4888759 A P s)). Qed.
Lemma lem4888762 {A : Type'} (P : type686 A) (s : A -> Prop) : (term200 A P s) = (term210 A P s).
Proof. exact (eq_refl (term200 A P s)). Qed.
Lemma lem4888763 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term209 A P s) = (term200 A P s)) = ((term200 A P s) = (term210 A P s)).
Proof. exact (MK_COMB (@lem4888761 A P s) (@lem4888762 A P s)). Qed.
Lemma lem4888764 {A : Type'} (P : type686 A) (s : A -> Prop) : (term200 A P s) = (term210 A P s).
Proof. exact (EQ_MP (@lem4888763 A P s) (@lem4888755 A P s)). Qed.
Lemma lem4888781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4888782 {A : Type'} (P : type686 A) (s : A -> Prop) : (term202 A P s) = (term214 A P s).
Proof. exact (MK_COMB (@lem4888781) (@lem4888764 A P s)). Qed.
Lemma lem4888784 {A B : Type'} (f : A -> B) (y : A) : (term207 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4888785 {A : Type'} (f : type686 A) (y : A -> Prop) : (term208 A f y) = (f y).
Proof. exact (@lem4888784 (A -> Prop) Prop f y). Qed.
Lemma lem4888786 {A : Type'} (P : type686 A) (t : A -> Prop) : (term209 A P t) = (term200 A P t).
Proof. exact (@lem4888785 A (term199 A P) t). Qed.
Lemma lem4888787 {A : Type'} (P : type686 A) (s : A -> Prop) : (term200 A P s) = (term210 A P s).
Proof. exact (eq_refl (term200 A P s)). Qed.
Lemma lem4888788 {A : Type'} (P : type686 A) : (term211 A P) = (term199 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4888787 A P s)). Qed.
Lemma lem4888789 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4888790 {A : Type'} (P : type686 A) (t : A -> Prop) : (term209 A P t) = (term200 A P t).
Proof. exact (MK_COMB (@lem4888788 A P) (@lem4888789 A t)). Qed.
Lemma lem4888791 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4888792 {A : Type'} (P : type686 A) (t : A -> Prop) : (term212 A P t) = (term213 A P t).
Proof. exact (MK_COMB (@lem4888791) (@lem4888790 A P t)). Qed.
Lemma lem4888793 {A : Type'} (P : type686 A) (t : A -> Prop) : (term200 A P t) = (term210 A P t).
Proof. exact (eq_refl (term200 A P t)). Qed.
Lemma lem4888794 {A : Type'} (P : type686 A) (t : A -> Prop) : ((term209 A P t) = (term200 A P t)) = ((term200 A P t) = (term210 A P t)).
Proof. exact (MK_COMB (@lem4888792 A P t) (@lem4888793 A P t)). Qed.
Lemma lem4888795 {A : Type'} (P : type686 A) (t : A -> Prop) : (term200 A P t) = (term210 A P t).
Proof. exact (EQ_MP (@lem4888794 A P t) (@lem4888786 A P t)). Qed.
Lemma lem4888812 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term203 A s P t) = (term215 A s P t).
Proof. exact (MK_COMB (@lem4888782 A P s) (@lem4888795 A P t)). Qed.
Lemma lem4888815 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4888816 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term205 A s P t) = (term216 A s P t).
Proof. exact (MK_COMB (@lem4888815) (@lem4888812 A s P t)). Qed.
Lemma lem4888817 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term54 A P s t).
Proof. exact (eq_refl (term54 A P s t)). Qed.
Lemma lem4888818 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term206 A P s t) = (term217 A P s t).
Proof. exact (MK_COMB (@lem4888816 A s P t) (@lem4888817 A P s t)). Qed.
Lemma lem4888821 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term217 A P s t) = (term206 A P s t).
Proof. exact (SYM (@lem4888818 A P s t)). Qed.
Lemma lem4888822 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term215 A s P t) : term215 A s P t.
Proof. exact (h1). Qed.
Lemma lem4888832 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (@UNIONS A u) = s.
Proof. exact (h1). Qed.
Lemma lem4888833 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : s = (@UNIONS A u).
Proof. exact (SYM (@lem4888832 A u s h1)). Qed.
Lemma lem4888834 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : s = (@UNIONS A u)) : s = (@UNIONS A u).
Proof. exact (h1). Qed.
Lemma lem4888835 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : s = (@UNIONS A u)) : (@UNIONS A u) = s.
Proof. exact (SYM (@lem4888834 A s u h1)). Qed.
Lemma lem4888836 {A : Type'} (s : A -> Prop) (u : type686 A) : ((@UNIONS A u) = s) = (s = (@UNIONS A u)).
Proof. exact (prop_ext (fun h1 : (@UNIONS A u) = s => @lem4888833 A u s h1) (fun h1 : s = (@UNIONS A u) => @lem4888835 A s u h1)). Qed.
Lemma lem4888837 {A : Type'} (u : type686 A) (P : type686 A) : (term218 A u P) = (term218 A u P).
Proof. exact (eq_refl (term218 A u P)). Qed.
Lemma lem4888838 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) : (term219 A P u s) = (term220 A P s u).
Proof. exact (MK_COMB (@lem4888837 A u P) (@lem4888836 A s u)). Qed.
Lemma lem4888839 {A : Type'} (u : type686 A) : (term221 A u) = (term221 A u).
Proof. exact (eq_refl (term221 A u)). Qed.
Lemma lem4888840 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) : (term222 A P u s) = (term223 A P s u).
Proof. exact (MK_COMB (@lem4888839 A u) (@lem4888838 A P s u)). Qed.
Lemma lem4888841 {A : Type'} (P : type686 A) (s : A -> Prop) : (term224 A P s) = (term225 A P s).
Proof. exact (fun_ext (fun u : type686 A => @lem4888840 A P s u)). Qed.
Lemma lem4888842 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4888843 {A : Type'} (P : type686 A) (s : A -> Prop) : (term210 A P s) = (term226 A P s).
Proof. exact (MK_COMB (@lem4888842 A) (@lem4888841 A P s)). Qed.
Lemma lem4888844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4888845 {A : Type'} (P : type686 A) (s : A -> Prop) : (term214 A P s) = (term227 A P s).
Proof. exact (MK_COMB (@lem4888844) (@lem4888843 A P s)). Qed.
Lemma lem4888854 {A : Type'} (u : type686 A) (t : A -> Prop) (h1 : (@UNIONS A u) = t) : (@UNIONS A u) = t.
Proof. exact (h1). Qed.
Lemma lem4888855 {A : Type'} (u : type686 A) (t : A -> Prop) (h1 : (@UNIONS A u) = t) : t = (@UNIONS A u).
Proof. exact (SYM (@lem4888854 A u t h1)). Qed.
Lemma lem4888856 {A : Type'} (t : A -> Prop) (u : type686 A) (h1 : t = (@UNIONS A u)) : t = (@UNIONS A u).
Proof. exact (h1). Qed.
Lemma lem4888857 {A : Type'} (t : A -> Prop) (u : type686 A) (h1 : t = (@UNIONS A u)) : (@UNIONS A u) = t.
Proof. exact (SYM (@lem4888856 A t u h1)). Qed.
Lemma lem4888858 {A : Type'} (t : A -> Prop) (u : type686 A) : ((@UNIONS A u) = t) = (t = (@UNIONS A u)).
Proof. exact (prop_ext (fun h1 : (@UNIONS A u) = t => @lem4888855 A u t h1) (fun h1 : t = (@UNIONS A u) => @lem4888857 A t u h1)). Qed.
Lemma lem4888859 {A : Type'} (u : type686 A) (P : type686 A) : (term218 A u P) = (term218 A u P).
Proof. exact (eq_refl (term218 A u P)). Qed.
Lemma lem4888860 {A : Type'} (P : type686 A) (t : A -> Prop) (u : type686 A) : (term219 A P u t) = (term220 A P t u).
Proof. exact (MK_COMB (@lem4888859 A u P) (@lem4888858 A t u)). Qed.
Lemma lem4888861 {A : Type'} (u : type686 A) : (term221 A u) = (term221 A u).
Proof. exact (eq_refl (term221 A u)). Qed.
Lemma lem4888862 {A : Type'} (P : type686 A) (t : A -> Prop) (u : type686 A) : (term222 A P u t) = (term223 A P t u).
Proof. exact (MK_COMB (@lem4888861 A u) (@lem4888860 A P t u)). Qed.
Lemma lem4888863 {A : Type'} (P : type686 A) (t : A -> Prop) : (term224 A P t) = (term225 A P t).
Proof. exact (fun_ext (fun u : type686 A => @lem4888862 A P t u)). Qed.
Lemma lem4888864 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4888865 {A : Type'} (P : type686 A) (t : A -> Prop) : (term210 A P t) = (term226 A P t).
Proof. exact (MK_COMB (@lem4888864 A) (@lem4888863 A P t)). Qed.
Lemma lem4888866 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term215 A s P t) = (term228 A s P t).
Proof. exact (MK_COMB (@lem4888845 A P s) (@lem4888865 A P t)). Qed.
Lemma lem4888867 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term215 A s P t) : term228 A s P t.
Proof. exact (EQ_MP (@lem4888866 A s P t) (@lem4888822 A s P t h1)). Qed.
Lemma lem4888868 {A : Type'} (P : type686 A) (t : A -> Prop) (h1 : term226 A P t) : term226 A P t.
Proof. exact (h1). Qed.
Lemma lem4888869 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term226 A P s) : term226 A P s.
Proof. exact (h1). Qed.
Lemma lem4888870 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term223 A P s u) : term223 A P s u.
Proof. exact (h1). Qed.
Lemma lem4888871 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term220 A P s u) : term220 A P s u.
Proof. exact (h1). Qed.
Lemma lem4888872 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : @FINITE (A -> Prop) u.
Proof. exact (h1). Qed.
Lemma lem4888873 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : s = (@UNIONS A u)) : s = (@UNIONS A u).
Proof. exact (h1). Qed.
Lemma lem4888874 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term229 A u P) : term229 A u P.
Proof. exact (h1). Qed.
Lemma lem4888875 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term223 A P t u') : term223 A P t u'.
Proof. exact (h1). Qed.
Lemma lem4888876 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term220 A P t u') : term220 A P t u'.
Proof. exact (h1). Qed.
Lemma lem4888877 {A : Type'} (u' : type686 A) (h1 : @FINITE (A -> Prop) u') : @FINITE (A -> Prop) u'.
Proof. exact (h1). Qed.
Lemma lem4888878 {A : Type'} (t : A -> Prop) (u' : type686 A) (h1 : t = (@UNIONS A u')) : t = (@UNIONS A u').
Proof. exact (h1). Qed.
Lemma lem4888879 {A : Type'} (u' : type686 A) (P : type686 A) (h1 : term229 A u' P) : term229 A u' P.
Proof. exact (h1). Qed.
Lemma lem4888880 {_87026 : Type'} : term230 _87026.
Proof. exact (proj2 (@lem3341279 Prop _87026)). Qed.
Lemma lem4888881 {_87026 : Type'} (s : type686 _87026) : term231 _87026 s.
Proof. exact (@lem4888880 _87026 s). Qed.
Lemma lem4888882 {_87026 : Type'} (s : type686 _87026) : (term231 _87026 s) = (term232 _87026 s).
Proof. exact (eq_refl (term231 _87026 s)). Qed.
Lemma lem4888883 {_87026 : Type'} (s : type686 _87026) : term232 _87026 s.
Proof. exact (EQ_MP (@lem4888882 _87026 s) (@lem4888881 _87026 s)). Qed.
Lemma lem4888884 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : term233 _87026 s t.
Proof. exact (@lem4888883 _87026 s t). Qed.
Lemma lem4888885 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term233 _87026 s t) = ((term234 _87026 t s) = (term235 _87026 s t)).
Proof. exact (eq_refl (term233 _87026 s t)). Qed.
Lemma lem4888887 {_86990 : Type'} : term236 _86990.
Proof. exact (proj1 (@lem3341279 _86990 Prop)). Qed.
Lemma lem4888888 {_86990 : Type'} (s : type686 _86990) : term237 _86990 s.
Proof. exact (@lem4888887 _86990 s). Qed.
Lemma lem4888889 {_86990 : Type'} (s : type686 _86990) : (term237 _86990 s) = (term238 _86990 s).
Proof. exact (eq_refl (term237 _86990 s)). Qed.
Lemma lem4888890 {_86990 : Type'} (s : type686 _86990) : term238 _86990 s.
Proof. exact (EQ_MP (@lem4888889 _86990 s) (@lem4888888 _86990 s)). Qed.
Lemma lem4888891 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : term239 _86990 s t.
Proof. exact (@lem4888890 _86990 s t). Qed.
Lemma lem4888892 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term239 _86990 s t) = ((term240 _86990 s t) = (term241 _86990 s t)).
Proof. exact (eq_refl (term239 _86990 s t)). Qed.
Lemma lem4888917 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : s = (@UNIONS A u)) : s = (@UNIONS A u).
Proof. exact (h1). Qed.
Lemma lem4888918 {A : Type'} : (@INTER A) = (@INTER A).
Proof. exact (eq_refl (@INTER A)). Qed.
Lemma lem4888919 {A : Type'} (s : A -> Prop) (u : type686 A) (h1 : s = (@UNIONS A u)) : (@INTER A s) = (term242 A u).
Proof. exact (MK_COMB (@lem4888918 A) (@lem4888917 A s u h1)). Qed.
Lemma lem4888921 {A : Type'} (t : A -> Prop) (u' : type686 A) (h1 : t = (@UNIONS A u')) : t = (@UNIONS A u').
Proof. exact (h1). Qed.
Lemma lem4888922 {A : Type'} (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : s = (@UNIONS A u)) (h2 : t = (@UNIONS A u')) : (@INTER A s t) = (term243 A u u').
Proof. exact (MK_COMB (@lem4888919 A s u h1) (@lem4888921 A t u' h2)). Qed.
Lemma lem4888924 {_86990 : Type'} (s : type686 _86990) (t : _86990 -> Prop) : (term240 _86990 s t) = (term241 _86990 s t).
Proof. exact (EQ_MP (@lem4888892 _86990 s t) (@lem4888891 _86990 s t)). Qed.
Lemma lem4888925 {A : Type'} (s : type686 A) (t : A -> Prop) : (term240 A s t) = (term241 A s t).
Proof. exact (@lem4888924 A s t). Qed.
Lemma lem4888926 {A : Type'} (u : type686 A) (u' : type686 A) : (term243 A u u') = (term244 A u u').
Proof. exact (@lem4888925 A u (@UNIONS A u')). Qed.
Lemma lem4888932 {_87026 : Type'} (s : type686 _87026) (t : _87026 -> Prop) : (term234 _87026 t s) = (term235 _87026 s t).
Proof. exact (EQ_MP (@lem4888885 _87026 s t) (@lem4888884 _87026 s t)). Qed.
Lemma lem4888933 {A : Type'} (s : type686 A) (t : A -> Prop) : (term234 A t s) = (term235 A s t).
Proof. exact (@lem4888932 A s t). Qed.
Lemma lem4888934 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term234 A x u') = (term235 A u' x).
Proof. exact (@lem4888933 A u' x). Qed.
Lemma lem4888939 {A : Type'} (GEN_PVAR_21 : A -> Prop) (x : A -> Prop) (u : type686 A) : (term245 A GEN_PVAR_21 x u) = (term245 A GEN_PVAR_21 x u).
Proof. exact (eq_refl (term245 A GEN_PVAR_21 x u)). Qed.
Lemma lem4888940 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) (x : A -> Prop) : (term246 A GEN_PVAR_21 u x u') = (term247 A GEN_PVAR_21 u u' x).
Proof. exact (MK_COMB (@lem4888939 A GEN_PVAR_21 x u) (@lem4888934 A u' x)). Qed.
Lemma lem4888941 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) : (term248 A GEN_PVAR_21 u u') = (term249 A GEN_PVAR_21 u u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4888940 A GEN_PVAR_21 u u' x)). Qed.
Lemma lem4888942 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4888943 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) : (term250 A GEN_PVAR_21 u u') = (term251 A GEN_PVAR_21 u u').
Proof. exact (MK_COMB (@lem4888942 A) (@lem4888941 A GEN_PVAR_21 u u')). Qed.
Lemma lem4888948 {A : Type'} (u : type686 A) (u' : type686 A) : (term252 A u u') = (term253 A u u').
Proof. exact (fun_ext (fun GEN_PVAR_21 : A -> Prop => @lem4888943 A GEN_PVAR_21 u u')). Qed.
Lemma lem4888949 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4888950 {A : Type'} (u : type686 A) (u' : type686 A) : (term254 A u u') = (term255 A u u').
Proof. exact (MK_COMB (@lem4888949 A) (@lem4888948 A u u')). Qed.
Lemma lem4888951 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4888952 {A : Type'} (u : type686 A) (u' : type686 A) : (term244 A u u') = (term256 A u u').
Proof. exact (MK_COMB (@lem4888951 A) (@lem4888950 A u u')). Qed.
Lemma lem4888953 {A : Type'} (u : type686 A) (u' : type686 A) : (term243 A u u') = (term256 A u u').
Proof. exact (TRANS (@lem4888926 A u u') (@lem4888952 A u u')). Qed.
Lemma lem4888954 {A : Type'} (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : s = (@UNIONS A u)) (h2 : t = (@UNIONS A u')) : (@INTER A s t) = (term256 A u u').
Proof. exact (TRANS (@lem4888922 A s u t u' h1 h2) (@lem4888953 A u u')). Qed.
Lemma lem4888955 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@UNION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (eq_refl (@UNION_OF A (@FINITE (A -> Prop)) P)). Qed.
Lemma lem4888956 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : s = (@UNIONS A u)) (h2 : t = (@UNIONS A u')) : (term54 A P s t) = (term257 A P u u').
Proof. exact (MK_COMB (@lem4888955 A P) (@lem4888954 A s u t u' h1 h2)). Qed.
Lemma lem4888957 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : s = (@UNIONS A u)) (h2 : t = (@UNIONS A u')) : (term257 A P u u') = (term54 A P s t).
Proof. exact (SYM (@lem4888956 A P s u t u' h1 h2)). Qed.
Lemma lem4888959 {A : Type'} (P : type686 A) (u : type686 A) : term4 A P u.
Proof. exact (EQ_MP (@lem4887688 A P u) (@lem4887687 A P u)). Qed.
Lemma lem4888960 {A : Type'} (P : type686 A) (u : type686 A) : term4 A P u.
Proof. exact (@lem4888959 A P u). Qed.
Lemma lem4888961 {A : Type'} (P : type686 A) (u : type686 A) (u' : type686 A) : term258 A P u u'.
Proof. exact (@lem4888960 A P (term255 A u u')). Qed.
Lemma lem4888962 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term259 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4888963 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term259 _87967 _87968 P f) = (term260 _87967 _87968 P f).
Proof. exact (eq_refl (term259 _87967 _87968 P f)). Qed.
Lemma lem4888964 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term260 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4888963 _87967 _87968 P f) (@lem4888962 _87967 _87968 P f)). Qed.
Lemma lem4888965 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term261 _87967 _87968 P f s.
Proof. exact (@lem4888964 _87967 _87968 P f s). Qed.
Lemma lem4888966 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term261 _87967 _87968 P f s) = ((term262 _87967 _87968 f s P) = (term263 _87967 _87968 s P f)).
Proof. exact (eq_refl (term261 _87967 _87968 P f s)). Qed.
Lemma lem4888968 {A B : Type'} (f : A -> B) : term264 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem4888969 {A B : Type'} (f : A -> B) : (term264 A B f) = (term265 A B f).
Proof. exact (eq_refl (term264 A B f)). Qed.
Lemma lem4888970 {A B : Type'} (f : A -> B) : term265 A B f.
Proof. exact (EQ_MP (@lem4888969 A B f) (@lem4888968 A B f)). Qed.
Lemma lem4888971 {A B : Type'} (f : A -> B) (s : A -> Prop) : term266 A B f s.
Proof. exact (@lem4888970 A B f s). Qed.
Lemma lem4888972 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term266 A B f s) = (term267 A B f s).
Proof. exact (eq_refl (term266 A B f s)). Qed.
Lemma lem4888973 {A B : Type'} (f : A -> B) (s : A -> Prop) : term267 A B f s.
Proof. exact (EQ_MP (@lem4888972 A B f s) (@lem4888971 A B f s)). Qed.
Lemma lem4888974 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4888975 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term268 A B f s.
Proof. exact (@lem4888973 A B f s (@lem4888974 A s h1)). Qed.
Lemma lem4888976 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term268 A B f s) = ((term268 A B f s) = True).
Proof. exact (@lem7 (term268 A B f s)). Qed.
Lemma lem4888977 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term268 A B f s) = True.
Proof. exact (EQ_MP (@lem4888976 A B f s) (@lem4888975 A B f s h1)). Qed.
Lemma lem4888983 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term269 _88128 _88132 f.
Proof. exact (@lem3393993 _88128 _88132 f). Qed.
Lemma lem4888984 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term269 _88128 _88132 f) = (term270 _88128 _88132 f).
Proof. exact (eq_refl (term269 _88128 _88132 f)). Qed.
Lemma lem4888985 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term270 _88128 _88132 f.
Proof. exact (EQ_MP (@lem4888984 _88128 _88132 f) (@lem4888983 _88128 _88132 f)). Qed.
Lemma lem4888986 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : term271 _88128 _88132 f s.
Proof. exact (@lem4888985 _88128 _88132 f s). Qed.
Lemma lem4888987 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term271 _88128 _88132 f s) = ((term272 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)).
Proof. exact (eq_refl (term271 _88128 _88132 f s)). Qed.
Lemma lem4889004 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = ((@FINITE (A -> Prop) u) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) u)). Qed.
Lemma lem4889035 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term272 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem4888987 _88128 _88132 f s) (@lem4888986 _88128 _88132 f s)). Qed.
Lemma lem4889036 {A : Type'} (f : type672 A) (s : type686 A) : (term273 A s f) = (@IMAGE (A -> Prop) (A -> Prop) f s).
Proof. exact (@lem4889035 (A -> Prop) (A -> Prop) f s). Qed.
Lemma lem4889037 {A : Type'} (u' : type686 A) (u : type686 A) : (term274 A u u') = (term275 A u' u).
Proof. exact (@lem4889036 A (term276 A u') u). Qed.
Lemma lem4889038 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term277 A u' x) = (term235 A u' x).
Proof. exact (eq_refl (term277 A u' x)). Qed.
Lemma lem4889039 {A : Type'} (GEN_PVAR_21 : A -> Prop) (x : A -> Prop) (u : type686 A) : (term245 A GEN_PVAR_21 x u) = (term245 A GEN_PVAR_21 x u).
Proof. exact (eq_refl (term245 A GEN_PVAR_21 x u)). Qed.
Lemma lem4889040 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) (x : A -> Prop) : (term278 A GEN_PVAR_21 u u' x) = (term247 A GEN_PVAR_21 u u' x).
Proof. exact (MK_COMB (@lem4889039 A GEN_PVAR_21 x u) (@lem4889038 A u' x)). Qed.
Lemma lem4889041 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) : (term279 A GEN_PVAR_21 u u') = (term249 A GEN_PVAR_21 u u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4889040 A GEN_PVAR_21 u u' x)). Qed.
Lemma lem4889042 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4889043 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) : (term280 A GEN_PVAR_21 u u') = (term251 A GEN_PVAR_21 u u').
Proof. exact (MK_COMB (@lem4889042 A) (@lem4889041 A GEN_PVAR_21 u u')). Qed.
Lemma lem4889044 {A : Type'} (u : type686 A) (u' : type686 A) : (term281 A u u') = (term253 A u u').
Proof. exact (fun_ext (fun GEN_PVAR_21 : A -> Prop => @lem4889043 A GEN_PVAR_21 u u')). Qed.
Lemma lem4889045 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4889046 {A : Type'} (u : type686 A) (u' : type686 A) : (term274 A u u') = (term255 A u u').
Proof. exact (MK_COMB (@lem4889045 A) (@lem4889044 A u u')). Qed.
Lemma lem4889047 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4889048 {A : Type'} (u : type686 A) (u' : type686 A) : (term282 A u u') = (term283 A u u').
Proof. exact (MK_COMB (@lem4889047 A) (@lem4889046 A u u')). Qed.
Lemma lem4889049 {A : Type'} (u' : type686 A) (u : type686 A) : (term275 A u' u) = (term275 A u' u).
Proof. exact (eq_refl (term275 A u' u)). Qed.
Lemma lem4889050 {A : Type'} (u' : type686 A) (u : type686 A) : ((term274 A u u') = (term275 A u' u)) = ((term255 A u u') = (term275 A u' u)).
Proof. exact (MK_COMB (@lem4889048 A u u') (@lem4889049 A u' u)). Qed.
Lemma lem4889051 {A : Type'} (u' : type686 A) (u : type686 A) : (term255 A u u') = (term275 A u' u).
Proof. exact (EQ_MP (@lem4889050 A u' u) (@lem4889037 A u' u)). Qed.
Lemma lem4889053 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term272 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem4888987 _88128 _88132 f s) (@lem4888986 _88128 _88132 f s)). Qed.
Lemma lem4889054 {A : Type'} (f : type672 A) (s : type686 A) : (term273 A s f) = (@IMAGE (A -> Prop) (A -> Prop) f s).
Proof. exact (@lem4889053 (A -> Prop) (A -> Prop) f s). Qed.
Lemma lem4889055 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term284 A u' x) = (term285 A x u').
Proof. exact (@lem4889054 A (term286 A x) u'). Qed.
Lemma lem4889056 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term287 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term287 A x x')). Qed.
Lemma lem4889057 {A : Type'} (GEN_PVAR_22 : A -> Prop) (x' : A -> Prop) (u' : type686 A) : (term245 A GEN_PVAR_22 x' u') = (term245 A GEN_PVAR_22 x' u').
Proof. exact (eq_refl (term245 A GEN_PVAR_22 x' u')). Qed.
Lemma lem4889058 {A : Type'} (GEN_PVAR_22 : A -> Prop) (u' : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term288 A GEN_PVAR_22 u' x x') = (term289 A GEN_PVAR_22 u' x x').
Proof. exact (MK_COMB (@lem4889057 A GEN_PVAR_22 x' u') (@lem4889056 A x x')). Qed.
Lemma lem4889059 {A : Type'} (GEN_PVAR_22 : A -> Prop) (u' : type686 A) (x : A -> Prop) : (term290 A GEN_PVAR_22 u' x) = (term291 A GEN_PVAR_22 u' x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4889058 A GEN_PVAR_22 u' x x')). Qed.
Lemma lem4889060 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4889061 {A : Type'} (GEN_PVAR_22 : A -> Prop) (u' : type686 A) (x : A -> Prop) : (term292 A GEN_PVAR_22 u' x) = (term293 A GEN_PVAR_22 u' x).
Proof. exact (MK_COMB (@lem4889060 A) (@lem4889059 A GEN_PVAR_22 u' x)). Qed.
Lemma lem4889062 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term294 A u' x) = (term295 A u' x).
Proof. exact (fun_ext (fun GEN_PVAR_22 : A -> Prop => @lem4889061 A GEN_PVAR_22 u' x)). Qed.
Lemma lem4889063 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4889064 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term284 A u' x) = (term296 A u' x).
Proof. exact (MK_COMB (@lem4889063 A) (@lem4889062 A u' x)). Qed.
Lemma lem4889065 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4889066 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term297 A u' x) = (term298 A u' x).
Proof. exact (MK_COMB (@lem4889065 A) (@lem4889064 A u' x)). Qed.
Lemma lem4889067 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term285 A x u') = (term285 A x u').
Proof. exact (eq_refl (term285 A x u')). Qed.
Lemma lem4889068 {A : Type'} (x : A -> Prop) (u' : type686 A) : ((term284 A u' x) = (term285 A x u')) = ((term296 A u' x) = (term285 A x u')).
Proof. exact (MK_COMB (@lem4889066 A u' x) (@lem4889067 A x u')). Qed.
Lemma lem4889069 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term296 A u' x) = (term285 A x u').
Proof. exact (EQ_MP (@lem4889068 A x u') (@lem4889055 A x u')). Qed.
Lemma lem4889070 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4889071 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term235 A u' x) = (term299 A x u').
Proof. exact (MK_COMB (@lem4889070 A) (@lem4889069 A x u')). Qed.
Lemma lem4889072 {A : Type'} (u' : type686 A) : (term276 A u') = (term300 A u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4889071 A x u')). Qed.
Lemma lem4889073 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4889074 {A : Type'} (u' : type686 A) : (term301 A u') = (term302 A u').
Proof. exact (MK_COMB (@lem4889073 A) (@lem4889072 A u')). Qed.
Lemma lem4889075 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4889076 {A : Type'} (u' : type686 A) (u : type686 A) : (term275 A u' u) = (term303 A u' u).
Proof. exact (MK_COMB (@lem4889074 A u') (@lem4889075 A u)). Qed.
Lemma lem4889077 {A : Type'} (u' : type686 A) (u : type686 A) : (term255 A u u') = (term303 A u' u).
Proof. exact (TRANS (@lem4889051 A u' u) (@lem4889076 A u' u)). Qed.
Lemma lem4889078 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem4889079 {A : Type'} (u' : type686 A) (u : type686 A) : (term304 A u u') = (term305 A u' u).
Proof. exact (MK_COMB (@lem4889078 A) (@lem4889077 A u' u)). Qed.
Lemma lem4889081 {A B : Type'} (f : A -> B) (s : A -> Prop) : term306 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4888977 A B f s h0). Qed.
Lemma lem4889082 {A : Type'} (f : type672 A) (s : type686 A) : term307 A f s.
Proof. exact (@lem4889081 (A -> Prop) (A -> Prop) f s). Qed.
Lemma lem4889083 {A : Type'} (u' : type686 A) (u : type686 A) : term308 A u' u.
Proof. exact (@lem4889082 A (term300 A u') u). Qed.
Lemma lem4889085 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (@FINITE (A -> Prop) u) = True.
Proof. exact (EQ_MP (@lem4889004 A u) (@lem4888872 A u h1)). Qed.
Lemma lem4889086 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : True = (@FINITE (A -> Prop) u).
Proof. exact (SYM (@lem4889085 A u h1)). Qed.
Lemma lem4889087 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : @FINITE (A -> Prop) u.
Proof. exact (EQ_MP (@lem4889086 A u h1) (@lem0)). Qed.
Lemma lem4889088 {A : Type'} (u' : type686 A) (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term305 A u' u) = True.
Proof. exact (@lem4889083 A u' u (@lem4889087 A u h1)). Qed.
Lemma lem4889089 {A : Type'} (u' : type686 A) (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term304 A u u') = True.
Proof. exact (TRANS (@lem4889079 A u' u) (@lem4889088 A u' u h1)). Qed.
Lemma lem4889090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4889091 {A : Type'} (u' : type686 A) (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term309 A u u') = (and True).
Proof. exact (MK_COMB (@lem4889090) (@lem4889089 A u' u h1)). Qed.
Lemma lem4889196 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term310 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4889197 (p : Prop) (q : Prop) (p' : Prop) : term311 p q p'.
Proof. exact (fun q' : Prop => @lem4889196 p q p' q'). Qed.
Lemma lem4889198 (p : Prop) (q : Prop) : term312 p q.
Proof. exact (fun p' : Prop => @lem4889197 p q p'). Qed.
Lemma lem4889199 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60403 : A -> Prop) : term313 A u u' P _60403.
Proof. exact (@lem4889198 (term314 A _60403 u u') (@UNION_OF A (@FINITE (A -> Prop)) P _60403)). Qed.
Lemma lem4889200 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60403 : A -> Prop) (p' : Prop) : term315 A u u' P _60403 p'.
Proof. exact (@lem4889199 A u u' P _60403 p'). Qed.
Lemma lem4889201 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60403 : A -> Prop) (p' : Prop) : (term315 A u u' P _60403 p') = (term316 A u u' P _60403 p').
Proof. exact (eq_refl (term315 A u u' P _60403 p')). Qed.
Lemma lem4889202 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60403 : A -> Prop) (p' : Prop) : term316 A u u' P _60403 p'.
Proof. exact (EQ_MP (@lem4889201 A u u' P _60403 p') (@lem4889200 A u u' P _60403 p')). Qed.
Lemma lem4889203 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60403 : A -> Prop) (p' : Prop) (q' : Prop) : term317 A u u' P _60403 p' q'.
Proof. exact (@lem4889202 A u u' P _60403 p' q'). Qed.
Lemma lem4889204 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60403 : A -> Prop) (p' : Prop) (q' : Prop) : (term317 A u u' P _60403 p' q') = (term318 A u u' P _60403 p' q').
Proof. exact (eq_refl (term317 A u u' P _60403 p' q')). Qed.
Lemma lem4889205 {A : Type'} (u : type686 A) (u' : type686 A) (P : type686 A) (_60403 : A -> Prop) (p' : Prop) (q' : Prop) : term318 A u u' P _60403 p' q'.
Proof. exact (EQ_MP (@lem4889204 A u u' P _60403 p' q') (@lem4889203 A u u' P _60403 p' q')). Qed.
Lemma lem4889207 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term272 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem4888987 _88128 _88132 f s) (@lem4888986 _88128 _88132 f s)). Qed.
Lemma lem4889208 {A : Type'} (f : type672 A) (s : type686 A) : (term273 A s f) = (@IMAGE (A -> Prop) (A -> Prop) f s).
Proof. exact (@lem4889207 (A -> Prop) (A -> Prop) f s). Qed.
Lemma lem4889209 {A : Type'} (u' : type686 A) (u : type686 A) : (term274 A u u') = (term275 A u' u).
Proof. exact (@lem4889208 A (term276 A u') u). Qed.
Lemma lem4889210 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term277 A u' x) = (term235 A u' x).
Proof. exact (eq_refl (term277 A u' x)). Qed.
Lemma lem4889211 {A : Type'} (GEN_PVAR_21 : A -> Prop) (x : A -> Prop) (u : type686 A) : (term245 A GEN_PVAR_21 x u) = (term245 A GEN_PVAR_21 x u).
Proof. exact (eq_refl (term245 A GEN_PVAR_21 x u)). Qed.
Lemma lem4889212 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) (x : A -> Prop) : (term278 A GEN_PVAR_21 u u' x) = (term247 A GEN_PVAR_21 u u' x).
Proof. exact (MK_COMB (@lem4889211 A GEN_PVAR_21 x u) (@lem4889210 A u' x)). Qed.
Lemma lem4889213 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) : (term279 A GEN_PVAR_21 u u') = (term249 A GEN_PVAR_21 u u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4889212 A GEN_PVAR_21 u u' x)). Qed.
Lemma lem4889214 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4889215 {A : Type'} (GEN_PVAR_21 : A -> Prop) (u : type686 A) (u' : type686 A) : (term280 A GEN_PVAR_21 u u') = (term251 A GEN_PVAR_21 u u').
Proof. exact (MK_COMB (@lem4889214 A) (@lem4889213 A GEN_PVAR_21 u u')). Qed.
Lemma lem4889216 {A : Type'} (u : type686 A) (u' : type686 A) : (term281 A u u') = (term253 A u u').
Proof. exact (fun_ext (fun GEN_PVAR_21 : A -> Prop => @lem4889215 A GEN_PVAR_21 u u')). Qed.
Lemma lem4889217 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4889218 {A : Type'} (u : type686 A) (u' : type686 A) : (term274 A u u') = (term255 A u u').
Proof. exact (MK_COMB (@lem4889217 A) (@lem4889216 A u u')). Qed.
Lemma lem4889219 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4889220 {A : Type'} (u : type686 A) (u' : type686 A) : (term282 A u u') = (term283 A u u').
Proof. exact (MK_COMB (@lem4889219 A) (@lem4889218 A u u')). Qed.
Lemma lem4889221 {A : Type'} (u' : type686 A) (u : type686 A) : (term275 A u' u) = (term275 A u' u).
Proof. exact (eq_refl (term275 A u' u)). Qed.
Lemma lem4889222 {A : Type'} (u' : type686 A) (u : type686 A) : ((term274 A u u') = (term275 A u' u)) = ((term255 A u u') = (term275 A u' u)).
Proof. exact (MK_COMB (@lem4889220 A u u') (@lem4889221 A u' u)). Qed.
Lemma lem4889223 {A : Type'} (u' : type686 A) (u : type686 A) : (term255 A u u') = (term275 A u' u).
Proof. exact (EQ_MP (@lem4889222 A u' u) (@lem4889209 A u' u)). Qed.
Lemma lem4889225 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term272 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem4888987 _88128 _88132 f s) (@lem4888986 _88128 _88132 f s)). Qed.
Lemma lem4889226 {A : Type'} (f : type672 A) (s : type686 A) : (term273 A s f) = (@IMAGE (A -> Prop) (A -> Prop) f s).
Proof. exact (@lem4889225 (A -> Prop) (A -> Prop) f s). Qed.
Lemma lem4889227 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term284 A u' x) = (term285 A x u').
Proof. exact (@lem4889226 A (term286 A x) u'). Qed.
Lemma lem4889228 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term287 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term287 A x x')). Qed.
Lemma lem4889229 {A : Type'} (GEN_PVAR_22 : A -> Prop) (x' : A -> Prop) (u' : type686 A) : (term245 A GEN_PVAR_22 x' u') = (term245 A GEN_PVAR_22 x' u').
Proof. exact (eq_refl (term245 A GEN_PVAR_22 x' u')). Qed.
Lemma lem4889230 {A : Type'} (GEN_PVAR_22 : A -> Prop) (u' : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term288 A GEN_PVAR_22 u' x x') = (term289 A GEN_PVAR_22 u' x x').
Proof. exact (MK_COMB (@lem4889229 A GEN_PVAR_22 x' u') (@lem4889228 A x x')). Qed.
Lemma lem4889231 {A : Type'} (GEN_PVAR_22 : A -> Prop) (u' : type686 A) (x : A -> Prop) : (term290 A GEN_PVAR_22 u' x) = (term291 A GEN_PVAR_22 u' x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4889230 A GEN_PVAR_22 u' x x')). Qed.
Lemma lem4889232 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4889233 {A : Type'} (GEN_PVAR_22 : A -> Prop) (u' : type686 A) (x : A -> Prop) : (term292 A GEN_PVAR_22 u' x) = (term293 A GEN_PVAR_22 u' x).
Proof. exact (MK_COMB (@lem4889232 A) (@lem4889231 A GEN_PVAR_22 u' x)). Qed.
Lemma lem4889234 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term294 A u' x) = (term295 A u' x).
Proof. exact (fun_ext (fun GEN_PVAR_22 : A -> Prop => @lem4889233 A GEN_PVAR_22 u' x)). Qed.
Lemma lem4889235 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4889236 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term284 A u' x) = (term296 A u' x).
Proof. exact (MK_COMB (@lem4889235 A) (@lem4889234 A u' x)). Qed.
Lemma lem4889237 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4889238 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term297 A u' x) = (term298 A u' x).
Proof. exact (MK_COMB (@lem4889237 A) (@lem4889236 A u' x)). Qed.
Lemma lem4889239 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term285 A x u') = (term285 A x u').
Proof. exact (eq_refl (term285 A x u')). Qed.
Lemma lem4889240 {A : Type'} (x : A -> Prop) (u' : type686 A) : ((term284 A u' x) = (term285 A x u')) = ((term296 A u' x) = (term285 A x u')).
Proof. exact (MK_COMB (@lem4889238 A u' x) (@lem4889239 A x u')). Qed.
Lemma lem4889241 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term296 A u' x) = (term285 A x u').
Proof. exact (EQ_MP (@lem4889240 A x u') (@lem4889227 A x u')). Qed.
Lemma lem4889242 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4889243 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term235 A u' x) = (term299 A x u').
Proof. exact (MK_COMB (@lem4889242 A) (@lem4889241 A x u')). Qed.
Lemma lem4889244 {A : Type'} (u' : type686 A) : (term276 A u') = (term300 A u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4889243 A x u')). Qed.
Lemma lem4889245 {A : Type'} : (@IMAGE (A -> Prop) (A -> Prop)) = (@IMAGE (A -> Prop) (A -> Prop)).
Proof. exact (eq_refl (@IMAGE (A -> Prop) (A -> Prop))). Qed.
Lemma lem4889246 {A : Type'} (u' : type686 A) : (term301 A u') = (term302 A u').
Proof. exact (MK_COMB (@lem4889245 A) (@lem4889244 A u')). Qed.
Lemma lem4889247 {A : Type'} (u : type686 A) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4889248 {A : Type'} (u' : type686 A) (u : type686 A) : (term275 A u' u) = (term303 A u' u).
Proof. exact (MK_COMB (@lem4889246 A u') (@lem4889247 A u)). Qed.
Lemma lem4889249 {A : Type'} (u' : type686 A) (u : type686 A) : (term255 A u u') = (term303 A u' u).
Proof. exact (TRANS (@lem4889223 A u' u) (@lem4889248 A u' u)). Qed.
Lemma lem4889250 {A : Type'} (_60403 : A -> Prop) : (@IN (A -> Prop) _60403) = (@IN (A -> Prop) _60403).
Proof. exact (eq_refl (@IN (A -> Prop) _60403)). Qed.
Lemma lem4889251 {A : Type'} (_60403 : A -> Prop) (u' : type686 A) (u : type686 A) : (term314 A _60403 u u') = (term319 A _60403 u' u).
Proof. exact (MK_COMB (@lem4889250 A _60403) (@lem4889249 A u' u)). Qed.
Lemma lem4889252 {A : Type'} (P : type686 A) (_60403 : A -> Prop) (u' : type686 A) (u : type686 A) (q' : Prop) : term320 A P _60403 u' u q'.
Proof. exact (@lem4889205 A u u' P _60403 (term319 A _60403 u' u) q'). Qed.
Lemma lem4889253 {A : Type'} (P : type686 A) (_60403 : A -> Prop) (u' : type686 A) (u : type686 A) (q' : Prop) : term321 A P _60403 u' u q'.
Proof. exact (@lem4889252 A P _60403 u' u q' (@lem4889251 A _60403 u' u)). Qed.
Lemma lem4889257 {A : Type'} (P : type686 A) (_60403 : A -> Prop) : (@UNION_OF A (@FINITE (A -> Prop)) P _60403) = (@UNION_OF A (@FINITE (A -> Prop)) P _60403).
Proof. exact (eq_refl (@UNION_OF A (@FINITE (A -> Prop)) P _60403)). Qed.
Lemma lem4889258 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) (_60403 : A -> Prop) : term322 A u' u P _60403.
Proof. exact (fun h0 : term319 A _60403 u' u => @lem4889257 A P _60403). Qed.
Lemma lem4889259 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) (_60403 : A -> Prop) : term323 A u' u P _60403.
Proof. exact (@lem4889253 A P _60403 u' u (@UNION_OF A (@FINITE (A -> Prop)) P _60403)). Qed.
Lemma lem4889260 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) (_60403 : A -> Prop) : (term324 A u u' P _60403) = (term325 A u' u P _60403).
Proof. exact (@lem4889259 A u' u P _60403 (@lem4889258 A u' u P _60403)). Qed.
Lemma lem4889286 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) : (term326 A u u' P) = (term327 A u' u P).
Proof. exact (fun_ext (fun _60403 : A -> Prop => @lem4889260 A u' u P _60403)). Qed.
Lemma lem4889364 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4889365 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) : (term328 A u u' P) = (term329 A u' u P).
Proof. exact (MK_COMB (@lem4889364 A) (@lem4889286 A u' u P)). Qed.
Lemma lem4889367 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term262 _87967 _87968 f s P) = (term263 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4888966 _87967 _87968 s P f) (@lem4888965 _87967 _87968 P f s)). Qed.
Lemma lem4889368 {A : Type'} (s : type686 A) (P : type686 A) (f : type672 A) : (term330 A f s P) = (term331 A s P f).
Proof. exact (@lem4889367 (A -> Prop) (A -> Prop) s P f). Qed.
Lemma lem4889369 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term332 A u' u P) = (term333 A u P u').
Proof. exact (@lem4889368 A u (term334 A P) (term300 A u')). Qed.
Lemma lem4889370 {A : Type'} (P : type686 A) (s : A -> Prop) : (term335 A P s) = (@UNION_OF A (@FINITE (A -> Prop)) P s).
Proof. exact (eq_refl (term335 A P s)). Qed.
Lemma lem4889371 {A : Type'} (s : A -> Prop) (u' : type686 A) (u : type686 A) : (term336 A s u' u) = (term336 A s u' u).
Proof. exact (eq_refl (term336 A s u' u)). Qed.
Lemma lem4889372 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) (s : A -> Prop) : (term337 A u' u P s) = (term325 A u' u P s).
Proof. exact (MK_COMB (@lem4889371 A s u' u) (@lem4889370 A P s)). Qed.
Lemma lem4889373 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) : (term338 A u' u P) = (term327 A u' u P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4889372 A u' u P s)). Qed.
Lemma lem4889374 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4889375 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) : (term332 A u' u P) = (term329 A u' u P).
Proof. exact (MK_COMB (@lem4889374 A) (@lem4889373 A u' u P)). Qed.
Lemma lem4889376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4889377 {A : Type'} (u' : type686 A) (u : type686 A) (P : type686 A) : (term339 A u' u P) = (term340 A u' u P).
Proof. exact (MK_COMB (@lem4889376) (@lem4889375 A u' u P)). Qed.
Lemma lem4889378 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) : (term341 A P u' x) = (term342 A P u' x).
Proof. exact (eq_refl (term341 A P u' x)). Qed.
Lemma lem4889379 {A : Type'} (x : A -> Prop) (u : type686 A) : (term343 A x u) = (term343 A x u).
Proof. exact (eq_refl (term343 A x u)). Qed.
Lemma lem4889380 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) : (term344 A u P u' x) = (term345 A u P u' x).
Proof. exact (MK_COMB (@lem4889379 A x u) (@lem4889378 A P u' x)). Qed.
Lemma lem4889381 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term346 A u P u') = (term347 A u P u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4889380 A u P u' x)). Qed.
Lemma lem4889382 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4889383 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term333 A u P u') = (term348 A u P u').
Proof. exact (MK_COMB (@lem4889382 A) (@lem4889381 A u P u')). Qed.
Lemma lem4889384 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : ((term332 A u' u P) = (term333 A u P u')) = ((term329 A u' u P) = (term348 A u P u')).
Proof. exact (MK_COMB (@lem4889377 A u' u P) (@lem4889383 A u P u')). Qed.
Lemma lem4889385 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term329 A u' u P) = (term348 A u P u').
Proof. exact (EQ_MP (@lem4889384 A u P u') (@lem4889369 A u P u')). Qed.
Lemma lem4889393 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term310 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4889394 (p : Prop) (q : Prop) (p' : Prop) : term311 p q p'.
Proof. exact (fun q' : Prop => @lem4889393 p q p' q'). Qed.
Lemma lem4889395 (p : Prop) (q : Prop) : term312 p q.
Proof. exact (fun p' : Prop => @lem4889394 p q p'). Qed.
Lemma lem4889396 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) : term349 A u P u' x.
Proof. exact (@lem4889395 (@IN (A -> Prop) x u) (term342 A P u' x)). Qed.
Lemma lem4889397 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) (p' : Prop) : term350 A u P u' x p'.
Proof. exact (@lem4889396 A u P u' x p'). Qed.
Lemma lem4889398 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) (p' : Prop) : (term350 A u P u' x p') = (term351 A u P u' x p').
Proof. exact (eq_refl (term350 A u P u' x p')). Qed.
Lemma lem4889399 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) (p' : Prop) : term351 A u P u' x p'.
Proof. exact (EQ_MP (@lem4889398 A u P u' x p') (@lem4889397 A u P u' x p')). Qed.
Lemma lem4889400 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : term352 A u P u' x p' q'.
Proof. exact (@lem4889399 A u P u' x p' q'). Qed.
Lemma lem4889401 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : (term352 A u P u' x p' q') = (term353 A u P u' x p' q').
Proof. exact (eq_refl (term352 A u P u' x p' q')). Qed.
Lemma lem4889402 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (x : A -> Prop) (p' : Prop) (q' : Prop) : term353 A u P u' x p' q'.
Proof. exact (EQ_MP (@lem4889401 A u P u' x p' q') (@lem4889400 A u P u' x p' q')). Qed.
Lemma lem4889403 {A : Type'} (x : A -> Prop) (u : type686 A) : (@IN (A -> Prop) x u) = (@IN (A -> Prop) x u).
Proof. exact (eq_refl (@IN (A -> Prop) x u)). Qed.
Lemma lem4889404 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) (u : type686 A) (q' : Prop) : term354 A P u' x u q'.
Proof. exact (@lem4889402 A u P u' x (@IN (A -> Prop) x u) q'). Qed.
Lemma lem4889405 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) (u : type686 A) (q' : Prop) : term355 A P u' x u q'.
Proof. exact (@lem4889404 A P u' x u q' (@lem4889403 A x u)). Qed.
Lemma lem4889410 {A B : Type'} (f : A -> B) (y : A) : (term207 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4889411 {A : Type'} (f : type672 A) (y : A -> Prop) : (term356 A f y) = (f y).
Proof. exact (@lem4889410 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4889412 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term357 A u' x) = (term358 A u' x).
Proof. exact (@lem4889411 A (term300 A u') x). Qed.
Lemma lem4889413 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term358 A u' x) = (term299 A x u').
Proof. exact (eq_refl (term358 A u' x)). Qed.
Lemma lem4889414 {A : Type'} (u' : type686 A) : (term359 A u') = (term300 A u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4889413 A x u')). Qed.
Lemma lem4889415 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4889416 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term357 A u' x) = (term358 A u' x).
Proof. exact (MK_COMB (@lem4889414 A u') (@lem4889415 A x)). Qed.
Lemma lem4889417 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4889418 {A : Type'} (u' : type686 A) (x : A -> Prop) : (term360 A u' x) = (term361 A u' x).
Proof. exact (MK_COMB (@lem4889417 A) (@lem4889416 A u' x)). Qed.
Lemma lem4889419 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term358 A u' x) = (term299 A x u').
Proof. exact (eq_refl (term358 A u' x)). Qed.
Lemma lem4889420 {A : Type'} (x : A -> Prop) (u' : type686 A) : ((term357 A u' x) = (term358 A u' x)) = ((term358 A u' x) = (term299 A x u')).
Proof. exact (MK_COMB (@lem4889418 A u' x) (@lem4889419 A x u')). Qed.
Lemma lem4889421 {A : Type'} (x : A -> Prop) (u' : type686 A) : (term358 A u' x) = (term299 A x u').
Proof. exact (EQ_MP (@lem4889420 A x u') (@lem4889412 A u' x)). Qed.
Lemma lem4889422 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@UNION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (eq_refl (@UNION_OF A (@FINITE (A -> Prop)) P)). Qed.
Lemma lem4889423 {A : Type'} (P : type686 A) (x : A -> Prop) (u' : type686 A) : (term342 A P u' x) = (term362 A P x u').
Proof. exact (MK_COMB (@lem4889422 A P) (@lem4889421 A x u')). Qed.
Lemma lem4889424 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (u' : type686 A) : term363 A u P x u'.
Proof. exact (fun h0 : @IN (A -> Prop) x u => @lem4889423 A P x u'). Qed.
Lemma lem4889425 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (u' : type686 A) : term364 A u P x u'.
Proof. exact (@lem4889405 A P u' x u (term362 A P x u')). Qed.
Lemma lem4889426 {A : Type'} (u : type686 A) (P : type686 A) (x : A -> Prop) (u' : type686 A) : (term345 A u P u' x) = (term365 A u P x u').
Proof. exact (@lem4889425 A u P x u' (@lem4889424 A u P x u')). Qed.
Lemma lem4889450 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term347 A u P u') = (term366 A u P u').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4889426 A u P x u')). Qed.
Lemma lem4889474 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4889475 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term348 A u P u') = (term367 A u P u').
Proof. exact (MK_COMB (@lem4889474 A) (@lem4889450 A u P u')). Qed.
Lemma lem4889503 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term329 A u' u P) = (term367 A u P u').
Proof. exact (TRANS (@lem4889385 A u P u') (@lem4889475 A u P u')). Qed.
Lemma lem4889504 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term328 A u u' P) = (term367 A u P u').
Proof. exact (TRANS (@lem4889365 A u' u P) (@lem4889503 A u P u')). Qed.
Lemma lem4889505 {A : Type'} (P : type686 A) (u' : type686 A) (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term368 A u u' P) = (term369 A u P u').
Proof. exact (MK_COMB (@lem4889091 A u' u h1) (@lem4889504 A u P u')). Qed.
Lemma lem4889507 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4889508 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) : (term369 A u P u') = (term367 A u P u').
Proof. exact (@lem4889507 (term367 A u P u')). Qed.
Lemma lem4889536 {A : Type'} (P : type686 A) (u' : type686 A) (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term368 A u u' P) = (term367 A u P u').
Proof. exact (TRANS (@lem4889505 A P u' u h1) (@lem4889508 A u P u')). Qed.
Lemma lem4889537 {A : Type'} (u' : type686 A) (P : type686 A) (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term367 A u P u') = (term368 A u u' P).
Proof. exact (SYM (@lem4889536 A P u' u h1)). Qed.
Lemma lem4889538 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : @IN (A -> Prop) x u.
Proof. exact (h1). Qed.
Lemma lem4889540 {A : Type'} (P : type686 A) (u : type686 A) : term4 A P u.
Proof. exact (EQ_MP (@lem4887688 A P u) (@lem4887687 A P u)). Qed.
Lemma lem4889541 {A : Type'} (P : type686 A) (u : type686 A) : term4 A P u.
Proof. exact (@lem4889540 A P u). Qed.
Lemma lem4889542 {A : Type'} (P : type686 A) (x : A -> Prop) (u' : type686 A) : term370 A P x u'.
Proof. exact (@lem4889541 A P (term285 A x u')). Qed.
Lemma lem4889543 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term259 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4889544 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term259 _87967 _87968 P f) = (term260 _87967 _87968 P f).
Proof. exact (eq_refl (term259 _87967 _87968 P f)). Qed.
Lemma lem4889545 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term260 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4889544 _87967 _87968 P f) (@lem4889543 _87967 _87968 P f)). Qed.
Lemma lem4889546 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term261 _87967 _87968 P f s.
Proof. exact (@lem4889545 _87967 _87968 P f s). Qed.
Lemma lem4889547 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term261 _87967 _87968 P f s) = ((term262 _87967 _87968 f s P) = (term263 _87967 _87968 s P f)).
Proof. exact (eq_refl (term261 _87967 _87968 P f s)). Qed.
Lemma lem4889549 {A B : Type'} (f : A -> B) : term264 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem4889550 {A B : Type'} (f : A -> B) : (term264 A B f) = (term265 A B f).
Proof. exact (eq_refl (term264 A B f)). Qed.
Lemma lem4889551 {A B : Type'} (f : A -> B) : term265 A B f.
Proof. exact (EQ_MP (@lem4889550 A B f) (@lem4889549 A B f)). Qed.
Lemma lem4889552 {A B : Type'} (f : A -> B) (s : A -> Prop) : term266 A B f s.
Proof. exact (@lem4889551 A B f s). Qed.
Lemma lem4889553 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term266 A B f s) = (term267 A B f s).
Proof. exact (eq_refl (term266 A B f s)). Qed.
Lemma lem4889554 {A B : Type'} (f : A -> B) (s : A -> Prop) : term267 A B f s.
Proof. exact (EQ_MP (@lem4889553 A B f s) (@lem4889552 A B f s)). Qed.
Lemma lem4889555 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4889556 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term268 A B f s.
Proof. exact (@lem4889554 A B f s (@lem4889555 A s h1)). Qed.
Lemma lem4889557 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term268 A B f s) = ((term268 A B f s) = True).
Proof. exact (@lem7 (term268 A B f s)). Qed.
Lemma lem4889558 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term268 A B f s) = True.
Proof. exact (EQ_MP (@lem4889557 A B f s) (@lem4889556 A B f s h1)). Qed.
Lemma lem4889570 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term45 A P) : term78 A P s.
Proof. exact (@lem4888727 A P h1 s). Qed.
Lemma lem4889571 {A : Type'} (P : type686 A) (s : A -> Prop) : (term78 A P s) = (term43 A P s).
Proof. exact (eq_refl (term78 A P s)). Qed.
Lemma lem4889572 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term45 A P) : term43 A P s.
Proof. exact (EQ_MP (@lem4889571 A P s) (@lem4889570 A s P h1)). Qed.
Lemma lem4889573 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term71 A P s t.
Proof. exact (@lem4889572 A s P h1 t). Qed.
Lemma lem4889574 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term71 A P s t) = (term41 A P s t).
Proof. exact (eq_refl (term71 A P s t)). Qed.
Lemma lem4889575 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term41 A P s t.
Proof. exact (EQ_MP (@lem4889574 A P s t) (@lem4889573 A s t P h1)). Qed.
Lemma lem4889576 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term66 A s P t) : term66 A s P t.
Proof. exact (h1). Qed.
Lemma lem4889577 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term66 A s P t) : term54 A P s t.
Proof. exact (@lem4889575 A s t P h1 (@lem4889576 A s P t h2)). Qed.
Lemma lem4889578 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = ((term54 A P s t) = True).
Proof. exact (@lem7 (term54 A P s t)). Qed.
Lemma lem4889579 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term66 A s P t) : (term54 A P s t) = True.
Proof. exact (EQ_MP (@lem4889578 A P s t) (@lem4889577 A s P t h1 h2)). Qed.
Lemma lem4889587 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term229 A u P) : term371 A u P c.
Proof. exact (@lem4888874 A u P h1 c). Qed.
Lemma lem4889588 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term371 A u P c) = (term372 A u P c).
Proof. exact (eq_refl (term371 A u P c)). Qed.
Lemma lem4889589 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term229 A u P) : term372 A u P c.
Proof. exact (EQ_MP (@lem4889588 A u P c) (@lem4889587 A c u P h1)). Qed.
Lemma lem4889590 {A : Type'} (c : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) c u) : @IN (A -> Prop) c u.
Proof. exact (h1). Qed.
Lemma lem4889591 {A : Type'} (P : type686 A) (c : A -> Prop) (u : type686 A) (h1 : term229 A u P) (h2 : @IN (A -> Prop) c u) : P c.
Proof. exact (@lem4889589 A c u P h1 (@lem4889590 A c u h2)). Qed.
Lemma lem4889592 {A : Type'} (P : type686 A) (c : A -> Prop) : (P c) = ((P c) = True).
Proof. exact (@lem7 (P c)). Qed.
Lemma lem4889593 {A : Type'} (P : type686 A) (c : A -> Prop) (u : type686 A) (h1 : term229 A u P) (h2 : @IN (A -> Prop) c u) : (P c) = True.
Proof. exact (EQ_MP (@lem4889592 A P c) (@lem4889591 A P c u h1 h2)). Qed.
Lemma lem4889599 {A : Type'} (u' : type686 A) : (@FINITE (A -> Prop) u') = ((@FINITE (A -> Prop) u') = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) u')). Qed.
Lemma lem4889601 {A : Type'} (c : A -> Prop) (u' : type686 A) (P : type686 A) (h1 : term229 A u' P) : term371 A u' P c.
Proof. exact (@lem4888879 A u' P h1 c). Qed.
Lemma lem4889602 {A : Type'} (u' : type686 A) (P : type686 A) (c : A -> Prop) : (term371 A u' P c) = (term372 A u' P c).
Proof. exact (eq_refl (term371 A u' P c)). Qed.
Lemma lem4889603 {A : Type'} (c : A -> Prop) (u' : type686 A) (P : type686 A) (h1 : term229 A u' P) : term372 A u' P c.
Proof. exact (EQ_MP (@lem4889602 A u' P c) (@lem4889601 A c u' P h1)). Qed.
Lemma lem4889604 {A : Type'} (c : A -> Prop) (u' : type686 A) (h1 : @IN (A -> Prop) c u') : @IN (A -> Prop) c u'.
Proof. exact (h1). Qed.
Lemma lem4889605 {A : Type'} (P : type686 A) (c : A -> Prop) (u' : type686 A) (h1 : term229 A u' P) (h2 : @IN (A -> Prop) c u') : P c.
Proof. exact (@lem4889603 A c u' P h1 (@lem4889604 A c u' h2)). Qed.
Lemma lem4889606 {A : Type'} (P : type686 A) (c : A -> Prop) : (P c) = ((P c) = True).
Proof. exact (@lem7 (P c)). Qed.
Lemma lem4889607 {A : Type'} (P : type686 A) (c : A -> Prop) (u' : type686 A) (h1 : term229 A u' P) (h2 : @IN (A -> Prop) c u') : (P c) = True.
Proof. exact (EQ_MP (@lem4889606 A P c) (@lem4889605 A P c u' h1 h2)). Qed.
Lemma lem4889613 {A : Type'} (x : A -> Prop) (u : type686 A) : (@IN (A -> Prop) x u) = ((@IN (A -> Prop) x u) = True).
Proof. exact (@lem7 (@IN (A -> Prop) x u)). Qed.
Lemma lem4889618 {A B : Type'} (f : A -> B) (s : A -> Prop) : term306 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4889558 A B f s h0). Qed.
Lemma lem4889619 {A : Type'} (f : type672 A) (s : type686 A) : term307 A f s.
Proof. exact (@lem4889618 (A -> Prop) (A -> Prop) f s). Qed.
Lemma lem4889620 {A : Type'} (x : A -> Prop) (u' : type686 A) : term373 A x u'.
Proof. exact (@lem4889619 A (term286 A x) u'). Qed.
Lemma lem4889622 {A : Type'} (u' : type686 A) (h1 : @FINITE (A -> Prop) u') : (@FINITE (A -> Prop) u') = True.
Proof. exact (EQ_MP (@lem4889599 A u') (@lem4888877 A u' h1)). Qed.
Lemma lem4889623 {A : Type'} (u' : type686 A) (h1 : @FINITE (A -> Prop) u') : True = (@FINITE (A -> Prop) u').
Proof. exact (SYM (@lem4889622 A u' h1)). Qed.
Lemma lem4889624 {A : Type'} (u' : type686 A) (h1 : @FINITE (A -> Prop) u') : @FINITE (A -> Prop) u'.
Proof. exact (EQ_MP (@lem4889623 A u' h1) (@lem0)). Qed.
Lemma lem4889625 {A : Type'} (x : A -> Prop) (u' : type686 A) (h1 : @FINITE (A -> Prop) u') : (term374 A x u') = True.
Proof. exact (@lem4889620 A x u' (@lem4889624 A u' h1)). Qed.
Lemma lem4889626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4889627 {A : Type'} (x : A -> Prop) (u' : type686 A) (h1 : @FINITE (A -> Prop) u') : (term375 A x u') = (and True).
Proof. exact (MK_COMB (@lem4889626) (@lem4889625 A x u' h1)). Qed.
Lemma lem4889629 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term262 _87967 _87968 f s P) = (term263 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4889547 _87967 _87968 s P f) (@lem4889546 _87967 _87968 P f s)). Qed.
Lemma lem4889630 {A : Type'} (s : type686 A) (P : type686 A) (f : type672 A) : (term330 A f s P) = (term331 A s P f).
Proof. exact (@lem4889629 (A -> Prop) (A -> Prop) s P f). Qed.
Lemma lem4889631 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) : (term376 A x u' P) = (term377 A u' P x).
Proof. exact (@lem4889630 A u' (term334 A P) (term286 A x)). Qed.
Lemma lem4889632 {A : Type'} (P : type686 A) (s : A -> Prop) : (term335 A P s) = (@UNION_OF A (@FINITE (A -> Prop)) P s).
Proof. exact (eq_refl (term335 A P s)). Qed.
Lemma lem4889633 {A : Type'} (s : A -> Prop) (x : A -> Prop) (u' : type686 A) : (term378 A s x u') = (term378 A s x u').
Proof. exact (eq_refl (term378 A s x u')). Qed.
Lemma lem4889634 {A : Type'} (x : A -> Prop) (u' : type686 A) (P : type686 A) (s : A -> Prop) : (term379 A x u' P s) = (term380 A x u' P s).
Proof. exact (MK_COMB (@lem4889633 A s x u') (@lem4889632 A P s)). Qed.
Lemma lem4889635 {A : Type'} (x : A -> Prop) (u' : type686 A) (P : type686 A) : (term381 A x u' P) = (term382 A x u' P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4889634 A x u' P s)). Qed.
Lemma lem4889636 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4889637 {A : Type'} (x : A -> Prop) (u' : type686 A) (P : type686 A) : (term376 A x u' P) = (term383 A x u' P).
Proof. exact (MK_COMB (@lem4889636 A) (@lem4889635 A x u' P)). Qed.
Lemma lem4889638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4889639 {A : Type'} (x : A -> Prop) (u' : type686 A) (P : type686 A) : (term384 A x u' P) = (term385 A x u' P).
Proof. exact (MK_COMB (@lem4889638) (@lem4889637 A x u' P)). Qed.
Lemma lem4889640 {A : Type'} (P : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term386 A P x x') = (term387 A P x x').
Proof. exact (eq_refl (term386 A P x x')). Qed.
Lemma lem4889641 {A : Type'} (x' : A -> Prop) (u' : type686 A) : (term343 A x' u') = (term343 A x' u').
Proof. exact (eq_refl (term343 A x' u')). Qed.
Lemma lem4889642 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term388 A u' P x x') = (term389 A u' P x x').
Proof. exact (MK_COMB (@lem4889641 A x' u') (@lem4889640 A P x x')). Qed.
Lemma lem4889643 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) : (term390 A u' P x) = (term391 A u' P x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4889642 A u' P x x')). Qed.
Lemma lem4889644 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4889645 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) : (term377 A u' P x) = (term392 A u' P x).
Proof. exact (MK_COMB (@lem4889644 A) (@lem4889643 A u' P x)). Qed.
Lemma lem4889646 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) : ((term376 A x u' P) = (term377 A u' P x)) = ((term383 A x u' P) = (term392 A u' P x)).
Proof. exact (MK_COMB (@lem4889639 A x u' P) (@lem4889645 A u' P x)). Qed.
Lemma lem4889647 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) : (term383 A x u' P) = (term392 A u' P x).
Proof. exact (EQ_MP (@lem4889646 A u' P x) (@lem4889631 A u' P x)). Qed.
Lemma lem4889655 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term310 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4889656 (p : Prop) (q : Prop) (p' : Prop) : term311 p q p'.
Proof. exact (fun q' : Prop => @lem4889655 p q p' q'). Qed.
Lemma lem4889657 (p : Prop) (q : Prop) : term312 p q.
Proof. exact (fun p' : Prop => @lem4889656 p q p'). Qed.
Lemma lem4889658 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) : term393 A u' P x x'.
Proof. exact (@lem4889657 (@IN (A -> Prop) x' u') (term387 A P x x')). Qed.
Lemma lem4889659 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (p' : Prop) : term394 A u' P x x' p'.
Proof. exact (@lem4889658 A u' P x x' p'). Qed.
Lemma lem4889660 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (p' : Prop) : (term394 A u' P x x' p') = (term395 A u' P x x' p').
Proof. exact (eq_refl (term394 A u' P x x' p')). Qed.
Lemma lem4889661 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (p' : Prop) : term395 A u' P x x' p'.
Proof. exact (EQ_MP (@lem4889660 A u' P x x' p') (@lem4889659 A u' P x x' p')). Qed.
Lemma lem4889662 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (p' : Prop) (q' : Prop) : term396 A u' P x x' p' q'.
Proof. exact (@lem4889661 A u' P x x' p' q'). Qed.
Lemma lem4889663 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (p' : Prop) (q' : Prop) : (term396 A u' P x x' p' q') = (term397 A u' P x x' p' q').
Proof. exact (eq_refl (term396 A u' P x x' p' q')). Qed.
Lemma lem4889664 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (p' : Prop) (q' : Prop) : term397 A u' P x x' p' q'.
Proof. exact (EQ_MP (@lem4889663 A u' P x x' p' q') (@lem4889662 A u' P x x' p' q')). Qed.
Lemma lem4889665 {A : Type'} (x' : A -> Prop) (u' : type686 A) : (@IN (A -> Prop) x' u') = (@IN (A -> Prop) x' u').
Proof. exact (eq_refl (@IN (A -> Prop) x' u')). Qed.
Lemma lem4889666 {A : Type'} (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (u' : type686 A) (q' : Prop) : term398 A P x x' u' q'.
Proof. exact (@lem4889664 A u' P x x' (@IN (A -> Prop) x' u') q'). Qed.
Lemma lem4889667 {A : Type'} (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (u' : type686 A) (q' : Prop) : term399 A P x x' u' q'.
Proof. exact (@lem4889666 A P x x' u' q' (@lem4889665 A x' u')). Qed.
Lemma lem4889668 {A : Type'} (x' : A -> Prop) (u' : type686 A) (h1 : @IN (A -> Prop) x' u') : @IN (A -> Prop) x' u'.
Proof. exact (h1). Qed.
Lemma lem4889669 {A : Type'} (x' : A -> Prop) (u' : type686 A) : (@IN (A -> Prop) x' u') = ((@IN (A -> Prop) x' u') = True).
Proof. exact (@lem7 (@IN (A -> Prop) x' u')). Qed.
Lemma lem4889672 {A B : Type'} (f : A -> B) (y : A) : (term207 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4889673 {A : Type'} (f : type672 A) (y : A -> Prop) : (term356 A f y) = (f y).
Proof. exact (@lem4889672 (A -> Prop) (A -> Prop) f y). Qed.
Lemma lem4889674 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term400 A x x') = (term287 A x x').
Proof. exact (@lem4889673 A (term286 A x) x'). Qed.
Lemma lem4889675 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term287 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term287 A x x')). Qed.
Lemma lem4889676 {A : Type'} (x : A -> Prop) : (term401 A x) = (term286 A x).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4889675 A x x')). Qed.
Lemma lem4889677 {A : Type'} (x' : A -> Prop) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4889678 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term400 A x x') = (term287 A x x').
Proof. exact (MK_COMB (@lem4889676 A x) (@lem4889677 A x')). Qed.
Lemma lem4889679 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4889680 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term402 A x x') = (term403 A x x').
Proof. exact (MK_COMB (@lem4889679 A) (@lem4889678 A x x')). Qed.
Lemma lem4889681 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term287 A x x') = (@INTER A x x').
Proof. exact (eq_refl (term287 A x x')). Qed.
Lemma lem4889682 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : ((term400 A x x') = (term287 A x x')) = ((term287 A x x') = (@INTER A x x')).
Proof. exact (MK_COMB (@lem4889680 A x x') (@lem4889681 A x x')). Qed.
Lemma lem4889683 {A : Type'} (x : A -> Prop) (x' : A -> Prop) : (term287 A x x') = (@INTER A x x').
Proof. exact (EQ_MP (@lem4889682 A x x') (@lem4889674 A x x')). Qed.
Lemma lem4889684 {A : Type'} (P : type686 A) : (@UNION_OF A (@FINITE (A -> Prop)) P) = (@UNION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (eq_refl (@UNION_OF A (@FINITE (A -> Prop)) P)). Qed.
Lemma lem4889685 {A : Type'} (P : type686 A) (x : A -> Prop) (x' : A -> Prop) : (term387 A P x x') = (term54 A P x x').
Proof. exact (MK_COMB (@lem4889684 A P) (@lem4889683 A x x')). Qed.
Lemma lem4889687 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term404 A P s t.
Proof. exact (fun h0 : term66 A s P t => @lem4889579 A s P t h1 h0). Qed.
Lemma lem4889688 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term404 A P s t.
Proof. exact (@lem4889687 A s t P h1). Qed.
Lemma lem4889689 {A : Type'} (x : A -> Prop) (x' : A -> Prop) (P : type686 A) (h1 : term45 A P) : term404 A P x x'.
Proof. exact (@lem4889688 A x x' P h1). Qed.
Lemma lem4889693 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term229 A u P) : term405 A u P c.
Proof. exact (fun h0 : @IN (A -> Prop) c u => @lem4889593 A P c u h1 h0). Qed.
Lemma lem4889694 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term229 A u P) : term405 A u P c.
Proof. exact (@lem4889693 A c u P h1). Qed.
Lemma lem4889695 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term229 A u P) : term405 A u P x.
Proof. exact (@lem4889694 A x u P h1). Qed.
Lemma lem4889697 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : (@IN (A -> Prop) x u) = True.
Proof. exact (EQ_MP (@lem4889613 A x u) (@lem4889538 A x u h1)). Qed.
Lemma lem4889698 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : True = (@IN (A -> Prop) x u).
Proof. exact (SYM (@lem4889697 A x u h1)). Qed.
Lemma lem4889699 {A : Type'} (x : A -> Prop) (u : type686 A) (h1 : @IN (A -> Prop) x u) : @IN (A -> Prop) x u.
Proof. exact (EQ_MP (@lem4889698 A x u h1) (@lem0)). Qed.
Lemma lem4889700 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term229 A u P) (h2 : @IN (A -> Prop) x u) : (P x) = True.
Proof. exact (@lem4889695 A x u P h1 (@lem4889699 A x u h2)). Qed.
Lemma lem4889701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4889702 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term229 A u P) (h2 : @IN (A -> Prop) x u) : (term140 A P x) = (and True).
Proof. exact (MK_COMB (@lem4889701) (@lem4889700 A P x u h1 h2)). Qed.
Lemma lem4889710 {A : Type'} (c : A -> Prop) (u' : type686 A) (P : type686 A) (h1 : term229 A u' P) : term405 A u' P c.
Proof. exact (fun h0 : @IN (A -> Prop) c u' => @lem4889607 A P c u' h1 h0). Qed.
Lemma lem4889711 {A : Type'} (c : A -> Prop) (u' : type686 A) (P : type686 A) (h1 : term229 A u' P) : term405 A u' P c.
Proof. exact (@lem4889710 A c u' P h1). Qed.
Lemma lem4889712 {A : Type'} (x' : A -> Prop) (u' : type686 A) (P : type686 A) (h1 : term229 A u' P) : term405 A u' P x'.
Proof. exact (@lem4889711 A x' u' P h1). Qed.
Lemma lem4889714 {A : Type'} (x' : A -> Prop) (u' : type686 A) (h1 : @IN (A -> Prop) x' u') : (@IN (A -> Prop) x' u') = True.
Proof. exact (EQ_MP (@lem4889669 A x' u') (@lem4889668 A x' u' h1)). Qed.
Lemma lem4889715 {A : Type'} (x' : A -> Prop) (u' : type686 A) (h1 : @IN (A -> Prop) x' u') : True = (@IN (A -> Prop) x' u').
Proof. exact (SYM (@lem4889714 A x' u' h1)). Qed.
Lemma lem4889716 {A : Type'} (x' : A -> Prop) (u' : type686 A) (h1 : @IN (A -> Prop) x' u') : @IN (A -> Prop) x' u'.
Proof. exact (EQ_MP (@lem4889715 A x' u' h1) (@lem0)). Qed.
Lemma lem4889717 {A : Type'} (P : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term229 A u' P) (h2 : @IN (A -> Prop) x' u') : (P x') = True.
Proof. exact (@lem4889712 A x' u' P h1 (@lem4889716 A x' u' h2)). Qed.
Lemma lem4889718 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term229 A u P) (h2 : term229 A u' P) (h3 : @IN (A -> Prop) x u) (h4 : @IN (A -> Prop) x' u') : (term66 A x P x') = (True /\ True).
Proof. exact (MK_COMB (@lem4889702 A P x u h1 h3) (@lem4889717 A P x' u' h2 h4)). Qed.
Lemma lem4889720 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4889721 : (True /\ True) = True.
Proof. exact (@lem4889720 True). Qed.
Lemma lem4889722 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term229 A u P) (h2 : term229 A u' P) (h3 : @IN (A -> Prop) x u) (h4 : @IN (A -> Prop) x' u') : (term66 A x P x') = True.
Proof. exact (TRANS (@lem4889718 A P x u x' u' h1 h2 h3 h4) (@lem4889721)). Qed.
Lemma lem4889723 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term229 A u P) (h2 : term229 A u' P) (h3 : @IN (A -> Prop) x u) (h4 : @IN (A -> Prop) x' u') : True = (term66 A x P x').
Proof. exact (SYM (@lem4889722 A P x u x' u' h1 h2 h3 h4)). Qed.
Lemma lem4889724 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term229 A u P) (h2 : term229 A u' P) (h3 : @IN (A -> Prop) x u) (h4 : @IN (A -> Prop) x' u') : term66 A x P x'.
Proof. exact (EQ_MP (@lem4889723 A P x u x' u' h1 h2 h3 h4) (@lem0)). Qed.
Lemma lem4889725 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) (h5 : @IN (A -> Prop) x' u') : (term54 A P x x') = True.
Proof. exact (@lem4889689 A x x' P h1 (@lem4889724 A P x u x' u' h2 h3 h4 h5)). Qed.
Lemma lem4889726 {A : Type'} (P : type686 A) (x : A -> Prop) (u : type686 A) (x' : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) (h5 : @IN (A -> Prop) x' u') : (term387 A P x x') = True.
Proof. exact (TRANS (@lem4889685 A P x x') (@lem4889725 A P x u x' u' h1 h2 h3 h4 h5)). Qed.
Lemma lem4889727 {A : Type'} (x' : A -> Prop) (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : term406 A u' P x x'.
Proof. exact (fun h0 : @IN (A -> Prop) x' u' => @lem4889726 A P x u x' u' h1 h2 h3 h4 h0). Qed.
Lemma lem4889728 {A : Type'} (P : type686 A) (x : A -> Prop) (x' : A -> Prop) (u' : type686 A) : term407 A P x x' u'.
Proof. exact (@lem4889667 A P x x' u' True). Qed.
Lemma lem4889729 {A : Type'} (x' : A -> Prop) (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (term389 A u' P x x') = (term408 A x' u').
Proof. exact (@lem4889728 A P x x' u' (@lem4889727 A x' u' P x u h1 h2 h3 h4)). Qed.
Lemma lem4889731 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4889732 {A : Type'} (x' : A -> Prop) (u' : type686 A) : (term408 A x' u') = True.
Proof. exact (@lem4889731 (@IN (A -> Prop) x' u')). Qed.
Lemma lem4889733 {A : Type'} (x' : A -> Prop) (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (term389 A u' P x x') = True.
Proof. exact (TRANS (@lem4889729 A x' u' P x u h1 h2 h3 h4) (@lem4889732 A x' u')). Qed.
Lemma lem4889734 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (term391 A u' P x) = (term409 A).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem4889733 A x' u' P x u h1 h2 h3 h4)). Qed.
Lemma lem4889735 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4889736 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (term392 A u' P x) = (term410 A).
Proof. exact (MK_COMB (@lem4889735 A) (@lem4889734 A u' P x u h1 h2 h3 h4)). Qed.
Lemma lem4889738 {A : Type'} (t : Prop) : (term411 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4889739 {A : Type'} (t : Prop) : (term412 A t) = t.
Proof. exact (@lem4889738 (A -> Prop) t). Qed.
Lemma lem4889740 {A : Type'} : (term410 A) = True.
Proof. exact (@lem4889739 A True). Qed.
Lemma lem4889741 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (term392 A u' P x) = True.
Proof. exact (TRANS (@lem4889736 A u' P x u h1 h2 h3 h4) (@lem4889740 A)). Qed.
Lemma lem4889742 {A : Type'} (u' : type686 A) (P : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @IN (A -> Prop) x u) : (term383 A x u' P) = True.
Proof. exact (TRANS (@lem4889647 A u' P x) (@lem4889741 A u' P x u h1 h2 h3 h4)). Qed.
Lemma lem4889743 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u') (h5 : @IN (A -> Prop) x u) : (term413 A x u' P) = (True /\ True).
Proof. exact (MK_COMB (@lem4889627 A x u' h4) (@lem4889742 A u' P x u h1 h2 h3 h5)). Qed.
Lemma lem4889745 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4889746 : (True /\ True) = True.
Proof. exact (@lem4889745 True). Qed.
Lemma lem4889747 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u') (h5 : @IN (A -> Prop) x u) : (term413 A x u' P) = True.
Proof. exact (TRANS (@lem4889743 A P u' x u h1 h2 h3 h4 h5) (@lem4889746)). Qed.
Lemma lem4889748 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u') (h5 : @IN (A -> Prop) x u) : True = (term413 A x u' P).
Proof. exact (SYM (@lem4889747 A P u' x u h1 h2 h3 h4 h5)). Qed.
Lemma lem4889749 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u') (h5 : @IN (A -> Prop) x u) : term413 A x u' P.
Proof. exact (EQ_MP (@lem4889748 A P u' x u h1 h2 h3 h4 h5) (@lem0)). Qed.
Lemma lem4889750 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u') (h5 : @IN (A -> Prop) x u) : term362 A P x u'.
Proof. exact (@lem4889542 A P x u' (@lem4889749 A P u' x u h1 h2 h3 h4 h5)). Qed.
Lemma lem4889751 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u') (h5 : @IN (A -> Prop) x u) : (@IN (A -> Prop) x u) = (term362 A P x u').
Proof. exact (prop_ext (fun h6 : @IN (A -> Prop) x u => @lem4889750 A P u' x u h1 h2 h3 h4 h5) (fun h6 : term362 A P x u' => @lem4889538 A x u h5)). Qed.
Lemma lem4889752 {A : Type'} (P : type686 A) (u' : type686 A) (x : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u') (h5 : @IN (A -> Prop) x u) : term362 A P x u'.
Proof. exact (EQ_MP (@lem4889751 A P u' x u h1 h2 h3 h4 h5) (@lem4889538 A x u h5)). Qed.
Lemma lem4889753 {A : Type'} (x : A -> Prop) (u : type686 A) (P : type686 A) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u') : term365 A u P x u'.
Proof. exact (fun h0 : @IN (A -> Prop) x u => @lem4889752 A P u' x u h1 h2 h3 h4 h0). Qed.
Lemma lem4889758 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u') : term367 A u P u'.
Proof. exact (fun x : A -> Prop => @lem4889753 A x u P u' h1 h2 h3 h4). Qed.
Lemma lem4889759 {A : Type'} (P : type686 A) (u : type686 A) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u) (h5 : @FINITE (A -> Prop) u') : term368 A u u' P.
Proof. exact (EQ_MP (@lem4889537 A u' P u h4) (@lem4889758 A u P u' h1 h2 h3 h5)). Qed.
Lemma lem4889760 {A : Type'} (P : type686 A) (u : type686 A) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u) (h5 : @FINITE (A -> Prop) u') : term257 A P u u'.
Proof. exact (@lem4888961 A P u u' (@lem4889759 A P u u' h1 h2 h3 h4 h5)). Qed.
Lemma lem4889761 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u) (h5 : @FINITE (A -> Prop) u') (h6 : s = (@UNIONS A u)) (h7 : t = (@UNIONS A u')) : term54 A P s t.
Proof. exact (EQ_MP (@lem4888957 A P s u t u' h6 h7) (@lem4889760 A P u u' h1 h2 h3 h4 h5)). Qed.
Lemma lem4889762 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term215 A s P t) : term226 A P t.
Proof. exact (proj2 (@lem4888867 A s P t h1)). Qed.
Lemma lem4889763 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term215 A s P t) : term226 A P s.
Proof. exact (proj1 (@lem4888867 A s P t h1)). Qed.
Lemma lem4889764 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term223 A P t u') : term220 A P t u'.
Proof. exact (proj2 (@lem4888875 A P t u' h1)). Qed.
Lemma lem4889765 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term223 A P t u') : @FINITE (A -> Prop) u'.
Proof. exact (proj1 (@lem4888875 A P t u' h1)). Qed.
Lemma lem4889766 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term220 A P t u') : t = (@UNIONS A u').
Proof. exact (proj2 (@lem4888876 A P t u' h1)). Qed.
Lemma lem4889767 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term220 A P t u') : term229 A u' P.
Proof. exact (proj1 (@lem4888876 A P t u' h1)). Qed.
Lemma lem4889768 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u) (h5 : @FINITE (A -> Prop) u') (h6 : s = (@UNIONS A u)) (h7 : t = (@UNIONS A u')) : (t = (@UNIONS A u')) = (term54 A P s t).
Proof. exact (prop_ext (fun h8 : t = (@UNIONS A u') => @lem4889761 A P s u t u' h1 h2 h3 h4 h5 h6 h7) (fun h8 : term54 A P s t => @lem4888878 A t u' h7)). Qed.
Lemma lem4889769 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u) (h5 : @FINITE (A -> Prop) u') (h6 : s = (@UNIONS A u)) (h7 : t = (@UNIONS A u')) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889768 A P s u t u' h1 h2 h3 h4 h5 h6 h7) (@lem4888878 A t u' h7)). Qed.
Lemma lem4889770 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u) (h5 : @FINITE (A -> Prop) u') (h6 : s = (@UNIONS A u)) (h7 : t = (@UNIONS A u')) : (term229 A u' P) = (term54 A P s t).
Proof. exact (prop_ext (fun h8 : term229 A u' P => @lem4889769 A P s u t u' h1 h2 h3 h4 h5 h6 h7) (fun h8 : term54 A P s t => @lem4888879 A u' P h3)). Qed.
Lemma lem4889771 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (t : A -> Prop) (u' : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u) (h5 : @FINITE (A -> Prop) u') (h6 : s = (@UNIONS A u)) (h7 : t = (@UNIONS A u')) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889770 A P s u t u' h1 h2 h3 h4 h5 h6 h7) (@lem4888879 A u' P h3)). Qed.
Lemma lem4889772 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u) (h5 : @FINITE (A -> Prop) u') (h6 : term220 A P t u') (h7 : s = (@UNIONS A u)) : (t = (@UNIONS A u')) = (term54 A P s t).
Proof. exact (prop_ext (fun h8 : t = (@UNIONS A u') => @lem4889771 A P s u t u' h1 h2 h3 h4 h5 h7 h8) (fun h8 : term54 A P s t => @lem4889766 A P t u' h6)). Qed.
Lemma lem4889773 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term229 A u' P) (h4 : @FINITE (A -> Prop) u) (h5 : @FINITE (A -> Prop) u') (h6 : term220 A P t u') (h7 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889772 A P t u' s u h1 h2 h3 h4 h5 h6 h7) (@lem4889766 A P t u' h6)). Qed.
Lemma lem4889774 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : @FINITE (A -> Prop) u) (h4 : @FINITE (A -> Prop) u') (h5 : term220 A P t u') (h6 : s = (@UNIONS A u)) : (term229 A u' P) = (term54 A P s t).
Proof. exact (prop_ext (fun h7 : term229 A u' P => @lem4889773 A P t u' s u h1 h2 h7 h3 h4 h5 h6) (fun h7 : term54 A P s t => @lem4889767 A P t u' h5)). Qed.
Lemma lem4889775 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : @FINITE (A -> Prop) u) (h4 : @FINITE (A -> Prop) u') (h5 : term220 A P t u') (h6 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889774 A P t u' s u h1 h2 h3 h4 h5 h6) (@lem4889767 A P t u' h5)). Qed.
Lemma lem4889776 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : @FINITE (A -> Prop) u) (h4 : @FINITE (A -> Prop) u') (h5 : term220 A P t u') (h6 : s = (@UNIONS A u)) : (@FINITE (A -> Prop) u') = (term54 A P s t).
Proof. exact (prop_ext (fun h7 : @FINITE (A -> Prop) u' => @lem4889775 A P t u' s u h1 h2 h3 h4 h5 h6) (fun h7 : term54 A P s t => @lem4888877 A u' h4)). Qed.
Lemma lem4889777 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : @FINITE (A -> Prop) u) (h4 : @FINITE (A -> Prop) u') (h5 : term220 A P t u') (h6 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889776 A P t u' s u h1 h2 h3 h4 h5 h6) (@lem4888877 A u' h4)). Qed.
Lemma lem4889778 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : @FINITE (A -> Prop) u) (h4 : @FINITE (A -> Prop) u') (h5 : term223 A P t u') (h6 : s = (@UNIONS A u)) : (term220 A P t u') = (term54 A P s t).
Proof. exact (prop_ext (fun h7 : term220 A P t u' => @lem4889777 A P t u' s u h1 h2 h3 h4 h7 h6) (fun h7 : term54 A P s t => @lem4889764 A P t u' h5)). Qed.
Lemma lem4889779 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : @FINITE (A -> Prop) u) (h4 : @FINITE (A -> Prop) u') (h5 : term223 A P t u') (h6 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889778 A P t u' s u h1 h2 h3 h4 h5 h6) (@lem4889764 A P t u' h5)). Qed.
Lemma lem4889780 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : @FINITE (A -> Prop) u) (h4 : term223 A P t u') (h5 : s = (@UNIONS A u)) : (@FINITE (A -> Prop) u') = (term54 A P s t).
Proof. exact (prop_ext (fun h6 : @FINITE (A -> Prop) u' => @lem4889779 A P t u' s u h1 h2 h3 h6 h4 h5) (fun h6 : term54 A P s t => @lem4889765 A P t u' h4)). Qed.
Lemma lem4889781 {A : Type'} (P : type686 A) (t : A -> Prop) (u' : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : @FINITE (A -> Prop) u) (h4 : term223 A P t u') (h5 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889780 A P t u' s u h1 h2 h3 h4 h5) (@lem4889765 A P t u' h4)). Qed.
Lemma lem4889782 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : @FINITE (A -> Prop) u) (h5 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (ex_elim (@lem4888868 A P t h3) (fun u' : type686 A => fun h0 : term225 A P t u' => @lem4889781 A P t u' s u h1 h2 h4 h0 h5)). Qed.
Lemma lem4889783 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term223 A P s u) : term220 A P s u.
Proof. exact (proj2 (@lem4888870 A P s u h1)). Qed.
Lemma lem4889784 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term223 A P s u) : @FINITE (A -> Prop) u.
Proof. exact (proj1 (@lem4888870 A P s u h1)). Qed.
Lemma lem4889785 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term220 A P s u) : s = (@UNIONS A u).
Proof. exact (proj2 (@lem4888871 A P s u h1)). Qed.
Lemma lem4889786 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term220 A P s u) : term229 A u P.
Proof. exact (proj1 (@lem4888871 A P s u h1)). Qed.
Lemma lem4889787 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : @FINITE (A -> Prop) u) (h5 : s = (@UNIONS A u)) : (s = (@UNIONS A u)) = (term54 A P s t).
Proof. exact (prop_ext (fun h6 : s = (@UNIONS A u) => @lem4889782 A P t s u h1 h2 h3 h4 h5) (fun h6 : term54 A P s t => @lem4888873 A s u h5)). Qed.
Lemma lem4889788 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : @FINITE (A -> Prop) u) (h5 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889787 A P t s u h1 h2 h3 h4 h5) (@lem4888873 A s u h5)). Qed.
Lemma lem4889789 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : @FINITE (A -> Prop) u) (h5 : s = (@UNIONS A u)) : (term229 A u P) = (term54 A P s t).
Proof. exact (prop_ext (fun h6 : term229 A u P => @lem4889788 A P t s u h1 h2 h3 h4 h5) (fun h6 : term54 A P s t => @lem4888874 A u P h2)). Qed.
Lemma lem4889790 {A : Type'} (P : type686 A) (t : A -> Prop) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : @FINITE (A -> Prop) u) (h5 : s = (@UNIONS A u)) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889789 A P t s u h1 h2 h3 h4 h5) (@lem4888874 A u P h2)). Qed.
Lemma lem4889791 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : @FINITE (A -> Prop) u) (h5 : term220 A P s u) : (s = (@UNIONS A u)) = (term54 A P s t).
Proof. exact (prop_ext (fun h6 : s = (@UNIONS A u) => @lem4889790 A P t s u h1 h2 h3 h4 h6) (fun h6 : term54 A P s t => @lem4889785 A P s u h5)). Qed.
Lemma lem4889792 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term229 A u P) (h3 : term226 A P t) (h4 : @FINITE (A -> Prop) u) (h5 : term220 A P s u) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889791 A t P s u h1 h2 h3 h4 h5) (@lem4889785 A P s u h5)). Qed.
Lemma lem4889793 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term226 A P t) (h3 : @FINITE (A -> Prop) u) (h4 : term220 A P s u) : (term229 A u P) = (term54 A P s t).
Proof. exact (prop_ext (fun h5 : term229 A u P => @lem4889792 A t P s u h1 h5 h2 h3 h4) (fun h5 : term54 A P s t => @lem4889786 A P s u h4)). Qed.
Lemma lem4889794 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term226 A P t) (h3 : @FINITE (A -> Prop) u) (h4 : term220 A P s u) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889793 A t P s u h1 h2 h3 h4) (@lem4889786 A P s u h4)). Qed.
Lemma lem4889795 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term226 A P t) (h3 : @FINITE (A -> Prop) u) (h4 : term220 A P s u) : (@FINITE (A -> Prop) u) = (term54 A P s t).
Proof. exact (prop_ext (fun h5 : @FINITE (A -> Prop) u => @lem4889794 A t P s u h1 h2 h3 h4) (fun h5 : term54 A P s t => @lem4888872 A u h3)). Qed.
Lemma lem4889796 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term226 A P t) (h3 : @FINITE (A -> Prop) u) (h4 : term220 A P s u) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889795 A t P s u h1 h2 h3 h4) (@lem4888872 A u h3)). Qed.
Lemma lem4889797 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term226 A P t) (h3 : @FINITE (A -> Prop) u) (h4 : term223 A P s u) : (term220 A P s u) = (term54 A P s t).
Proof. exact (prop_ext (fun h5 : term220 A P s u => @lem4889796 A t P s u h1 h2 h3 h5) (fun h5 : term54 A P s t => @lem4889783 A P s u h4)). Qed.
Lemma lem4889798 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term226 A P t) (h3 : @FINITE (A -> Prop) u) (h4 : term223 A P s u) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889797 A t P s u h1 h2 h3 h4) (@lem4889783 A P s u h4)). Qed.
Lemma lem4889799 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term226 A P t) (h3 : term223 A P s u) : (@FINITE (A -> Prop) u) = (term54 A P s t).
Proof. exact (prop_ext (fun h4 : @FINITE (A -> Prop) u => @lem4889798 A t P s u h1 h2 h4 h3) (fun h4 : term54 A P s t => @lem4889784 A P s u h3)). Qed.
Lemma lem4889800 {A : Type'} (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : term45 A P) (h2 : term226 A P t) (h3 : term223 A P s u) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889799 A t P s u h1 h2 h3) (@lem4889784 A P s u h3)). Qed.
Lemma lem4889801 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term226 A P s) (h3 : term226 A P t) : term54 A P s t.
Proof. exact (ex_elim (@lem4888869 A P s h2) (fun u : type686 A => fun h0 : term225 A P s u => @lem4889800 A t P s u h1 h3 h0)). Qed.
Lemma lem4889802 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term226 A P s) (h3 : term215 A s P t) : (term226 A P t) = (term54 A P s t).
Proof. exact (prop_ext (fun h4 : term226 A P t => @lem4889801 A s P t h1 h2 h4) (fun h4 : term54 A P s t => @lem4889762 A s P t h3)). Qed.
Lemma lem4889803 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term226 A P s) (h3 : term215 A s P t) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889802 A s P t h1 h2 h3) (@lem4889762 A s P t h3)). Qed.
Lemma lem4889804 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term215 A s P t) : (term226 A P s) = (term54 A P s t).
Proof. exact (prop_ext (fun h3 : term226 A P s => @lem4889803 A s P t h1 h3 h2) (fun h3 : term54 A P s t => @lem4889763 A s P t h2)). Qed.
Lemma lem4889805 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) (h1 : term45 A P) (h2 : term215 A s P t) : term54 A P s t.
Proof. exact (EQ_MP (@lem4889804 A s P t h1 h2) (@lem4889763 A s P t h2)). Qed.
Lemma lem4889806 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term217 A P s t.
Proof. exact (fun h0 : term215 A s P t => @lem4889805 A s P t h1 h0). Qed.
Lemma lem4889807 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term206 A P s t.
Proof. exact (EQ_MP (@lem4888821 A P s t) (@lem4889806 A s t P h1)). Qed.
Lemma lem4889808 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (h1 : term45 A P) : term46 A P s t.
Proof. exact (EQ_MP (@lem4888747 A P s t) (@lem4889807 A s t P h1)). Qed.
Lemma lem4889813 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term45 A P) : term48 A P s.
Proof. exact (fun t : A -> Prop => @lem4889808 A s t P h1). Qed.
Lemma lem4889818 {A : Type'} (P : type686 A) (h1 : term45 A P) : term50 A P.
Proof. exact (fun s : A -> Prop => @lem4889813 A s P h1). Qed.
Lemma lem4889819 {A : Type'} (P : type686 A) : term414 A P.
Proof. exact (fun h0 : term45 A P => @lem4889818 A P h0). Qed.
Lemma lem4889820 {A : Type'} (P : type686 A) : term415 A P.
Proof. exact (conj (@lem4888726 A P) (@lem4889819 A P)). Qed.
Lemma lem4889821 {A : Type'} (P : type686 A) : (term415 A P) = ((term50 A P) = (term45 A P)).
Proof. exact (@lem32 (term50 A P) (term45 A P)). Qed.
Lemma lem4889822 {A : Type'} (P : type686 A) : (term50 A P) = (term45 A P).
Proof. exact (EQ_MP (@lem4889821 A P) (@lem4889820 A P)). Qed.
Lemma lem4889827 {A : Type'} : term416 A.
Proof. exact (fun P : type686 A => @lem4889822 A P). Qed.
