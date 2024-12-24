Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1362040_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_ADD_RID_spec.
Require Import thm0_spec.
Require Import thm1338588_spec.
Require Import thm16474_spec.
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
Require Import thm69_spec.
Lemma lem1361605 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1361608 (h1 : term1) : term1.
Proof. exact (h1). Qed.
Lemma lem1361609 : term2.
Proof. exact (fun h0 : term1 => @lem1361608 h0). Qed.
Lemma lem1361610 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem1361611 (h1 : term1) : term1.
Proof. exact (h1). Qed.
Lemma lem1361612 (h1 : term1) (h2 : term2) : term1.
Proof. exact (@lem1361610 h2 (@lem1361611 h1)). Qed.
Lemma lem1361613 (h1 : term1) : term3.
Proof. exact (fun h0 : term2 => @lem1361612 h1 h0). Qed.
Lemma lem1361614 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem1361615 (h1 : term1) (h2 : term2) : term1.
Proof. exact (@lem1361613 h1 (@lem1361614 h2)). Qed.
Lemma lem1361616 (h1 : term2) : term2.
Proof. exact (fun h0 : term1 => @lem1361615 h0 h1). Qed.
Lemma lem1361617 : term4.
Proof. exact (fun h0 : term2 => @lem1361616 h0). Qed.
Lemma lem1361620 : term2.
Proof. exact (@lem1361617 (@lem1361609)). Qed.
Lemma lem1361630 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1361631 : term5 = term6.
Proof. exact (@lem1361630 term7). Qed.
Lemma lem1361636 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1361637 : term9 = term10.
Proof. exact (MK_COMB (@lem1361636) (@lem1361631)). Qed.
Lemma lem1361640 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1361647 : term1 = term12.
Proof. exact (MK_COMB (@lem1361640) (@lem1361637)). Qed.
Lemma lem1361648 (x : real) : ((term13 x) = term14) = ((term13 x) = term14).
Proof. exact (eq_refl ((term13 x) = term14)). Qed.
Lemma lem1361649 : term15 = term15.
Proof. exact (fun_ext (fun x : real => @lem1361648 x)). Qed.
Lemma lem1361650 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361651 : term7 = term7.
Proof. exact (MK_COMB (@lem1361650) (@lem1361649)). Qed.
Lemma lem1361652 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1361653 : term6 = term6.
Proof. exact (MK_COMB (@lem1361652) (@lem1361651)). Qed.
Lemma lem1361654 (x : real) : ((term16 x) = x) = ((term16 x) = x).
Proof. exact (eq_refl ((term16 x) = x)). Qed.
Lemma lem1361655 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1361654 x)). Qed.
Lemma lem1361656 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361657 : term18 = term18.
Proof. exact (MK_COMB (@lem1361656) (@lem1361655)). Qed.
Lemma lem1361658 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1361659 : term8 = term8.
Proof. exact (MK_COMB (@lem1361658) (@lem1361657)). Qed.
Lemma lem1361660 : term10 = term10.
Proof. exact (MK_COMB (@lem1361659) (@lem1361653)). Qed.
Lemma lem1361665 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1361666 : term12 = term12.
Proof. exact (MK_COMB (@lem1361665) (@lem1361660)). Qed.
Lemma lem1361685 : term1 = term12.
Proof. exact (TRANS (@lem1361647) (@lem1361666)). Qed.
Lemma lem1361686 : term12 = term1.
Proof. exact (SYM (@lem1361685)). Qed.
Lemma lem1361688 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem1361689 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1361695 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1361696 (x : real) : ((term16 x) = x) = ((term16 x) = x).
Proof. exact (eq_refl ((term16 x) = x)). Qed.
Lemma lem1361697 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1361696 x)). Qed.
Lemma lem1361698 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361707 : term18 = term18.
Proof. exact (MK_COMB (@lem1361698) (@lem1361697)). Qed.
Lemma lem1361708 (h1 : term18) : term18.
Proof. exact (EQ_MP (@lem1361707) (@lem1361688 h1)). Qed.
Lemma lem1361709 (x : real) : ((term13 x) = term14) = ((term13 x) = term14).
Proof. exact (eq_refl ((term13 x) = term14)). Qed.
Lemma lem1361710 : term15 = term15.
Proof. exact (fun_ext (fun x : real => @lem1361709 x)). Qed.
Lemma lem1361711 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361720 : term7 = term7.
Proof. exact (MK_COMB (@lem1361711) (@lem1361710)). Qed.
Lemma lem1361721 (h1 : term7) : term7.
Proof. exact (EQ_MP (@lem1361720) (@lem1361689 h1)). Qed.
Lemma lem1361739 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1361752 (x : real) : ((term16 x) = x) = ((term16 x) = x).
Proof. exact (eq_refl ((term16 x) = x)). Qed.
Lemma lem1361753 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1361752 x)). Qed.
Lemma lem1361754 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361755 : term18 = term18.
Proof. exact (MK_COMB (@lem1361754) (@lem1361753)). Qed.
Lemma lem1361756 (h1 : term18) : term18.
Proof. exact (EQ_MP (@lem1361755) (@lem1361708 h1)). Qed.
Lemma lem1361771 (x : real) : ((term13 x) = term14) = ((term13 x) = term14).
Proof. exact (eq_refl ((term13 x) = term14)). Qed.
Lemma lem1361772 : term15 = term15.
Proof. exact (fun_ext (fun x : real => @lem1361771 x)). Qed.
Lemma lem1361773 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361774 : term7 = term7.
Proof. exact (MK_COMB (@lem1361773) (@lem1361772)). Qed.
Lemma lem1361775 (h1 : term7) : term7.
Proof. exact (EQ_MP (@lem1361774) (@lem1361721 h1)). Qed.
Lemma lem1361779 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1361781 (x : real) : ((term16 x) = x) = ((term16 x) = x).
Proof. exact (eq_refl ((term16 x) = x)). Qed.
Lemma lem1361782 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1361781 x)). Qed.
Lemma lem1361783 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361785 : term18 = term18.
Proof. exact (MK_COMB (@lem1361783) (@lem1361782)). Qed.
Lemma lem1361786 (h1 : term18) : term18.
Proof. exact (EQ_MP (@lem1361785) (@lem1361756 h1)). Qed.
Lemma lem1361788 (x : real) : ((term13 x) = term14) = ((term13 x) = term14).
Proof. exact (eq_refl ((term13 x) = term14)). Qed.
Lemma lem1361789 : term15 = term15.
Proof. exact (fun_ext (fun x : real => @lem1361788 x)). Qed.
Lemma lem1361790 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361792 : term7 = term7.
Proof. exact (MK_COMB (@lem1361790) (@lem1361789)). Qed.
Lemma lem1361793 (h1 : term7) : term7.
Proof. exact (EQ_MP (@lem1361792) (@lem1361775 h1)). Qed.
Lemma lem1361794 (_24216 : real) (h1 : term18) : term19 _24216.
Proof. exact (@lem1361786 h1 _24216). Qed.
Lemma lem1361795 (_24216 : real) : (term19 _24216) = ((term16 _24216) = _24216).
Proof. exact (eq_refl (term19 _24216)). Qed.
Lemma lem1361797 (_24217 : real) (h1 : term7) : term20 _24217.
Proof. exact (@lem1361793 h1 _24217). Qed.
Lemma lem1361798 (_24217 : real) : (term20 _24217) = ((term13 _24217) = term14).
Proof. exact (eq_refl (term20 _24217)). Qed.
Lemma lem1361801 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1361846 (x : real) (y : real) (z : real) : term21 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1361850 (_24216 : real) (h1 : term18) : (term16 _24216) = _24216.
Proof. exact (EQ_MP (@lem1361795 _24216) (@lem1361794 _24216 h1)). Qed.
Lemma lem1361851 (h1 : term18) : term22 = term23.
Proof. exact (@lem1361850 term23 h1). Qed.
Lemma lem1361852 (h1 : term18) : term24.
Proof. exact (fun h0 : term25 => @lem1361851 h1). Qed.
Lemma lem1361854 (p : Prop) : (term26 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1361855 : term24 = (term22 = term23).
Proof. exact (@lem1361854 (term22 = term23)). Qed.
Lemma lem1361856 (h1 : term18) : term22 = term23.
Proof. exact (EQ_MP (@lem1361855) (@lem1361852 h1)). Qed.
Lemma lem1361858 (_24217 : real) (h1 : term7) : (term13 _24217) = term14.
Proof. exact (EQ_MP (@lem1361798 _24217) (@lem1361797 _24217 h1)). Qed.
Lemma lem1361859 (h1 : term7) : term22 = term14.
Proof. exact (@lem1361858 term14 h1). Qed.
Lemma lem1361860 (h1 : term7) : term27.
Proof. exact (fun h0 : term28 => @lem1361859 h1). Qed.
Lemma lem1361862 (p : Prop) : (term26 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1361863 : term27 = (term22 = term14).
Proof. exact (@lem1361862 (term22 = term14)). Qed.
Lemma lem1361864 (h1 : term7) : term22 = term14.
Proof. exact (EQ_MP (@lem1361863) (@lem1361860 h1)). Qed.
Lemma lem1361882 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1361883 (y : real) (x : real) (z : real) : (term29 x y z) = (term30 y x z).
Proof. exact (@lem1361882 (y = z) (term31 x z)). Qed.
Lemma lem1361893 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (eq_refl (term32 x y)). Qed.
Lemma lem1361894 (y : real) (x : real) (z : real) : (term21 x y z) = (term33 y x z).
Proof. exact (MK_COMB (@lem1361893 x y) (@lem1361883 y x z)). Qed.
Lemma lem1361898 (q : Prop) (p : Prop) (r : Prop) : (term34 p q r) = (term34 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1361899 (y : real) (x : real) (z : real) : (term33 y x z) = (term35 y x z).
Proof. exact (@lem1361898 (y = z) (term31 x y) (term31 x z)). Qed.
Lemma lem1361921 (y : real) (x : real) (z : real) : (term21 x y z) = (term35 y x z).
Proof. exact (TRANS (@lem1361894 y x z) (@lem1361899 y x z)). Qed.
Lemma lem1361922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1361923 (y : real) (x : real) (z : real) : (term36 x y z) = (term37 y x z).
Proof. exact (MK_COMB (@lem1361922) (@lem1361921 y x z)). Qed.
Lemma lem1361945 (y : real) (x : real) (z : real) : (term35 y x z) = (term35 y x z).
Proof. exact (eq_refl (term35 y x z)). Qed.
Lemma lem1361946 (y : real) (x : real) (z : real) : ((term21 x y z) = (term35 y x z)) = ((term35 y x z) = (term35 y x z)).
Proof. exact (MK_COMB (@lem1361923 y x z) (@lem1361945 y x z)). Qed.
Lemma lem1361948 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1361949 (x : Prop) : (x = x) = True.
Proof. exact (@lem1361948 Prop x). Qed.
Lemma lem1361950 (y : real) (x : real) (z : real) : ((term35 y x z) = (term35 y x z)) = True.
Proof. exact (@lem1361949 (term35 y x z)). Qed.
Lemma lem1361951 (y : real) (x : real) (z : real) : ((term21 x y z) = (term35 y x z)) = True.
Proof. exact (TRANS (@lem1361946 y x z) (@lem1361950 y x z)). Qed.
Lemma lem1361952 (y : real) (x : real) (z : real) : True = ((term21 x y z) = (term35 y x z)).
Proof. exact (SYM (@lem1361951 y x z)). Qed.
Lemma lem1361953 (y : real) (x : real) (z : real) : (term21 x y z) = (term35 y x z).
Proof. exact (EQ_MP (@lem1361952 y x z) (@lem0)). Qed.
Lemma lem1361954 (y : real) (x : real) (z : real) : term35 y x z.
Proof. exact (EQ_MP (@lem1361953 y x z) (@lem1361846 x y z)). Qed.
Lemma lem1361956 (b : Prop) (a : Prop) : (a \/ b) = (term38 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1361957 (x : real) (y : real) (z : real) : (term35 y x z) = (term39 x y z).
Proof. exact (@lem1361956 (term40 y x z) (y = z)). Qed.
Lemma lem1361959 (a : Prop) (b : Prop) : (term41 a b) = (term42 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1361960 (y : real) (x : real) (z : real) : (term43 y x z) = (term44 y x z).
Proof. exact (@lem1361959 (term31 x y) (term31 x z)). Qed.
Lemma lem1361962 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1361963 (x : real) (y : real) : (term46 x y) = (x = y).
Proof. exact (@lem1361962 (x = y)). Qed.
Lemma lem1361964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1361965 (x : real) (y : real) : (term47 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1361964) (@lem1361963 x y)). Qed.
Lemma lem1361967 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1361968 (x : real) (z : real) : (term46 x z) = (x = z).
Proof. exact (@lem1361967 (x = z)). Qed.
Lemma lem1361969 (y : real) (x : real) (z : real) : (term44 y x z) = (term49 y x z).
Proof. exact (MK_COMB (@lem1361965 x y) (@lem1361968 x z)). Qed.
Lemma lem1361970 (y : real) (x : real) (z : real) : (term43 y x z) = (term49 y x z).
Proof. exact (TRANS (@lem1361960 y x z) (@lem1361969 y x z)). Qed.
Lemma lem1361971 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1361972 (y : real) (x : real) (z : real) : (term50 y x z) = (term51 y x z).
Proof. exact (MK_COMB (@lem1361971) (@lem1361970 y x z)). Qed.
Lemma lem1361973 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1361974 (x : real) (y : real) (z : real) : (term39 x y z) = (term52 x y z).
Proof. exact (MK_COMB (@lem1361972 y x z) (@lem1361973 y z)). Qed.
Lemma lem1361975 (x : real) (y : real) (z : real) : (term35 y x z) = (term52 x y z).
Proof. exact (TRANS (@lem1361957 x y z) (@lem1361974 x y z)). Qed.
Lemma lem1361977 (h1 : term18) (h2 : term7) : term53.
Proof. exact (conj (@lem1361856 h1) (@lem1361864 h2)). Qed.
Lemma lem1361979 (x : real) (y : real) (z : real) : term52 x y z.
Proof. exact (EQ_MP (@lem1361975 x y z) (@lem1361954 y x z)). Qed.
Lemma lem1361980 : term54.
Proof. exact (@lem1361979 term22 term23 term14). Qed.
Lemma lem1361983 (h1 : term18) (h2 : term7) : term23 = term14.
Proof. exact (@lem1361980 (@lem1361977 h1 h2)). Qed.
Lemma lem1361984 (h1 : term18) (h2 : term7) : term55.
Proof. exact (fun h0 : term0 => @lem1361983 h1 h2). Qed.
Lemma lem1361986 (p : Prop) : (term26 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1361987 : term55 = (term23 = term14).
Proof. exact (@lem1361986 (term23 = term14)). Qed.
Lemma lem1361988 (h1 : term18) (h2 : term7) : term23 = term14.
Proof. exact (EQ_MP (@lem1361987) (@lem1361984 h1 h2)). Qed.
Lemma lem1361991 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1361993 : term0 = term56.
Proof. exact (@lem1361991 (term23 = term14)). Qed.
Lemma lem1361996 (h1 : term0) : term56.
Proof. exact (EQ_MP (@lem1361993) (@lem1361801 h1)). Qed.
Lemma lem1361999 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (@lem1361996 h3 (@lem1361988 h1 h2)). Qed.
Lemma lem1362000 (h1 : term18) (h2 : term7) (h3 : term0) : term57.
Proof. exact (fun h0 : ~ False => @lem1361999 h1 h2 h3). Qed.
Lemma lem1362002 (p : Prop) : (term26 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1362003 : term57 = False.
Proof. exact (@lem1362002 False). Qed.
Lemma lem1362004 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (EQ_MP (@lem1362003) (@lem1362000 h1 h2 h3)). Qed.
Lemma lem1362005 (h1 : term18) (h2 : term7) (h3 : term0) : term0 = False.
Proof. exact (prop_ext (fun h4 : term0 => @lem1362004 h1 h2 h3) (fun h4 : False => @lem1361801 h3)). Qed.
Lemma lem1362006 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (EQ_MP (@lem1362005 h1 h2 h3) (@lem1361801 h3)). Qed.
Lemma lem1362007 (h1 : term18) (h2 : term7) (h3 : term0) : term0 = False.
Proof. exact (prop_ext (fun h4 : term0 => @lem1362006 h1 h2 h3) (fun h4 : False => @lem1361779 h3)). Qed.
Lemma lem1362008 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (EQ_MP (@lem1362007 h1 h2 h3) (@lem1361779 h3)). Qed.
Lemma lem1362009 (h1 : term18) (h2 : term7) (h3 : term0) : term7 = False.
Proof. exact (prop_ext (fun h4 : term7 => @lem1362008 h1 h2 h3) (fun h4 : False => @lem1361793 h2)). Qed.
Lemma lem1362010 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (EQ_MP (@lem1362009 h1 h2 h3) (@lem1361793 h2)). Qed.
Lemma lem1362011 (h1 : term18) (h2 : term7) (h3 : term0) : term18 = False.
Proof. exact (prop_ext (fun h4 : term18 => @lem1362010 h1 h2 h3) (fun h4 : False => @lem1361786 h1)). Qed.
Lemma lem1362012 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (EQ_MP (@lem1362011 h1 h2 h3) (@lem1361786 h1)). Qed.
Lemma lem1362013 (h1 : term18) (h2 : term7) (h3 : term0) : term0 = False.
Proof. exact (prop_ext (fun h4 : term0 => @lem1362012 h1 h2 h3) (fun h4 : False => @lem1361779 h3)). Qed.
Lemma lem1362014 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (EQ_MP (@lem1362013 h1 h2 h3) (@lem1361779 h3)). Qed.
Lemma lem1362015 (h1 : term18) (h2 : term7) (h3 : term0) : term7 = False.
Proof. exact (prop_ext (fun h4 : term7 => @lem1362014 h1 h2 h3) (fun h4 : False => @lem1361775 h2)). Qed.
Lemma lem1362016 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (EQ_MP (@lem1362015 h1 h2 h3) (@lem1361775 h2)). Qed.
Lemma lem1362017 (h1 : term18) (h2 : term7) (h3 : term0) : term18 = False.
Proof. exact (prop_ext (fun h4 : term18 => @lem1362016 h1 h2 h3) (fun h4 : False => @lem1361756 h1)). Qed.
Lemma lem1362018 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (EQ_MP (@lem1362017 h1 h2 h3) (@lem1361756 h1)). Qed.
Lemma lem1362019 (h1 : term18) (h2 : term7) (h3 : term0) : term0 = False.
Proof. exact (prop_ext (fun h4 : term0 => @lem1362018 h1 h2 h3) (fun h4 : False => @lem1361739 h3)). Qed.
Lemma lem1362020 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (EQ_MP (@lem1362019 h1 h2 h3) (@lem1361739 h3)). Qed.
Lemma lem1362021 (h1 : term18) (h2 : term7) (h3 : term0) : term7 = False.
Proof. exact (prop_ext (fun h4 : term7 => @lem1362020 h1 h2 h3) (fun h4 : False => @lem1361721 h2)). Qed.
Lemma lem1362022 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (EQ_MP (@lem1362021 h1 h2 h3) (@lem1361721 h2)). Qed.
Lemma lem1362023 (h1 : term18) (h2 : term7) (h3 : term0) : term18 = False.
Proof. exact (prop_ext (fun h4 : term18 => @lem1362022 h1 h2 h3) (fun h4 : False => @lem1361708 h1)). Qed.
Lemma lem1362024 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (EQ_MP (@lem1362023 h1 h2 h3) (@lem1361708 h1)). Qed.
Lemma lem1362025 (h1 : term18) (h2 : term7) (h3 : term0) : term0 = False.
Proof. exact (prop_ext (fun h4 : term0 => @lem1362024 h1 h2 h3) (fun h4 : False => @lem1361695 h3)). Qed.
Lemma lem1362026 (h1 : term18) (h2 : term7) (h3 : term0) : False.
Proof. exact (EQ_MP (@lem1362025 h1 h2 h3) (@lem1361695 h3)). Qed.
Lemma lem1362027 (h1 : term18) (h2 : term0) : term5.
Proof. exact (fun h0 : term7 => @lem1362026 h1 h0 h2). Qed.
Lemma lem1362028 : term5 = term6.
Proof. exact (@lem69 term7). Qed.
Lemma lem1362029 (h1 : term18) (h2 : term0) : term6.
Proof. exact (EQ_MP (@lem1362028) (@lem1362027 h1 h2)). Qed.
Lemma lem1362030 (h1 : term0) : term10.
Proof. exact (fun h0 : term18 => @lem1362029 h0 h1). Qed.
Lemma lem1362031 : term12.
Proof. exact (fun h0 : term0 => @lem1362030 h0). Qed.
Lemma lem1362032 : term1.
Proof. exact (EQ_MP (@lem1361686) (@lem1362031)). Qed.
Lemma lem1362034 : term1.
Proof. exact (@lem1361620 (@lem1362032)). Qed.
Lemma lem1362035 (h1 : term0) : term9.
Proof. exact (@lem1362034 (@lem1361605 h1)). Qed.
Lemma lem1362036 (h1 : term0) : term5.
Proof. exact (@lem1362035 h1 (@lem1361590)). Qed.
Lemma lem1362037 (h1 : term0) : False.
Proof. exact (@lem1362036 h1 (@lem1338588)). Qed.
Lemma lem1362038 (h1 : term0) : term0 = False.
Proof. exact (prop_ext (fun h2 : term0 => @lem1362037 h1) (fun h2 : False => @lem1361605 h1)). Qed.
Lemma lem1362039 (h1 : term0) : False.
Proof. exact (EQ_MP (@lem1362038 h1) (@lem1361605 h1)). Qed.
Lemma lem1362040 : term58.
Proof. exact (fun h0 : term0 => @lem1362039 h0). Qed.
