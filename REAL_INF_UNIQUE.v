Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INF_UNIQUE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_NOT_LE_spec.
Require Import SELECT_UNIQUE_spec.
Require Import inf_spec.
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
Lemma lem5231644 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5231645 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5231646 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5231645 t1) (@lem5231644 t1)). Qed.
Lemma lem5231647 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5231646 t1 t2). Qed.
Lemma lem5231648 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5231649 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5231648 t1 t2) (@lem5231647 t1 t2)). Qed.
Lemma lem5231650 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5231649 t1 t2 t3). Qed.
Lemma lem5231651 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5231652 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5231651 t1 t2 t3) (@lem5231650 t1 t2 t3)). Qed.
Lemma lem5231653 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5231652 t1 t2 t3)). Qed.
Lemma lem5231654 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem5231655 {A : Type'} (P : A -> Prop) (h1 : term7 A) : term8 A P.
Proof. exact (@lem5231654 A h1 P). Qed.
Lemma lem5231656 {A : Type'} (P : A -> Prop) : (term8 A P) = (term9 A P).
Proof. exact (eq_refl (term8 A P)). Qed.
Lemma lem5231657 {A : Type'} (P : A -> Prop) (h1 : term7 A) : term9 A P.
Proof. exact (EQ_MP (@lem5231656 A P) (@lem5231655 A P h1)). Qed.
Lemma lem5231658 {A : Type'} (P : A -> Prop) (x : A) (h1 : term7 A) : term10 A P x.
Proof. exact (@lem5231657 A P h1 x). Qed.
Lemma lem5231659 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem5231660 {A : Type'} (P : A -> Prop) (x : A) (h1 : term7 A) : term11 A P x.
Proof. exact (EQ_MP (@lem5231659 A P x) (@lem5231658 A P x h1)). Qed.
Lemma lem5231661 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) : term12 A P x.
Proof. exact (h1). Qed.
Lemma lem5231662 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) (h2 : term7 A) : (@ε A P) = x.
Proof. exact (@lem5231660 A P x h2 (@lem5231661 A P x h1)). Qed.
Lemma lem5231663 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) : term13 A P x.
Proof. exact (fun h0 : term7 A => @lem5231662 A P x h1 h0). Qed.
Lemma lem5231664 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem5231665 {A : Type'} (P : A -> Prop) (x : A) (h1 : term12 A P x) (h2 : term7 A) : (@ε A P) = x.
Proof. exact (@lem5231663 A P x h1 (@lem5231664 A h2)). Qed.
Lemma lem5231666 {A : Type'} (P : A -> Prop) (x : A) (h1 : term7 A) : term11 A P x.
Proof. exact (fun h0 : term12 A P x => @lem5231665 A P x h0 h1). Qed.
Lemma lem5231667 {A : Type'} (P : A -> Prop) (h1 : term7 A) : term9 A P.
Proof. exact (fun x : A => @lem5231666 A P x h1). Qed.
Lemma lem5231668 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (fun P : A -> Prop => @lem5231667 A P h1). Qed.
Lemma lem5231669 {A : Type'} : term14 A.
Proof. exact (fun h0 : term7 A => @lem5231668 A h0). Qed.
Lemma lem5231670 {A : Type'} : term7 A.
Proof. exact (@lem5231669 A (@lem9522 A)). Qed.
Lemma lem5231671 {A : Type'} (P : A -> Prop) : term8 A P.
Proof. exact (@lem5231670 A P). Qed.
Lemma lem5231672 {A : Type'} (P : A -> Prop) : (term8 A P) = (term9 A P).
Proof. exact (eq_refl (term8 A P)). Qed.
Lemma lem5231673 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (EQ_MP (@lem5231672 A P) (@lem5231671 A P)). Qed.
Lemma lem5231674 {A : Type'} (P : A -> Prop) (x : A) : term10 A P x.
Proof. exact (@lem5231673 A P x). Qed.
Lemma lem5231675 {A : Type'} (P : A -> Prop) (x : A) : (term10 A P x) = (term11 A P x).
Proof. exact (eq_refl (term10 A P x)). Qed.
Lemma lem5231677 (s : real -> Prop) : term15 s.
Proof. exact (@lem5204233 s). Qed.
Lemma lem5231678 (s : real -> Prop) : (term15 s) = ((inf s) = (term16 s)).
Proof. exact (eq_refl (term15 s)). Qed.
Lemma lem5231680 (b : real) (s : real -> Prop) (h1 : term17 b s) : term17 b s.
Proof. exact (h1). Qed.
Lemma lem5231681 (b : real) (s : real -> Prop) (h1 : term18 b s) : term18 b s.
Proof. exact (h1). Qed.
Lemma lem5231682 (s : real -> Prop) (b : real) (h1 : term19 s b) : term19 s b.
Proof. exact (h1). Qed.
Lemma lem5231686 (s : real -> Prop) : (inf s) = (term16 s).
Proof. exact (EQ_MP (@lem5231678 s) (@lem5231677 s)). Qed.
Lemma lem5231707 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5231708 (s : real -> Prop) : (term20 s) = (term21 s).
Proof. exact (MK_COMB (@lem5231707) (@lem5231686 s)). Qed.
Lemma lem5231709 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5231710 (s : real -> Prop) (b : real) : ((inf s) = b) = ((term16 s) = b).
Proof. exact (MK_COMB (@lem5231708 s) (@lem5231709 b)). Qed.
Lemma lem5231713 (s : real -> Prop) (b : real) : ((term16 s) = b) = ((inf s) = b).
Proof. exact (SYM (@lem5231710 s b)). Qed.
Lemma lem5231715 {A : Type'} (P : A -> Prop) (x : A) : term11 A P x.
Proof. exact (EQ_MP (@lem5231675 A P x) (@lem5231674 A P x)). Qed.
Lemma lem5231716 (P : real -> Prop) (x : real) : term22 P x.
Proof. exact (@lem5231715 real P x). Qed.
Lemma lem5231717 (s : real -> Prop) (b : real) : term23 s b.
Proof. exact (@lem5231716 (term24 s) b). Qed.
Lemma lem5231719 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5231720 (s : real -> Prop) (b : real) : (term26 s b) = (term27 s b).
Proof. exact (@lem5231719 (term26 s b)). Qed.
Lemma lem5231721 (s : real -> Prop) (b : real) : (term27 s b) = (term26 s b).
Proof. exact (SYM (@lem5231720 s b)). Qed.
Lemma lem5231722 (s : real -> Prop) (b : real) (h1 : term28 s b) : term28 s b.
Proof. exact (h1). Qed.
Lemma lem5231725 (s : real -> Prop) (b : real) (h1 : term29 s b) : term29 s b.
Proof. exact (h1). Qed.
Lemma lem5231726 (s : real -> Prop) (b : real) : term30 s b.
Proof. exact (fun h0 : term29 s b => @lem5231725 s b h0). Qed.
Lemma lem5231727 (s : real -> Prop) (b : real) (h1 : term30 s b) : term30 s b.
Proof. exact (h1). Qed.
Lemma lem5231728 (s : real -> Prop) (b : real) (h1 : term29 s b) : term29 s b.
Proof. exact (h1). Qed.
Lemma lem5231729 (s : real -> Prop) (b : real) (h1 : term29 s b) (h2 : term30 s b) : term29 s b.
Proof. exact (@lem5231727 s b h2 (@lem5231728 s b h1)). Qed.
Lemma lem5231730 (s : real -> Prop) (b : real) (h1 : term29 s b) : term31 s b.
Proof. exact (fun h0 : term30 s b => @lem5231729 s b h1 h0). Qed.
Lemma lem5231731 (s : real -> Prop) (b : real) (h1 : term30 s b) : term30 s b.
Proof. exact (h1). Qed.
Lemma lem5231732 (s : real -> Prop) (b : real) (h1 : term29 s b) (h2 : term30 s b) : term29 s b.
Proof. exact (@lem5231730 s b h1 (@lem5231731 s b h2)). Qed.
Lemma lem5231733 (s : real -> Prop) (b : real) (h1 : term30 s b) : term30 s b.
Proof. exact (fun h0 : term29 s b => @lem5231732 s b h0 h1). Qed.
Lemma lem5231734 (s : real -> Prop) (b : real) : term32 s b.
Proof. exact (fun h0 : term30 s b => @lem5231733 s b h0). Qed.
Lemma lem5231737 (s : real -> Prop) (b : real) : term30 s b.
Proof. exact (@lem5231734 s b (@lem5231726 s b)). Qed.
Lemma lem5231851 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5231852 : term33 = term34.
Proof. exact (@lem5231851 term35). Qed.
Lemma lem5231861 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem5231862 : term37 = term38.
Proof. exact (MK_COMB (@lem5231861) (@lem5231852)). Qed.
Lemma lem5231865 (s : real -> Prop) (b : real) : (term39 s b) = (term39 s b).
Proof. exact (eq_refl (term39 s b)). Qed.
Lemma lem5231866 (s : real -> Prop) (b : real) : (term40 s b) = (term41 s b).
Proof. exact (MK_COMB (@lem5231865 s b) (@lem5231862)). Qed.
Lemma lem5231869 (b : real) (s : real -> Prop) : (term42 b s) = (term42 b s).
Proof. exact (eq_refl (term42 b s)). Qed.
Lemma lem5231870 (s : real -> Prop) (b : real) : (term43 s b) = (term44 s b).
Proof. exact (MK_COMB (@lem5231869 b s) (@lem5231866 s b)). Qed.
Lemma lem5231873 (s : real -> Prop) (b : real) : (term45 s b) = (term45 s b).
Proof. exact (eq_refl (term45 s b)). Qed.
Lemma lem5231874 (s : real -> Prop) (b : real) : (term29 s b) = (term46 s b).
Proof. exact (MK_COMB (@lem5231873 s b) (@lem5231870 s b)). Qed.
Lemma lem5231877 (b : real) : (term47 b) = (term48 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5231874 s b)). Qed.
Lemma lem5231878 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5231879 (b : real) : (term49 b) = (term50 b).
Proof. exact (MK_COMB (@lem5231878) (@lem5231877 b)). Qed.
Lemma lem5231884 : term51 = term52.
Proof. exact (fun_ext (fun b : real => @lem5231879 b)). Qed.
Lemma lem5231885 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5231886 : term53 = term54.
Proof. exact (MK_COMB (@lem5231885) (@lem5231884)). Qed.
Lemma lem5231891 (s : real -> Prop) (y : real) : (term55 s y) = (term56 s y).
Proof. exact (eq_refl (term55 s y)). Qed.
Lemma lem5231892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5231893 (s : real -> Prop) (y : real) : (term57 s y) = (term58 s y).
Proof. exact (MK_COMB (@lem5231892) (@lem5231891 s y)). Qed.
Lemma lem5231894 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5231895 (s : real -> Prop) (y : real) (b : real) : ((term55 s y) = (y = b)) = ((term56 s y) = (y = b)).
Proof. exact (MK_COMB (@lem5231893 s y) (@lem5231894 y b)). Qed.
Lemma lem5231896 (s : real -> Prop) (b : real) : (term59 s b) = (term60 s b).
Proof. exact (fun_ext (fun y : real => @lem5231895 s y b)). Qed.
Lemma lem5231897 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5231898 (s : real -> Prop) (b : real) : (term26 s b) = (term61 s b).
Proof. exact (MK_COMB (@lem5231897) (@lem5231896 s b)). Qed.
Lemma lem5231899 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5231900 (s : real -> Prop) (b : real) : (term28 s b) = (term62 s b).
Proof. exact (MK_COMB (@lem5231899) (@lem5231898 s b)). Qed.
Lemma lem5231901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5231902 (s : real -> Prop) (b : real) : (term39 s b) = (term63 s b).
Proof. exact (MK_COMB (@lem5231901) (@lem5231900 s b)). Qed.
Lemma lem5231903 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem5231904 (s : real -> Prop) (b : real) : (term41 s b) = (term64 s b).
Proof. exact (MK_COMB (@lem5231902 s b) (@lem5231903)). Qed.
Lemma lem5231905 (b : real) (s : real -> Prop) : (term42 b s) = (term42 b s).
Proof. exact (eq_refl (term42 b s)). Qed.
Lemma lem5231906 (s : real -> Prop) (b : real) : (term44 s b) = (term65 s b).
Proof. exact (MK_COMB (@lem5231905 b s) (@lem5231904 s b)). Qed.
Lemma lem5231907 (s : real -> Prop) (b : real) : (term45 s b) = (term45 s b).
Proof. exact (eq_refl (term45 s b)). Qed.
Lemma lem5231908 (s : real -> Prop) (b : real) : (term46 s b) = (term66 s b).
Proof. exact (MK_COMB (@lem5231907 s b) (@lem5231906 s b)). Qed.
Lemma lem5231909 (b : real) : (term48 b) = (term67 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5231908 s b)). Qed.
Lemma lem5231910 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5231911 (b : real) : (term50 b) = (term68 b).
Proof. exact (MK_COMB (@lem5231910) (@lem5231909 b)). Qed.
Lemma lem5231912 : term52 = term69.
Proof. exact (fun_ext (fun b : real => @lem5231911 b)). Qed.
Lemma lem5231913 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5231914 : term54 = term70.
Proof. exact (MK_COMB (@lem5231913) (@lem5231912)). Qed.
Lemma lem5231917 : term53 = term70.
Proof. exact (TRANS (@lem5231886) (@lem5231914)). Qed.
Lemma lem5231924 (y : real) (x : real) : ((term71 x y) = (real_lt y x)) = ((term71 x y) = (real_lt y x)).
Proof. exact (eq_refl ((term71 x y) = (real_lt y x))). Qed.
Lemma lem5231925 (x : real) : (term72 x) = (term72 x).
Proof. exact (fun_ext (fun y : real => @lem5231924 y x)). Qed.
Lemma lem5231926 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5231927 (x : real) : (term73 x) = (term73 x).
Proof. exact (MK_COMB (@lem5231926) (@lem5231925 x)). Qed.
Lemma lem5231928 : term74 = term74.
Proof. exact (fun_ext (fun x : real => @lem5231927 x)). Qed.
Lemma lem5231929 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5231930 : term35 = term35.
Proof. exact (MK_COMB (@lem5231929) (@lem5231928)). Qed.
Lemma lem5231931 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5231932 : term34 = term34.
Proof. exact (MK_COMB (@lem5231931) (@lem5231930)). Qed.
Lemma lem5231941 (x : real) (y : real) : ((term75 y x) = (x = y)) = ((term75 y x) = (x = y)).
Proof. exact (eq_refl ((term75 y x) = (x = y))). Qed.
Lemma lem5231942 (x : real) : (term76 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem5231941 x y)). Qed.
Lemma lem5231943 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5231944 (x : real) : (term77 x) = (term77 x).
Proof. exact (MK_COMB (@lem5231943) (@lem5231942 x)). Qed.
Lemma lem5231945 : term78 = term78.
Proof. exact (fun_ext (fun x : real => @lem5231944 x)). Qed.
Lemma lem5231946 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5231947 : term79 = term79.
Proof. exact (MK_COMB (@lem5231946) (@lem5231945)). Qed.
Lemma lem5231948 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5231949 : term36 = term36.
Proof. exact (MK_COMB (@lem5231948) (@lem5231947)). Qed.
Lemma lem5231950 : term38 = term38.
Proof. exact (MK_COMB (@lem5231949) (@lem5231932)). Qed.
Lemma lem5231951 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5231952 (b : real) (y : real) : (real_le b y) = (real_le b y).
Proof. exact (eq_refl (real_le b y)). Qed.
Lemma lem5231957 (s : real -> Prop) (b : real) (x : real) : (term80 s b x) = (term80 s b x).
Proof. exact (eq_refl (term80 s b x)). Qed.
Lemma lem5231958 (s : real -> Prop) (b : real) : (term81 s b) = (term81 s b).
Proof. exact (fun_ext (fun x : real => @lem5231957 s b x)). Qed.
Lemma lem5231959 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5231960 (s : real -> Prop) (b : real) : (term19 s b) = (term19 s b).
Proof. exact (MK_COMB (@lem5231959) (@lem5231958 s b)). Qed.
Lemma lem5231961 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5231962 (s : real -> Prop) (b : real) : (term45 s b) = (term45 s b).
Proof. exact (MK_COMB (@lem5231961) (@lem5231960 s b)). Qed.
Lemma lem5231963 (s : real -> Prop) (b : real) (y : real) : (term82 s b y) = (term82 s b y).
Proof. exact (MK_COMB (@lem5231962 s b) (@lem5231952 b y)). Qed.
Lemma lem5231964 (s : real -> Prop) (y : real) : (term83 s y) = (term83 s y).
Proof. exact (fun_ext (fun b : real => @lem5231963 s b y)). Qed.
Lemma lem5231965 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5231966 (s : real -> Prop) (y : real) : (term84 s y) = (term84 s y).
Proof. exact (MK_COMB (@lem5231965) (@lem5231964 s y)). Qed.
Lemma lem5231971 (s : real -> Prop) (y : real) (x : real) : (term80 s y x) = (term80 s y x).
Proof. exact (eq_refl (term80 s y x)). Qed.
Lemma lem5231972 (s : real -> Prop) (y : real) : (term81 s y) = (term81 s y).
Proof. exact (fun_ext (fun x : real => @lem5231971 s y x)). Qed.
Lemma lem5231973 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5231974 (s : real -> Prop) (y : real) : (term19 s y) = (term19 s y).
Proof. exact (MK_COMB (@lem5231973) (@lem5231972 s y)). Qed.
Lemma lem5231975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5231976 (s : real -> Prop) (y : real) : (term85 s y) = (term85 s y).
Proof. exact (MK_COMB (@lem5231975) (@lem5231974 s y)). Qed.
Lemma lem5231977 (s : real -> Prop) (y : real) : (term56 s y) = (term56 s y).
Proof. exact (MK_COMB (@lem5231976 s y) (@lem5231966 s y)). Qed.
Lemma lem5231978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5231979 (s : real -> Prop) (y : real) : (term58 s y) = (term58 s y).
Proof. exact (MK_COMB (@lem5231978) (@lem5231977 s y)). Qed.
Lemma lem5231980 (s : real -> Prop) (y : real) (b : real) : ((term56 s y) = (y = b)) = ((term56 s y) = (y = b)).
Proof. exact (MK_COMB (@lem5231979 s y) (@lem5231951 y b)). Qed.
Lemma lem5231981 (s : real -> Prop) (b : real) : (term60 s b) = (term60 s b).
Proof. exact (fun_ext (fun y : real => @lem5231980 s y b)). Qed.
Lemma lem5231982 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5231983 (s : real -> Prop) (b : real) : (term61 s b) = (term61 s b).
Proof. exact (MK_COMB (@lem5231982) (@lem5231981 s b)). Qed.
Lemma lem5231984 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5231985 (s : real -> Prop) (b : real) : (term62 s b) = (term62 s b).
Proof. exact (MK_COMB (@lem5231984) (@lem5231983 s b)). Qed.
Lemma lem5231986 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5231987 (s : real -> Prop) (b : real) : (term63 s b) = (term63 s b).
Proof. exact (MK_COMB (@lem5231986) (@lem5231985 s b)). Qed.
Lemma lem5231988 (s : real -> Prop) (b : real) : (term64 s b) = (term64 s b).
Proof. exact (MK_COMB (@lem5231987 s b) (@lem5231950)). Qed.
Lemma lem5231993 (s : real -> Prop) (x : real) (b' : real) : (term86 s x b') = (term86 s x b').
Proof. exact (eq_refl (term86 s x b')). Qed.
Lemma lem5231994 (s : real -> Prop) (b' : real) : (term87 s b') = (term87 s b').
Proof. exact (fun_ext (fun x : real => @lem5231993 s x b')). Qed.
Lemma lem5231995 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5231996 (s : real -> Prop) (b' : real) : (term88 s b') = (term88 s b').
Proof. exact (MK_COMB (@lem5231995) (@lem5231994 s b')). Qed.
Lemma lem5231999 (b : real) (b' : real) : (term89 b b') = (term89 b b').
Proof. exact (eq_refl (term89 b b')). Qed.
Lemma lem5232000 (b : real) (s : real -> Prop) (b' : real) : (term90 b s b') = (term90 b s b').
Proof. exact (MK_COMB (@lem5231999 b b') (@lem5231996 s b')). Qed.
Lemma lem5232001 (b : real) (s : real -> Prop) : (term91 b s) = (term91 b s).
Proof. exact (fun_ext (fun b' : real => @lem5232000 b s b')). Qed.
Lemma lem5232002 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232003 (b : real) (s : real -> Prop) : (term18 b s) = (term18 b s).
Proof. exact (MK_COMB (@lem5232002) (@lem5232001 b s)). Qed.
Lemma lem5232004 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5232005 (b : real) (s : real -> Prop) : (term42 b s) = (term42 b s).
Proof. exact (MK_COMB (@lem5232004) (@lem5232003 b s)). Qed.
Lemma lem5232006 (s : real -> Prop) (b : real) : (term65 s b) = (term65 s b).
Proof. exact (MK_COMB (@lem5232005 b s) (@lem5231988 s b)). Qed.
Lemma lem5232011 (s : real -> Prop) (b : real) (x : real) : (term80 s b x) = (term80 s b x).
Proof. exact (eq_refl (term80 s b x)). Qed.
Lemma lem5232012 (s : real -> Prop) (b : real) : (term81 s b) = (term81 s b).
Proof. exact (fun_ext (fun x : real => @lem5232011 s b x)). Qed.
Lemma lem5232013 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232014 (s : real -> Prop) (b : real) : (term19 s b) = (term19 s b).
Proof. exact (MK_COMB (@lem5232013) (@lem5232012 s b)). Qed.
Lemma lem5232015 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5232016 (s : real -> Prop) (b : real) : (term45 s b) = (term45 s b).
Proof. exact (MK_COMB (@lem5232015) (@lem5232014 s b)). Qed.
Lemma lem5232017 (s : real -> Prop) (b : real) : (term66 s b) = (term66 s b).
Proof. exact (MK_COMB (@lem5232016 s b) (@lem5232006 s b)). Qed.
Lemma lem5232018 (b : real) : (term67 b) = (term67 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5232017 s b)). Qed.
Lemma lem5232019 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5232020 (b : real) : (term68 b) = (term68 b).
Proof. exact (MK_COMB (@lem5232019) (@lem5232018 b)). Qed.
Lemma lem5232021 : term69 = term69.
Proof. exact (fun_ext (fun b : real => @lem5232020 b)). Qed.
Lemma lem5232022 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232023 : term70 = term70.
Proof. exact (MK_COMB (@lem5232022) (@lem5232021)). Qed.
Lemma lem5232128 : term53 = term70.
Proof. exact (TRANS (@lem5231917) (@lem5232023)). Qed.
Lemma lem5232129 : term70 = term53.
Proof. exact (SYM (@lem5232128)). Qed.
Lemma lem5232130 (s : real -> Prop) (b : real) (h1 : term19 s b) : term19 s b.
Proof. exact (h1). Qed.
Lemma lem5232131 (b : real) (s : real -> Prop) (h1 : term18 b s) : term18 b s.
Proof. exact (h1). Qed.
Lemma lem5232132 (s : real -> Prop) (b : real) (h1 : term62 s b) : term62 s b.
Proof. exact (h1). Qed.
Lemma lem5232133 (h1 : term79) : term79.
Proof. exact (h1). Qed.
Lemma lem5232134 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem5232141 (s : real -> Prop) (b : real) (x : real) : (term80 s b x) = (term92 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5232142 (s : real -> Prop) (b : real) : (term81 s b) = (term93 s b).
Proof. exact (fun_ext (fun x : real => @lem5232141 s b x)). Qed.
Lemma lem5232143 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232196 (s : real -> Prop) (b : real) : (term19 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5232143) (@lem5232142 s b)). Qed.
Lemma lem5232197 (s : real -> Prop) (b : real) (h1 : term19 s b) : term94 s b.
Proof. exact (EQ_MP (@lem5232196 s b) (@lem5232130 s b h1)). Qed.
Lemma lem5232203 (s : real -> Prop) (x : real) (b' : real) : (term86 s x b') = (term86 s x b').
Proof. exact (eq_refl (term86 s x b')). Qed.
Lemma lem5232204 (s : real -> Prop) (b' : real) : (term87 s b') = (term87 s b').
Proof. exact (fun_ext (fun x : real => @lem5232203 s x b')). Qed.
Lemma lem5232205 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232206 (s : real -> Prop) (b' : real) : (term88 s b') = (term88 s b').
Proof. exact (MK_COMB (@lem5232205) (@lem5232204 s b')). Qed.
Lemma lem5232208 (b : real) (b' : real) : (term95 b b') = (term95 b b').
Proof. exact (eq_refl (term95 b b')). Qed.
Lemma lem5232209 (b : real) (s : real -> Prop) (b' : real) : (term96 b s b') = (term96 b s b').
Proof. exact (MK_COMB (@lem5232208 b b') (@lem5232206 s b')). Qed.
Lemma lem5232210 (b : real) (s : real -> Prop) (b' : real) : (term90 b s b') = (term96 b s b').
Proof. exact (@lem17265 (real_lt b b') (term88 s b')). Qed.
Lemma lem5232211 (b : real) (s : real -> Prop) (b' : real) : (term90 b s b') = (term96 b s b').
Proof. exact (TRANS (@lem5232210 b s b') (@lem5232209 b s b')). Qed.
Lemma lem5232212 (b : real) (s : real -> Prop) : (term91 b s) = (term97 b s).
Proof. exact (fun_ext (fun b' : real => @lem5232211 b s b')). Qed.
Lemma lem5232213 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232214 (b : real) (s : real -> Prop) : (term18 b s) = (term98 b s).
Proof. exact (MK_COMB (@lem5232213) (@lem5232212 b s)). Qed.
Lemma lem5232313 {A : Type'} (P : Prop) (Q : A -> Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5232314 (P : Prop) (Q : real -> Prop) : (term101 P Q) = (term102 P Q).
Proof. exact (@lem5232313 real P Q). Qed.
Lemma lem5232315 (b : real) (s : real -> Prop) (b' : real) : (term103 b s b') = (term104 b s b').
Proof. exact (@lem5232314 (term105 b b') (term87 s b')). Qed.
Lemma lem5232316 (s : real -> Prop) (x : real) (b' : real) : (term106 s b' x) = (term86 s x b').
Proof. exact (eq_refl (term106 s b' x)). Qed.
Lemma lem5232317 (s : real -> Prop) (b' : real) : (term107 s b') = (term87 s b').
Proof. exact (fun_ext (fun x : real => @lem5232316 s x b')). Qed.
Lemma lem5232318 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232319 (s : real -> Prop) (b' : real) : (term108 s b') = (term88 s b').
Proof. exact (MK_COMB (@lem5232318) (@lem5232317 s b')). Qed.
Lemma lem5232320 (b : real) (b' : real) : (term95 b b') = (term95 b b').
Proof. exact (eq_refl (term95 b b')). Qed.
Lemma lem5232321 (b : real) (s : real -> Prop) (b' : real) : (term103 b s b') = (term96 b s b').
Proof. exact (MK_COMB (@lem5232320 b b') (@lem5232319 s b')). Qed.
Lemma lem5232322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5232323 (b : real) (s : real -> Prop) (b' : real) : (term109 b s b') = (term110 b s b').
Proof. exact (MK_COMB (@lem5232322) (@lem5232321 b s b')). Qed.
Lemma lem5232324 (s : real -> Prop) (x : real) (b' : real) : (term106 s b' x) = (term86 s x b').
Proof. exact (eq_refl (term106 s b' x)). Qed.
Lemma lem5232325 (b : real) (b' : real) : (term95 b b') = (term95 b b').
Proof. exact (eq_refl (term95 b b')). Qed.
Lemma lem5232326 (b : real) (s : real -> Prop) (x : real) (b' : real) : (term111 b s b' x) = (term112 b s x b').
Proof. exact (MK_COMB (@lem5232325 b b') (@lem5232324 s x b')). Qed.
Lemma lem5232327 (b : real) (s : real -> Prop) (b' : real) : (term113 b s b') = (term114 b s b').
Proof. exact (fun_ext (fun x : real => @lem5232326 b s x b')). Qed.
Lemma lem5232328 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232329 (b : real) (s : real -> Prop) (b' : real) : (term104 b s b') = (term115 b s b').
Proof. exact (MK_COMB (@lem5232328) (@lem5232327 b s b')). Qed.
Lemma lem5232330 (b : real) (s : real -> Prop) (b' : real) : ((term103 b s b') = (term104 b s b')) = ((term96 b s b') = (term115 b s b')).
Proof. exact (MK_COMB (@lem5232323 b s b') (@lem5232329 b s b')). Qed.
Lemma lem5232331 (b : real) (s : real -> Prop) (b' : real) : (term96 b s b') = (term115 b s b').
Proof. exact (EQ_MP (@lem5232330 b s b') (@lem5232315 b s b')). Qed.
Lemma lem5232332 (b : real) (s : real -> Prop) : (term97 b s) = (term116 b s).
Proof. exact (fun_ext (fun b' : real => @lem5232331 b s b')). Qed.
Lemma lem5232333 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232334 (b : real) (s : real -> Prop) : (term98 b s) = (term117 b s).
Proof. exact (MK_COMB (@lem5232333) (@lem5232332 b s)). Qed.
Lemma lem5232336 {A B : Type'} (P : type1413 A B) : (term118 A B P) = (term119 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5232337 (P : type1626) : (term120 P) = (term121 P).
Proof. exact (@lem5232336 real real P). Qed.
Lemma lem5232338 (b : real) (s : real -> Prop) : (term122 b s) = (term123 b s).
Proof. exact (@lem5232337 (term124 b s)). Qed.
Lemma lem5232339 (b : real) (s : real -> Prop) (b' : real) : (term125 b s b') = (term114 b s b').
Proof. exact (eq_refl (term125 b s b')). Qed.
Lemma lem5232340 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5232341 (b : real) (s : real -> Prop) (b' : real) (x : real) : (term126 b s b' x) = (term127 b s b' x).
Proof. exact (MK_COMB (@lem5232339 b s b') (@lem5232340 x)). Qed.
Lemma lem5232342 (b : real) (s : real -> Prop) (x : real) (b' : real) : (term127 b s b' x) = (term112 b s x b').
Proof. exact (eq_refl (term127 b s b' x)). Qed.
Lemma lem5232343 (b : real) (s : real -> Prop) (x : real) (b' : real) : (term126 b s b' x) = (term112 b s x b').
Proof. exact (TRANS (@lem5232341 b s b' x) (@lem5232342 b s x b')). Qed.
Lemma lem5232344 (b : real) (s : real -> Prop) (b' : real) : (term128 b s b') = (term114 b s b').
Proof. exact (fun_ext (fun x : real => @lem5232343 b s x b')). Qed.
Lemma lem5232345 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232346 (b : real) (s : real -> Prop) (b' : real) : (term129 b s b') = (term115 b s b').
Proof. exact (MK_COMB (@lem5232345) (@lem5232344 b s b')). Qed.
Lemma lem5232347 (b : real) (s : real -> Prop) : (term130 b s) = (term116 b s).
Proof. exact (fun_ext (fun b' : real => @lem5232346 b s b')). Qed.
Lemma lem5232348 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232349 (b : real) (s : real -> Prop) : (term122 b s) = (term117 b s).
Proof. exact (MK_COMB (@lem5232348) (@lem5232347 b s)). Qed.
Lemma lem5232350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5232351 (b : real) (s : real -> Prop) : (term131 b s) = (term132 b s).
Proof. exact (MK_COMB (@lem5232350) (@lem5232349 b s)). Qed.
Lemma lem5232352 (b : real) (s : real -> Prop) (b' : real) : (term125 b s b') = (term114 b s b').
Proof. exact (eq_refl (term125 b s b')). Qed.
Lemma lem5232353 (x : real -> real) (b' : real) : (x b') = (x b').
Proof. exact (eq_refl (x b')). Qed.
Lemma lem5232354 (b : real) (s : real -> Prop) (x : real -> real) (b' : real) : (term133 b s x b') = (term134 b s x b').
Proof. exact (MK_COMB (@lem5232352 b s b') (@lem5232353 x b')). Qed.
Lemma lem5232355 (b : real) (s : real -> Prop) (x : real -> real) (b' : real) : (term134 b s x b') = (term135 b s x b').
Proof. exact (eq_refl (term134 b s x b')). Qed.
Lemma lem5232356 (b : real) (s : real -> Prop) (x : real -> real) (b' : real) : (term133 b s x b') = (term135 b s x b').
Proof. exact (TRANS (@lem5232354 b s x b') (@lem5232355 b s x b')). Qed.
Lemma lem5232357 (b : real) (s : real -> Prop) (x : real -> real) : (term136 b s x) = (term137 b s x).
Proof. exact (fun_ext (fun b' : real => @lem5232356 b s x b')). Qed.
Lemma lem5232358 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232359 (b : real) (s : real -> Prop) (x : real -> real) : (term138 b s x) = (term139 b s x).
Proof. exact (MK_COMB (@lem5232358) (@lem5232357 b s x)). Qed.
Lemma lem5232360 (b : real) (s : real -> Prop) : (term140 b s) = (term141 b s).
Proof. exact (fun_ext (fun x : real -> real => @lem5232359 b s x)). Qed.
Lemma lem5232361 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5232362 (b : real) (s : real -> Prop) : (term123 b s) = (term142 b s).
Proof. exact (MK_COMB (@lem5232361) (@lem5232360 b s)). Qed.
Lemma lem5232363 (b : real) (s : real -> Prop) : ((term122 b s) = (term123 b s)) = ((term117 b s) = (term142 b s)).
Proof. exact (MK_COMB (@lem5232351 b s) (@lem5232362 b s)). Qed.
Lemma lem5232364 (b : real) (s : real -> Prop) : (term117 b s) = (term142 b s).
Proof. exact (EQ_MP (@lem5232363 b s) (@lem5232338 b s)). Qed.
Lemma lem5232366 (b : real) (s : real -> Prop) : (term98 b s) = (term142 b s).
Proof. exact (TRANS (@lem5232334 b s) (@lem5232364 b s)). Qed.
Lemma lem5232367 (b : real) (s : real -> Prop) : (term18 b s) = (term142 b s).
Proof. exact (TRANS (@lem5232214 b s) (@lem5232366 b s)). Qed.
Lemma lem5232368 (b : real) (s : real -> Prop) (h1 : term18 b s) : term142 b s.
Proof. exact (EQ_MP (@lem5232367 b s) (@lem5232131 b s h1)). Qed.
Lemma lem5232377 (s : real -> Prop) (y : real) (x : real) : (term143 s y x) = (term144 s y x).
Proof. exact (@lem17362 (@IN real x s) (real_le y x)). Qed.
Lemma lem5232382 (s : real -> Prop) (y : real) (x : real) : (term80 s y x) = (term92 s y x).
Proof. exact (@lem17265 (@IN real x s) (real_le y x)). Qed.
Lemma lem5232383 (P : real -> Prop) : (term145 P) = (term146 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5232384 (s : real -> Prop) (y : real) : (term147 s y) = (term148 s y).
Proof. exact (@lem5232383 (term81 s y)). Qed.
Lemma lem5232385 (s : real -> Prop) (y : real) (x : real) : (term149 s y x) = (term80 s y x).
Proof. exact (eq_refl (term149 s y x)). Qed.
Lemma lem5232386 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5232387 (s : real -> Prop) (y : real) (x : real) : (term150 s y x) = (term143 s y x).
Proof. exact (MK_COMB (@lem5232386) (@lem5232385 s y x)). Qed.
Lemma lem5232388 (s : real -> Prop) (y : real) (x : real) : (term150 s y x) = (term144 s y x).
Proof. exact (TRANS (@lem5232387 s y x) (@lem5232377 s y x)). Qed.
Lemma lem5232389 (s : real -> Prop) (y : real) : (term151 s y) = (term152 s y).
Proof. exact (fun_ext (fun x : real => @lem5232388 s y x)). Qed.
Lemma lem5232390 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232391 (s : real -> Prop) (y : real) : (term148 s y) = (term153 s y).
Proof. exact (MK_COMB (@lem5232390) (@lem5232389 s y)). Qed.
Lemma lem5232392 (s : real -> Prop) (y : real) : (term147 s y) = (term153 s y).
Proof. exact (TRANS (@lem5232384 s y) (@lem5232391 s y)). Qed.
Lemma lem5232393 (s : real -> Prop) (y : real) : (term81 s y) = (term93 s y).
Proof. exact (fun_ext (fun x : real => @lem5232382 s y x)). Qed.
Lemma lem5232394 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232395 (s : real -> Prop) (y : real) : (term19 s y) = (term94 s y).
Proof. exact (MK_COMB (@lem5232394) (@lem5232393 s y)). Qed.
Lemma lem5232404 (s : real -> Prop) (b : real) (x : real) : (term143 s b x) = (term144 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5232409 (s : real -> Prop) (b : real) (x : real) : (term80 s b x) = (term92 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5232410 (P : real -> Prop) : (term145 P) = (term146 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5232411 (s : real -> Prop) (b : real) : (term147 s b) = (term148 s b).
Proof. exact (@lem5232410 (term81 s b)). Qed.
Lemma lem5232412 (s : real -> Prop) (b : real) (x : real) : (term149 s b x) = (term80 s b x).
Proof. exact (eq_refl (term149 s b x)). Qed.
Lemma lem5232413 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5232414 (s : real -> Prop) (b : real) (x : real) : (term150 s b x) = (term143 s b x).
Proof. exact (MK_COMB (@lem5232413) (@lem5232412 s b x)). Qed.
Lemma lem5232415 (s : real -> Prop) (b : real) (x : real) : (term150 s b x) = (term144 s b x).
Proof. exact (TRANS (@lem5232414 s b x) (@lem5232404 s b x)). Qed.
Lemma lem5232416 (s : real -> Prop) (b : real) : (term151 s b) = (term152 s b).
Proof. exact (fun_ext (fun x : real => @lem5232415 s b x)). Qed.
Lemma lem5232417 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232418 (s : real -> Prop) (b : real) : (term148 s b) = (term153 s b).
Proof. exact (MK_COMB (@lem5232417) (@lem5232416 s b)). Qed.
Lemma lem5232419 (s : real -> Prop) (b : real) : (term147 s b) = (term153 s b).
Proof. exact (TRANS (@lem5232411 s b) (@lem5232418 s b)). Qed.
Lemma lem5232420 (s : real -> Prop) (b : real) : (term81 s b) = (term93 s b).
Proof. exact (fun_ext (fun x : real => @lem5232409 s b x)). Qed.
Lemma lem5232421 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232422 (s : real -> Prop) (b : real) : (term19 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5232421) (@lem5232420 s b)). Qed.
Lemma lem5232423 (b : real) (y : real) : (term71 b y) = (term71 b y).
Proof. exact (eq_refl (term71 b y)). Qed.
Lemma lem5232424 (b : real) (y : real) : (real_le b y) = (real_le b y).
Proof. exact (eq_refl (real_le b y)). Qed.
Lemma lem5232425 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5232426 (s : real -> Prop) (b : real) : (term85 s b) = (term154 s b).
Proof. exact (MK_COMB (@lem5232425) (@lem5232422 s b)). Qed.
Lemma lem5232427 (s : real -> Prop) (b : real) (y : real) : (term155 s b y) = (term156 s b y).
Proof. exact (MK_COMB (@lem5232426 s b) (@lem5232423 b y)). Qed.
Lemma lem5232428 (s : real -> Prop) (b : real) (y : real) : (term157 s b y) = (term155 s b y).
Proof. exact (@lem17362 (term19 s b) (real_le b y)). Qed.
Lemma lem5232429 (s : real -> Prop) (b : real) (y : real) : (term157 s b y) = (term156 s b y).
Proof. exact (TRANS (@lem5232428 s b y) (@lem5232427 s b y)). Qed.
Lemma lem5232430 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5232431 (s : real -> Prop) (b : real) : (term158 s b) = (term159 s b).
Proof. exact (MK_COMB (@lem5232430) (@lem5232419 s b)). Qed.
Lemma lem5232432 (s : real -> Prop) (b : real) (y : real) : (term160 s b y) = (term161 s b y).
Proof. exact (MK_COMB (@lem5232431 s b) (@lem5232424 b y)). Qed.
Lemma lem5232433 (s : real -> Prop) (b : real) (y : real) : (term82 s b y) = (term160 s b y).
Proof. exact (@lem17265 (term19 s b) (real_le b y)). Qed.
Lemma lem5232434 (s : real -> Prop) (b : real) (y : real) : (term82 s b y) = (term161 s b y).
Proof. exact (TRANS (@lem5232433 s b y) (@lem5232432 s b y)). Qed.
Lemma lem5232435 (P : real -> Prop) : (term145 P) = (term146 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5232436 (s : real -> Prop) (y : real) : (term162 s y) = (term163 s y).
Proof. exact (@lem5232435 (term83 s y)). Qed.
Lemma lem5232437 (s : real -> Prop) (b : real) (y : real) : (term164 s y b) = (term82 s b y).
Proof. exact (eq_refl (term164 s y b)). Qed.
Lemma lem5232438 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5232439 (s : real -> Prop) (b : real) (y : real) : (term165 s y b) = (term157 s b y).
Proof. exact (MK_COMB (@lem5232438) (@lem5232437 s b y)). Qed.
Lemma lem5232440 (s : real -> Prop) (b : real) (y : real) : (term165 s y b) = (term156 s b y).
Proof. exact (TRANS (@lem5232439 s b y) (@lem5232429 s b y)). Qed.
Lemma lem5232441 (s : real -> Prop) (y : real) : (term166 s y) = (term167 s y).
Proof. exact (fun_ext (fun b : real => @lem5232440 s b y)). Qed.
Lemma lem5232442 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232443 (s : real -> Prop) (y : real) : (term163 s y) = (term168 s y).
Proof. exact (MK_COMB (@lem5232442) (@lem5232441 s y)). Qed.
Lemma lem5232444 (s : real -> Prop) (y : real) : (term162 s y) = (term168 s y).
Proof. exact (TRANS (@lem5232436 s y) (@lem5232443 s y)). Qed.
Lemma lem5232445 (s : real -> Prop) (y : real) : (term83 s y) = (term169 s y).
Proof. exact (fun_ext (fun b : real => @lem5232434 s b y)). Qed.
Lemma lem5232446 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232447 (s : real -> Prop) (y : real) : (term84 s y) = (term170 s y).
Proof. exact (MK_COMB (@lem5232446) (@lem5232445 s y)). Qed.
Lemma lem5232448 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5232449 (s : real -> Prop) (y : real) : (term158 s y) = (term159 s y).
Proof. exact (MK_COMB (@lem5232448) (@lem5232392 s y)). Qed.
Lemma lem5232450 (s : real -> Prop) (y : real) : (term171 s y) = (term172 s y).
Proof. exact (MK_COMB (@lem5232449 s y) (@lem5232444 s y)). Qed.
Lemma lem5232451 (s : real -> Prop) (y : real) : (term173 s y) = (term171 s y).
Proof. exact (@lem17045 (term19 s y) (term84 s y)). Qed.
Lemma lem5232452 (s : real -> Prop) (y : real) : (term173 s y) = (term172 s y).
Proof. exact (TRANS (@lem5232451 s y) (@lem5232450 s y)). Qed.
Lemma lem5232453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5232454 (s : real -> Prop) (y : real) : (term85 s y) = (term154 s y).
Proof. exact (MK_COMB (@lem5232453) (@lem5232395 s y)). Qed.
Lemma lem5232455 (s : real -> Prop) (y : real) : (term56 s y) = (term174 s y).
Proof. exact (MK_COMB (@lem5232454 s y) (@lem5232447 s y)). Qed.
Lemma lem5232456 (y : real) (b : real) : (term175 y b) = (term175 y b).
Proof. exact (eq_refl (term175 y b)). Qed.
Lemma lem5232457 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5232458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5232459 (s : real -> Prop) (y : real) : (term176 s y) = (term177 s y).
Proof. exact (MK_COMB (@lem5232458) (@lem5232452 s y)). Qed.
Lemma lem5232460 (s : real -> Prop) (y : real) (b : real) : (term178 s y b) = (term179 s y b).
Proof. exact (MK_COMB (@lem5232459 s y) (@lem5232457 y b)). Qed.
Lemma lem5232461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5232462 (s : real -> Prop) (y : real) : (term180 s y) = (term181 s y).
Proof. exact (MK_COMB (@lem5232461) (@lem5232455 s y)). Qed.
Lemma lem5232463 (s : real -> Prop) (y : real) (b : real) : (term182 s y b) = (term183 s y b).
Proof. exact (MK_COMB (@lem5232462 s y) (@lem5232456 y b)). Qed.
Lemma lem5232464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5232465 (s : real -> Prop) (y : real) (b : real) : (term184 s y b) = (term185 s y b).
Proof. exact (MK_COMB (@lem5232464) (@lem5232463 s y b)). Qed.
Lemma lem5232466 (s : real -> Prop) (y : real) (b : real) : (term186 s y b) = (term187 s y b).
Proof. exact (MK_COMB (@lem5232465 s y b) (@lem5232460 s y b)). Qed.
Lemma lem5232467 (s : real -> Prop) (y : real) (b : real) : (term188 s y b) = (term186 s y b).
Proof. exact (@lem17646 (term56 s y) (y = b)). Qed.
Lemma lem5232468 (s : real -> Prop) (y : real) (b : real) : (term188 s y b) = (term187 s y b).
Proof. exact (TRANS (@lem5232467 s y b) (@lem5232466 s y b)). Qed.
Lemma lem5232469 (P : real -> Prop) : (term145 P) = (term146 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5232470 (s : real -> Prop) (b : real) : (term62 s b) = (term189 s b).
Proof. exact (@lem5232469 (term60 s b)). Qed.
Lemma lem5232471 (s : real -> Prop) (y : real) (b : real) : (term190 s b y) = ((term56 s y) = (y = b)).
Proof. exact (eq_refl (term190 s b y)). Qed.
Lemma lem5232472 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5232473 (s : real -> Prop) (y : real) (b : real) : (term191 s b y) = (term188 s y b).
Proof. exact (MK_COMB (@lem5232472) (@lem5232471 s y b)). Qed.
Lemma lem5232474 (s : real -> Prop) (y : real) (b : real) : (term191 s b y) = (term187 s y b).
Proof. exact (TRANS (@lem5232473 s y b) (@lem5232468 s y b)). Qed.
Lemma lem5232475 (s : real -> Prop) (b : real) : (term192 s b) = (term193 s b).
Proof. exact (fun_ext (fun y : real => @lem5232474 s y b)). Qed.
Lemma lem5232476 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232477 (s : real -> Prop) (b : real) : (term189 s b) = (term194 s b).
Proof. exact (MK_COMB (@lem5232476) (@lem5232475 s b)). Qed.
Lemma lem5232478 (s : real -> Prop) (b : real) : (term62 s b) = (term194 s b).
Proof. exact (TRANS (@lem5232470 s b) (@lem5232477 s b)). Qed.
Lemma lem5232480 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term195 A P Q) = (term196 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5232481 (P : real -> Prop) (Q : real -> Prop) : (term197 P Q) = (term198 P Q).
Proof. exact (@lem5232480 real P Q). Qed.
Lemma lem5232482 (s : real -> Prop) (b : real) : (term199 s b) = (term200 s b).
Proof. exact (@lem5232481 (term201 s b) (term202 s b)). Qed.
Lemma lem5232483 (s : real -> Prop) (y : real) (b : real) : (term203 s b y) = (term183 s y b).
Proof. exact (eq_refl (term203 s b y)). Qed.
Lemma lem5232484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5232485 (s : real -> Prop) (y : real) (b : real) : (term204 s b y) = (term185 s y b).
Proof. exact (MK_COMB (@lem5232484) (@lem5232483 s y b)). Qed.
Lemma lem5232486 (s : real -> Prop) (y : real) (b : real) : (term205 s b y) = (term179 s y b).
Proof. exact (eq_refl (term205 s b y)). Qed.
Lemma lem5232487 (s : real -> Prop) (y : real) (b : real) : (term206 s b y) = (term187 s y b).
Proof. exact (MK_COMB (@lem5232485 s y b) (@lem5232486 s y b)). Qed.
Lemma lem5232488 (s : real -> Prop) (b : real) : (term207 s b) = (term193 s b).
Proof. exact (fun_ext (fun y : real => @lem5232487 s y b)). Qed.
Lemma lem5232489 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232490 (s : real -> Prop) (b : real) : (term199 s b) = (term194 s b).
Proof. exact (MK_COMB (@lem5232489) (@lem5232488 s b)). Qed.
Lemma lem5232491 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5232492 (s : real -> Prop) (b : real) : (term208 s b) = (term209 s b).
Proof. exact (MK_COMB (@lem5232491) (@lem5232490 s b)). Qed.
Lemma lem5232493 (s : real -> Prop) (y : real) (b : real) : (term203 s b y) = (term183 s y b).
Proof. exact (eq_refl (term203 s b y)). Qed.
Lemma lem5232494 (s : real -> Prop) (b : real) : (term210 s b) = (term201 s b).
Proof. exact (fun_ext (fun y : real => @lem5232493 s y b)). Qed.
Lemma lem5232495 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232496 (s : real -> Prop) (b : real) : (term211 s b) = (term212 s b).
Proof. exact (MK_COMB (@lem5232495) (@lem5232494 s b)). Qed.
Lemma lem5232497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5232498 (s : real -> Prop) (b : real) : (term213 s b) = (term214 s b).
Proof. exact (MK_COMB (@lem5232497) (@lem5232496 s b)). Qed.
Lemma lem5232499 (s : real -> Prop) (y : real) (b : real) : (term205 s b y) = (term179 s y b).
Proof. exact (eq_refl (term205 s b y)). Qed.
Lemma lem5232500 (s : real -> Prop) (b : real) : (term215 s b) = (term202 s b).
Proof. exact (fun_ext (fun y : real => @lem5232499 s y b)). Qed.
Lemma lem5232501 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232502 (s : real -> Prop) (b : real) : (term216 s b) = (term217 s b).
Proof. exact (MK_COMB (@lem5232501) (@lem5232500 s b)). Qed.
Lemma lem5232503 (s : real -> Prop) (b : real) : (term200 s b) = (term218 s b).
Proof. exact (MK_COMB (@lem5232498 s b) (@lem5232502 s b)). Qed.
Lemma lem5232504 (s : real -> Prop) (b : real) : ((term199 s b) = (term200 s b)) = ((term194 s b) = (term218 s b)).
Proof. exact (MK_COMB (@lem5232492 s b) (@lem5232503 s b)). Qed.
Lemma lem5232505 (s : real -> Prop) (b : real) : (term194 s b) = (term218 s b).
Proof. exact (EQ_MP (@lem5232504 s b) (@lem5232482 s b)). Qed.
Lemma lem5232891 {A : Type'} (P : A -> Prop) (Q : Prop) : (term219 A P Q) = (term220 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5232892 (P : real -> Prop) (Q : Prop) : (term221 P Q) = (term222 P Q).
Proof. exact (@lem5232891 real P Q). Qed.
Lemma lem5232893 (s : real -> Prop) (b : real) (y : real) : (term223 s b y) = (term224 s b y).
Proof. exact (@lem5232892 (term152 s b) (real_le b y)). Qed.
Lemma lem5232894 (s : real -> Prop) (b : real) (x : real) : (term225 s b x) = (term144 s b x).
Proof. exact (eq_refl (term225 s b x)). Qed.
Lemma lem5232895 (s : real -> Prop) (b : real) : (term226 s b) = (term152 s b).
Proof. exact (fun_ext (fun x : real => @lem5232894 s b x)). Qed.
Lemma lem5232896 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232897 (s : real -> Prop) (b : real) : (term227 s b) = (term153 s b).
Proof. exact (MK_COMB (@lem5232896) (@lem5232895 s b)). Qed.
Lemma lem5232898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5232899 (s : real -> Prop) (b : real) : (term228 s b) = (term159 s b).
Proof. exact (MK_COMB (@lem5232898) (@lem5232897 s b)). Qed.
Lemma lem5232900 (b : real) (y : real) : (real_le b y) = (real_le b y).
Proof. exact (eq_refl (real_le b y)). Qed.
Lemma lem5232901 (s : real -> Prop) (b : real) (y : real) : (term223 s b y) = (term161 s b y).
Proof. exact (MK_COMB (@lem5232899 s b) (@lem5232900 b y)). Qed.
Lemma lem5232902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5232903 (s : real -> Prop) (b : real) (y : real) : (term229 s b y) = (term230 s b y).
Proof. exact (MK_COMB (@lem5232902) (@lem5232901 s b y)). Qed.
Lemma lem5232904 (s : real -> Prop) (b : real) (x : real) : (term225 s b x) = (term144 s b x).
Proof. exact (eq_refl (term225 s b x)). Qed.
Lemma lem5232905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5232906 (s : real -> Prop) (b : real) (x : real) : (term231 s b x) = (term232 s b x).
Proof. exact (MK_COMB (@lem5232905) (@lem5232904 s b x)). Qed.
Lemma lem5232907 (b : real) (y : real) : (real_le b y) = (real_le b y).
Proof. exact (eq_refl (real_le b y)). Qed.
Lemma lem5232908 (s : real -> Prop) (x : real) (b : real) (y : real) : (term233 s x b y) = (term234 s x b y).
Proof. exact (MK_COMB (@lem5232906 s b x) (@lem5232907 b y)). Qed.
Lemma lem5232909 (s : real -> Prop) (b : real) (y : real) : (term235 s b y) = (term236 s b y).
Proof. exact (fun_ext (fun x : real => @lem5232908 s x b y)). Qed.
Lemma lem5232910 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232911 (s : real -> Prop) (b : real) (y : real) : (term224 s b y) = (term237 s b y).
Proof. exact (MK_COMB (@lem5232910) (@lem5232909 s b y)). Qed.
Lemma lem5232912 (s : real -> Prop) (b : real) (y : real) : ((term223 s b y) = (term224 s b y)) = ((term161 s b y) = (term237 s b y)).
Proof. exact (MK_COMB (@lem5232903 s b y) (@lem5232911 s b y)). Qed.
Lemma lem5232913 (s : real -> Prop) (b : real) (y : real) : (term161 s b y) = (term237 s b y).
Proof. exact (EQ_MP (@lem5232912 s b y) (@lem5232893 s b y)). Qed.
Lemma lem5232914 (s : real -> Prop) (y : real) : (term169 s y) = (term238 s y).
Proof. exact (fun_ext (fun b : real => @lem5232913 s b y)). Qed.
Lemma lem5232915 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232916 (s : real -> Prop) (y : real) : (term170 s y) = (term239 s y).
Proof. exact (MK_COMB (@lem5232915) (@lem5232914 s y)). Qed.
Lemma lem5232918 {A B : Type'} (P : type1413 A B) : (term118 A B P) = (term119 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5232919 (P : type1626) : (term120 P) = (term121 P).
Proof. exact (@lem5232918 real real P). Qed.
Lemma lem5232920 (s : real -> Prop) (y : real) : (term240 s y) = (term241 s y).
Proof. exact (@lem5232919 (term242 s y)). Qed.
Lemma lem5232921 (s : real -> Prop) (b : real) (y : real) : (term243 s y b) = (term236 s b y).
Proof. exact (eq_refl (term243 s y b)). Qed.
Lemma lem5232922 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5232923 (s : real -> Prop) (b : real) (y : real) (x : real) : (term244 s y b x) = (term245 s b y x).
Proof. exact (MK_COMB (@lem5232921 s b y) (@lem5232922 x)). Qed.
Lemma lem5232924 (s : real -> Prop) (x : real) (b : real) (y : real) : (term245 s b y x) = (term234 s x b y).
Proof. exact (eq_refl (term245 s b y x)). Qed.
Lemma lem5232925 (s : real -> Prop) (x : real) (b : real) (y : real) : (term244 s y b x) = (term234 s x b y).
Proof. exact (TRANS (@lem5232923 s b y x) (@lem5232924 s x b y)). Qed.
Lemma lem5232926 (s : real -> Prop) (b : real) (y : real) : (term246 s y b) = (term236 s b y).
Proof. exact (fun_ext (fun x : real => @lem5232925 s x b y)). Qed.
Lemma lem5232927 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5232928 (s : real -> Prop) (b : real) (y : real) : (term247 s y b) = (term237 s b y).
Proof. exact (MK_COMB (@lem5232927) (@lem5232926 s b y)). Qed.
Lemma lem5232929 (s : real -> Prop) (y : real) : (term248 s y) = (term238 s y).
Proof. exact (fun_ext (fun b : real => @lem5232928 s b y)). Qed.
Lemma lem5232930 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232931 (s : real -> Prop) (y : real) : (term240 s y) = (term239 s y).
Proof. exact (MK_COMB (@lem5232930) (@lem5232929 s y)). Qed.
Lemma lem5232932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5232933 (s : real -> Prop) (y : real) : (term249 s y) = (term250 s y).
Proof. exact (MK_COMB (@lem5232932) (@lem5232931 s y)). Qed.
Lemma lem5232934 (s : real -> Prop) (b : real) (y : real) : (term243 s y b) = (term236 s b y).
Proof. exact (eq_refl (term243 s y b)). Qed.
Lemma lem5232935 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5232936 (s : real -> Prop) (y : real) (x : real -> real) (b : real) : (term251 s y x b) = (term252 s y x b).
Proof. exact (MK_COMB (@lem5232934 s b y) (@lem5232935 x b)). Qed.
Lemma lem5232937 (s : real -> Prop) (x : real -> real) (b : real) (y : real) : (term252 s y x b) = (term253 s x b y).
Proof. exact (eq_refl (term252 s y x b)). Qed.
Lemma lem5232938 (s : real -> Prop) (x : real -> real) (b : real) (y : real) : (term251 s y x b) = (term253 s x b y).
Proof. exact (TRANS (@lem5232936 s y x b) (@lem5232937 s x b y)). Qed.
Lemma lem5232939 (s : real -> Prop) (x : real -> real) (y : real) : (term254 s y x) = (term255 s x y).
Proof. exact (fun_ext (fun b : real => @lem5232938 s x b y)). Qed.
Lemma lem5232940 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5232941 (s : real -> Prop) (x : real -> real) (y : real) : (term256 s y x) = (term257 s x y).
Proof. exact (MK_COMB (@lem5232940) (@lem5232939 s x y)). Qed.
Lemma lem5232942 (s : real -> Prop) (y : real) : (term258 s y) = (term259 s y).
Proof. exact (fun_ext (fun x : real -> real => @lem5232941 s x y)). Qed.
Lemma lem5232943 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5232944 (s : real -> Prop) (y : real) : (term241 s y) = (term260 s y).
Proof. exact (MK_COMB (@lem5232943) (@lem5232942 s y)). Qed.
Lemma lem5232945 (s : real -> Prop) (y : real) : ((term240 s y) = (term241 s y)) = ((term239 s y) = (term260 s y)).
Proof. exact (MK_COMB (@lem5232933 s y) (@lem5232944 s y)). Qed.
Lemma lem5232946 (s : real -> Prop) (y : real) : (term239 s y) = (term260 s y).
Proof. exact (EQ_MP (@lem5232945 s y) (@lem5232920 s y)). Qed.
Lemma lem5232947 (s : real -> Prop) (y : real) : (term170 s y) = (term260 s y).
Proof. exact (TRANS (@lem5232916 s y) (@lem5232946 s y)). Qed.
Lemma lem5232948 (s : real -> Prop) (y : real) : (term154 s y) = (term154 s y).
Proof. exact (eq_refl (term154 s y)). Qed.
Lemma lem5232949 (s : real -> Prop) (y : real) : (term174 s y) = (term261 s y).
Proof. exact (MK_COMB (@lem5232948 s y) (@lem5232947 s y)). Qed.
Lemma lem5232951 {A : Type'} (P : Prop) (Q : A -> Prop) : (term262 A P Q) = (term263 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5232952 (P : Prop) (Q : type1028) : (term264 P Q) = (term265 P Q).
Proof. exact (@lem5232951 (real -> real) P Q). Qed.
Lemma lem5232953 (s : real -> Prop) (y : real) : (term266 s y) = (term267 s y).
Proof. exact (@lem5232952 (term94 s y) (term259 s y)). Qed.
Lemma lem5232954 (s : real -> Prop) (x : real -> real) (y : real) : (term268 s y x) = (term257 s x y).
Proof. exact (eq_refl (term268 s y x)). Qed.
Lemma lem5232955 (s : real -> Prop) (y : real) : (term269 s y) = (term259 s y).
Proof. exact (fun_ext (fun x : real -> real => @lem5232954 s x y)). Qed.
Lemma lem5232956 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5232957 (s : real -> Prop) (y : real) : (term270 s y) = (term260 s y).
Proof. exact (MK_COMB (@lem5232956) (@lem5232955 s y)). Qed.
Lemma lem5232958 (s : real -> Prop) (y : real) : (term154 s y) = (term154 s y).
Proof. exact (eq_refl (term154 s y)). Qed.
Lemma lem5232959 (s : real -> Prop) (y : real) : (term266 s y) = (term261 s y).
Proof. exact (MK_COMB (@lem5232958 s y) (@lem5232957 s y)). Qed.
Lemma lem5232960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5232961 (s : real -> Prop) (y : real) : (term271 s y) = (term272 s y).
Proof. exact (MK_COMB (@lem5232960) (@lem5232959 s y)). Qed.
Lemma lem5232962 (s : real -> Prop) (x : real -> real) (y : real) : (term268 s y x) = (term257 s x y).
Proof. exact (eq_refl (term268 s y x)). Qed.
Lemma lem5232963 (s : real -> Prop) (y : real) : (term154 s y) = (term154 s y).
Proof. exact (eq_refl (term154 s y)). Qed.
Lemma lem5232964 (s : real -> Prop) (x : real -> real) (y : real) : (term273 s y x) = (term274 s x y).
Proof. exact (MK_COMB (@lem5232963 s y) (@lem5232962 s x y)). Qed.
Lemma lem5232965 (s : real -> Prop) (y : real) : (term275 s y) = (term276 s y).
Proof. exact (fun_ext (fun x : real -> real => @lem5232964 s x y)). Qed.
Lemma lem5232966 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5232967 (s : real -> Prop) (y : real) : (term267 s y) = (term277 s y).
Proof. exact (MK_COMB (@lem5232966) (@lem5232965 s y)). Qed.
Lemma lem5232968 (s : real -> Prop) (y : real) : ((term266 s y) = (term267 s y)) = ((term261 s y) = (term277 s y)).
Proof. exact (MK_COMB (@lem5232961 s y) (@lem5232967 s y)). Qed.
Lemma lem5232969 (s : real -> Prop) (y : real) : (term261 s y) = (term277 s y).
Proof. exact (EQ_MP (@lem5232968 s y) (@lem5232953 s y)). Qed.
Lemma lem5232970 (s : real -> Prop) (y : real) : (term174 s y) = (term277 s y).
Proof. exact (TRANS (@lem5232949 s y) (@lem5232969 s y)). Qed.
Lemma lem5232971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5232972 (s : real -> Prop) (y : real) : (term181 s y) = (term278 s y).
Proof. exact (MK_COMB (@lem5232971) (@lem5232970 s y)). Qed.
Lemma lem5232973 (y : real) (b : real) : (term175 y b) = (term175 y b).
Proof. exact (eq_refl (term175 y b)). Qed.
Lemma lem5232974 (s : real -> Prop) (y : real) (b : real) : (term183 s y b) = (term279 s y b).
Proof. exact (MK_COMB (@lem5232972 s y) (@lem5232973 y b)). Qed.
Lemma lem5232976 {A : Type'} (P : A -> Prop) (Q : Prop) : (term280 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5232977 (P : type1028) (Q : Prop) : (term282 P Q) = (term283 P Q).
Proof. exact (@lem5232976 (real -> real) P Q). Qed.
Lemma lem5232978 (s : real -> Prop) (y : real) (b : real) : (term284 s y b) = (term285 s y b).
Proof. exact (@lem5232977 (term276 s y) (term175 y b)). Qed.
Lemma lem5232979 (s : real -> Prop) (x : real -> real) (y : real) : (term286 s y x) = (term274 s x y).
Proof. exact (eq_refl (term286 s y x)). Qed.
Lemma lem5232980 (s : real -> Prop) (y : real) : (term287 s y) = (term276 s y).
Proof. exact (fun_ext (fun x : real -> real => @lem5232979 s x y)). Qed.
Lemma lem5232981 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5232982 (s : real -> Prop) (y : real) : (term288 s y) = (term277 s y).
Proof. exact (MK_COMB (@lem5232981) (@lem5232980 s y)). Qed.
Lemma lem5232983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5232984 (s : real -> Prop) (y : real) : (term289 s y) = (term278 s y).
Proof. exact (MK_COMB (@lem5232983) (@lem5232982 s y)). Qed.
Lemma lem5232985 (y : real) (b : real) : (term175 y b) = (term175 y b).
Proof. exact (eq_refl (term175 y b)). Qed.
Lemma lem5232986 (s : real -> Prop) (y : real) (b : real) : (term284 s y b) = (term279 s y b).
Proof. exact (MK_COMB (@lem5232984 s y) (@lem5232985 y b)). Qed.
Lemma lem5232987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5232988 (s : real -> Prop) (y : real) (b : real) : (term290 s y b) = (term291 s y b).
Proof. exact (MK_COMB (@lem5232987) (@lem5232986 s y b)). Qed.
Lemma lem5232989 (s : real -> Prop) (x : real -> real) (y : real) : (term286 s y x) = (term274 s x y).
Proof. exact (eq_refl (term286 s y x)). Qed.
Lemma lem5232990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5232991 (s : real -> Prop) (x : real -> real) (y : real) : (term292 s y x) = (term293 s x y).
Proof. exact (MK_COMB (@lem5232990) (@lem5232989 s x y)). Qed.
Lemma lem5232992 (y : real) (b : real) : (term175 y b) = (term175 y b).
Proof. exact (eq_refl (term175 y b)). Qed.
Lemma lem5232993 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term294 s x y b) = (term295 s x y b).
Proof. exact (MK_COMB (@lem5232991 s x y) (@lem5232992 y b)). Qed.
Lemma lem5232994 (s : real -> Prop) (y : real) (b : real) : (term296 s y b) = (term297 s y b).
Proof. exact (fun_ext (fun x : real -> real => @lem5232993 s x y b)). Qed.
Lemma lem5232995 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5232996 (s : real -> Prop) (y : real) (b : real) : (term285 s y b) = (term298 s y b).
Proof. exact (MK_COMB (@lem5232995) (@lem5232994 s y b)). Qed.
Lemma lem5232997 (s : real -> Prop) (y : real) (b : real) : ((term284 s y b) = (term285 s y b)) = ((term279 s y b) = (term298 s y b)).
Proof. exact (MK_COMB (@lem5232988 s y b) (@lem5232996 s y b)). Qed.
Lemma lem5232998 (s : real -> Prop) (y : real) (b : real) : (term279 s y b) = (term298 s y b).
Proof. exact (EQ_MP (@lem5232997 s y b) (@lem5232978 s y b)). Qed.
Lemma lem5232999 (s : real -> Prop) (y : real) (b : real) : (term183 s y b) = (term298 s y b).
Proof. exact (TRANS (@lem5232974 s y b) (@lem5232998 s y b)). Qed.
Lemma lem5233000 (s : real -> Prop) (b : real) : (term201 s b) = (term299 s b).
Proof. exact (fun_ext (fun y : real => @lem5232999 s y b)). Qed.
Lemma lem5233001 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233002 (s : real -> Prop) (b : real) : (term212 s b) = (term300 s b).
Proof. exact (MK_COMB (@lem5233001) (@lem5233000 s b)). Qed.
Lemma lem5233003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5233004 (s : real -> Prop) (b : real) : (term214 s b) = (term301 s b).
Proof. exact (MK_COMB (@lem5233003) (@lem5233002 s b)). Qed.
Lemma lem5233006 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term196 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5233007 (P : real -> Prop) (Q : real -> Prop) : (term198 P Q) = (term197 P Q).
Proof. exact (@lem5233006 real P Q). Qed.
Lemma lem5233008 (s : real -> Prop) (y : real) : (term302 s y) = (term303 s y).
Proof. exact (@lem5233007 (term152 s y) (term167 s y)). Qed.
Lemma lem5233009 (s : real -> Prop) (y : real) (b : real) : (term225 s y b) = (term144 s y b).
Proof. exact (eq_refl (term225 s y b)). Qed.
Lemma lem5233010 (s : real -> Prop) (y : real) : (term226 s y) = (term152 s y).
Proof. exact (fun_ext (fun b : real => @lem5233009 s y b)). Qed.
Lemma lem5233011 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233012 (s : real -> Prop) (y : real) : (term227 s y) = (term153 s y).
Proof. exact (MK_COMB (@lem5233011) (@lem5233010 s y)). Qed.
Lemma lem5233013 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5233014 (s : real -> Prop) (y : real) : (term228 s y) = (term159 s y).
Proof. exact (MK_COMB (@lem5233013) (@lem5233012 s y)). Qed.
Lemma lem5233015 (s : real -> Prop) (b : real) (y : real) : (term304 s y b) = (term156 s b y).
Proof. exact (eq_refl (term304 s y b)). Qed.
Lemma lem5233016 (s : real -> Prop) (y : real) : (term305 s y) = (term167 s y).
Proof. exact (fun_ext (fun b : real => @lem5233015 s b y)). Qed.
Lemma lem5233017 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233018 (s : real -> Prop) (y : real) : (term306 s y) = (term168 s y).
Proof. exact (MK_COMB (@lem5233017) (@lem5233016 s y)). Qed.
Lemma lem5233019 (s : real -> Prop) (y : real) : (term302 s y) = (term172 s y).
Proof. exact (MK_COMB (@lem5233014 s y) (@lem5233018 s y)). Qed.
Lemma lem5233020 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5233021 (s : real -> Prop) (y : real) : (term307 s y) = (term308 s y).
Proof. exact (MK_COMB (@lem5233020) (@lem5233019 s y)). Qed.
Lemma lem5233022 (s : real -> Prop) (y : real) (b : real) : (term225 s y b) = (term144 s y b).
Proof. exact (eq_refl (term225 s y b)). Qed.
Lemma lem5233023 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5233024 (s : real -> Prop) (y : real) (b : real) : (term231 s y b) = (term232 s y b).
Proof. exact (MK_COMB (@lem5233023) (@lem5233022 s y b)). Qed.
Lemma lem5233025 (s : real -> Prop) (b : real) (y : real) : (term304 s y b) = (term156 s b y).
Proof. exact (eq_refl (term304 s y b)). Qed.
Lemma lem5233026 (s : real -> Prop) (b : real) (y : real) : (term309 s y b) = (term310 s b y).
Proof. exact (MK_COMB (@lem5233024 s y b) (@lem5233025 s b y)). Qed.
Lemma lem5233027 (s : real -> Prop) (y : real) : (term311 s y) = (term312 s y).
Proof. exact (fun_ext (fun b : real => @lem5233026 s b y)). Qed.
Lemma lem5233028 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233029 (s : real -> Prop) (y : real) : (term303 s y) = (term313 s y).
Proof. exact (MK_COMB (@lem5233028) (@lem5233027 s y)). Qed.
Lemma lem5233030 (s : real -> Prop) (y : real) : ((term302 s y) = (term303 s y)) = ((term172 s y) = (term313 s y)).
Proof. exact (MK_COMB (@lem5233021 s y) (@lem5233029 s y)). Qed.
Lemma lem5233031 (s : real -> Prop) (y : real) : (term172 s y) = (term313 s y).
Proof. exact (EQ_MP (@lem5233030 s y) (@lem5233008 s y)). Qed.
Lemma lem5233034 (s : real -> Prop) (y : real) : (term314 s y) = (term314 s y).
Proof. exact (eq_refl (term314 s y)). Qed.
Lemma lem5233035 (s : real -> Prop) (y : real) : (term314 s y) = ((term172 s y) = (term313 s y)).
Proof. exact (eq_refl (term314 s y)). Qed.
Lemma lem5233036 (s : real -> Prop) (y : real) : (term315 s y) = (term315 s y).
Proof. exact (eq_refl (term315 s y)). Qed.
Lemma lem5233037 (s : real -> Prop) (y : real) : ((term314 s y) = (term314 s y)) = ((term314 s y) = ((term172 s y) = (term313 s y))).
Proof. exact (MK_COMB (@lem5233036 s y) (@lem5233035 s y)). Qed.
Lemma lem5233038 (s : real -> Prop) (y : real) : (term314 s y) = ((term172 s y) = (term313 s y)).
Proof. exact (eq_refl (term314 s y)). Qed.
Lemma lem5233039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5233040 (s : real -> Prop) (y : real) : (term315 s y) = (term316 s y).
Proof. exact (MK_COMB (@lem5233039) (@lem5233038 s y)). Qed.
Lemma lem5233041 (s : real -> Prop) (y : real) : ((term172 s y) = (term313 s y)) = ((term172 s y) = (term313 s y)).
Proof. exact (eq_refl ((term172 s y) = (term313 s y))). Qed.
Lemma lem5233042 (s : real -> Prop) (y : real) : ((term314 s y) = ((term172 s y) = (term313 s y))) = (((term172 s y) = (term313 s y)) = ((term172 s y) = (term313 s y))).
Proof. exact (MK_COMB (@lem5233040 s y) (@lem5233041 s y)). Qed.
Lemma lem5233043 (s : real -> Prop) (y : real) : ((term314 s y) = (term314 s y)) = (((term172 s y) = (term313 s y)) = ((term172 s y) = (term313 s y))).
Proof. exact (TRANS (@lem5233037 s y) (@lem5233042 s y)). Qed.
Lemma lem5233044 (s : real -> Prop) (y : real) : ((term172 s y) = (term313 s y)) = ((term172 s y) = (term313 s y)).
Proof. exact (EQ_MP (@lem5233043 s y) (@lem5233034 s y)). Qed.
Lemma lem5233045 (s : real -> Prop) (y : real) : (term172 s y) = (term313 s y).
Proof. exact (EQ_MP (@lem5233044 s y) (@lem5233031 s y)). Qed.
Lemma lem5233046 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233047 (s : real -> Prop) (y : real) : (term177 s y) = (term317 s y).
Proof. exact (MK_COMB (@lem5233046) (@lem5233045 s y)). Qed.
Lemma lem5233048 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5233049 (s : real -> Prop) (y : real) (b : real) : (term179 s y b) = (term318 s y b).
Proof. exact (MK_COMB (@lem5233047 s y) (@lem5233048 y b)). Qed.
Lemma lem5233051 {A : Type'} (P : A -> Prop) (Q : Prop) : (term280 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5233052 (P : real -> Prop) (Q : Prop) : (term319 P Q) = (term320 P Q).
Proof. exact (@lem5233051 real P Q). Qed.
Lemma lem5233053 (s : real -> Prop) (y : real) (b : real) : (term321 s y b) = (term322 s y b).
Proof. exact (@lem5233052 (term312 s y) (y = b)). Qed.
Lemma lem5233054 (s : real -> Prop) (b : real) (y : real) : (term323 s y b) = (term310 s b y).
Proof. exact (eq_refl (term323 s y b)). Qed.
Lemma lem5233055 (s : real -> Prop) (y : real) : (term324 s y) = (term312 s y).
Proof. exact (fun_ext (fun b : real => @lem5233054 s b y)). Qed.
Lemma lem5233056 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233057 (s : real -> Prop) (y : real) : (term325 s y) = (term313 s y).
Proof. exact (MK_COMB (@lem5233056) (@lem5233055 s y)). Qed.
Lemma lem5233058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233059 (s : real -> Prop) (y : real) : (term326 s y) = (term317 s y).
Proof. exact (MK_COMB (@lem5233058) (@lem5233057 s y)). Qed.
Lemma lem5233060 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5233061 (s : real -> Prop) (y : real) (b : real) : (term321 s y b) = (term318 s y b).
Proof. exact (MK_COMB (@lem5233059 s y) (@lem5233060 y b)). Qed.
Lemma lem5233062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5233063 (s : real -> Prop) (y : real) (b : real) : (term327 s y b) = (term328 s y b).
Proof. exact (MK_COMB (@lem5233062) (@lem5233061 s y b)). Qed.
Lemma lem5233064 (s : real -> Prop) (b' : real) (y : real) : (term323 s y b') = (term310 s b' y).
Proof. exact (eq_refl (term323 s y b')). Qed.
Lemma lem5233065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233066 (s : real -> Prop) (b' : real) (y : real) : (term329 s y b') = (term330 s b' y).
Proof. exact (MK_COMB (@lem5233065) (@lem5233064 s b' y)). Qed.
Lemma lem5233067 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5233068 (s : real -> Prop) (b' : real) (y : real) (b : real) : (term331 s b' y b) = (term332 s b' y b).
Proof. exact (MK_COMB (@lem5233066 s b' y) (@lem5233067 y b)). Qed.
Lemma lem5233069 (s : real -> Prop) (y : real) (b : real) : (term333 s y b) = (term334 s y b).
Proof. exact (fun_ext (fun b' : real => @lem5233068 s b' y b)). Qed.
Lemma lem5233070 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233071 (s : real -> Prop) (y : real) (b : real) : (term322 s y b) = (term335 s y b).
Proof. exact (MK_COMB (@lem5233070) (@lem5233069 s y b)). Qed.
Lemma lem5233072 (s : real -> Prop) (y : real) (b : real) : ((term321 s y b) = (term322 s y b)) = ((term318 s y b) = (term335 s y b)).
Proof. exact (MK_COMB (@lem5233063 s y b) (@lem5233071 s y b)). Qed.
Lemma lem5233073 (s : real -> Prop) (y : real) (b : real) : (term318 s y b) = (term335 s y b).
Proof. exact (EQ_MP (@lem5233072 s y b) (@lem5233053 s y b)). Qed.
Lemma lem5233074 (s : real -> Prop) (y : real) (b : real) : (term179 s y b) = (term335 s y b).
Proof. exact (TRANS (@lem5233049 s y b) (@lem5233073 s y b)). Qed.
Lemma lem5233075 (s : real -> Prop) (b : real) : (term202 s b) = (term336 s b).
Proof. exact (fun_ext (fun y : real => @lem5233074 s y b)). Qed.
Lemma lem5233076 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233077 (s : real -> Prop) (b : real) : (term217 s b) = (term337 s b).
Proof. exact (MK_COMB (@lem5233076) (@lem5233075 s b)). Qed.
Lemma lem5233078 (s : real -> Prop) (b : real) : (term218 s b) = (term338 s b).
Proof. exact (MK_COMB (@lem5233004 s b) (@lem5233077 s b)). Qed.
Lemma lem5233080 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term196 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5233081 (P : real -> Prop) (Q : real -> Prop) : (term198 P Q) = (term197 P Q).
Proof. exact (@lem5233080 real P Q). Qed.
Lemma lem5233082 (s : real -> Prop) (b : real) : (term339 s b) = (term340 s b).
Proof. exact (@lem5233081 (term299 s b) (term336 s b)). Qed.
Lemma lem5233083 (s : real -> Prop) (y : real) (b : real) : (term341 s b y) = (term298 s y b).
Proof. exact (eq_refl (term341 s b y)). Qed.
Lemma lem5233084 (s : real -> Prop) (b : real) : (term342 s b) = (term299 s b).
Proof. exact (fun_ext (fun y : real => @lem5233083 s y b)). Qed.
Lemma lem5233085 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233086 (s : real -> Prop) (b : real) : (term343 s b) = (term300 s b).
Proof. exact (MK_COMB (@lem5233085) (@lem5233084 s b)). Qed.
Lemma lem5233087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5233088 (s : real -> Prop) (b : real) : (term344 s b) = (term301 s b).
Proof. exact (MK_COMB (@lem5233087) (@lem5233086 s b)). Qed.
Lemma lem5233089 (s : real -> Prop) (y : real) (b : real) : (term345 s b y) = (term335 s y b).
Proof. exact (eq_refl (term345 s b y)). Qed.
Lemma lem5233090 (s : real -> Prop) (b : real) : (term346 s b) = (term336 s b).
Proof. exact (fun_ext (fun y : real => @lem5233089 s y b)). Qed.
Lemma lem5233091 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233092 (s : real -> Prop) (b : real) : (term347 s b) = (term337 s b).
Proof. exact (MK_COMB (@lem5233091) (@lem5233090 s b)). Qed.
Lemma lem5233093 (s : real -> Prop) (b : real) : (term339 s b) = (term338 s b).
Proof. exact (MK_COMB (@lem5233088 s b) (@lem5233092 s b)). Qed.
Lemma lem5233094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5233095 (s : real -> Prop) (b : real) : (term348 s b) = (term349 s b).
Proof. exact (MK_COMB (@lem5233094) (@lem5233093 s b)). Qed.
Lemma lem5233096 (s : real -> Prop) (y : real) (b : real) : (term341 s b y) = (term298 s y b).
Proof. exact (eq_refl (term341 s b y)). Qed.
Lemma lem5233097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5233098 (s : real -> Prop) (y : real) (b : real) : (term350 s b y) = (term351 s y b).
Proof. exact (MK_COMB (@lem5233097) (@lem5233096 s y b)). Qed.
Lemma lem5233099 (s : real -> Prop) (y : real) (b : real) : (term345 s b y) = (term335 s y b).
Proof. exact (eq_refl (term345 s b y)). Qed.
Lemma lem5233100 (s : real -> Prop) (y : real) (b : real) : (term352 s b y) = (term353 s y b).
Proof. exact (MK_COMB (@lem5233098 s y b) (@lem5233099 s y b)). Qed.
Lemma lem5233101 (s : real -> Prop) (b : real) : (term354 s b) = (term355 s b).
Proof. exact (fun_ext (fun y : real => @lem5233100 s y b)). Qed.
Lemma lem5233102 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233103 (s : real -> Prop) (b : real) : (term340 s b) = (term356 s b).
Proof. exact (MK_COMB (@lem5233102) (@lem5233101 s b)). Qed.
Lemma lem5233104 (s : real -> Prop) (b : real) : ((term339 s b) = (term340 s b)) = ((term338 s b) = (term356 s b)).
Proof. exact (MK_COMB (@lem5233095 s b) (@lem5233103 s b)). Qed.
Lemma lem5233105 (s : real -> Prop) (b : real) : (term338 s b) = (term356 s b).
Proof. exact (EQ_MP (@lem5233104 s b) (@lem5233082 s b)). Qed.
Lemma lem5233109 {A : Type'} (P : A -> Prop) (Q : Prop) : (term219 A P Q) = (term220 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5233110 (P : type1028) (Q : Prop) : (term357 P Q) = (term358 P Q).
Proof. exact (@lem5233109 (real -> real) P Q). Qed.
Lemma lem5233111 (s : real -> Prop) (y : real) (b : real) : (term359 s y b) = (term360 s y b).
Proof. exact (@lem5233110 (term297 s y b) (term335 s y b)). Qed.
Lemma lem5233112 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term361 s y b x) = (term295 s x y b).
Proof. exact (eq_refl (term361 s y b x)). Qed.
Lemma lem5233113 (s : real -> Prop) (y : real) (b : real) : (term362 s y b) = (term297 s y b).
Proof. exact (fun_ext (fun x : real -> real => @lem5233112 s x y b)). Qed.
Lemma lem5233114 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5233115 (s : real -> Prop) (y : real) (b : real) : (term363 s y b) = (term298 s y b).
Proof. exact (MK_COMB (@lem5233114) (@lem5233113 s y b)). Qed.
Lemma lem5233116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5233117 (s : real -> Prop) (y : real) (b : real) : (term364 s y b) = (term351 s y b).
Proof. exact (MK_COMB (@lem5233116) (@lem5233115 s y b)). Qed.
Lemma lem5233118 (s : real -> Prop) (y : real) (b : real) : (term335 s y b) = (term335 s y b).
Proof. exact (eq_refl (term335 s y b)). Qed.
Lemma lem5233119 (s : real -> Prop) (y : real) (b : real) : (term359 s y b) = (term353 s y b).
Proof. exact (MK_COMB (@lem5233117 s y b) (@lem5233118 s y b)). Qed.
Lemma lem5233120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5233121 (s : real -> Prop) (y : real) (b : real) : (term365 s y b) = (term366 s y b).
Proof. exact (MK_COMB (@lem5233120) (@lem5233119 s y b)). Qed.
Lemma lem5233122 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term361 s y b x) = (term295 s x y b).
Proof. exact (eq_refl (term361 s y b x)). Qed.
Lemma lem5233123 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5233124 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term367 s y b x) = (term368 s x y b).
Proof. exact (MK_COMB (@lem5233123) (@lem5233122 s x y b)). Qed.
Lemma lem5233125 (s : real -> Prop) (y : real) (b : real) : (term335 s y b) = (term335 s y b).
Proof. exact (eq_refl (term335 s y b)). Qed.
Lemma lem5233126 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term369 x s y b) = (term370 x s y b).
Proof. exact (MK_COMB (@lem5233124 s x y b) (@lem5233125 s y b)). Qed.
Lemma lem5233127 (s : real -> Prop) (y : real) (b : real) : (term371 s y b) = (term372 s y b).
Proof. exact (fun_ext (fun x : real -> real => @lem5233126 x s y b)). Qed.
Lemma lem5233128 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5233129 (s : real -> Prop) (y : real) (b : real) : (term360 s y b) = (term373 s y b).
Proof. exact (MK_COMB (@lem5233128) (@lem5233127 s y b)). Qed.
Lemma lem5233130 (s : real -> Prop) (y : real) (b : real) : ((term359 s y b) = (term360 s y b)) = ((term353 s y b) = (term373 s y b)).
Proof. exact (MK_COMB (@lem5233121 s y b) (@lem5233129 s y b)). Qed.
Lemma lem5233131 (s : real -> Prop) (y : real) (b : real) : (term353 s y b) = (term373 s y b).
Proof. exact (EQ_MP (@lem5233130 s y b) (@lem5233111 s y b)). Qed.
Lemma lem5233133 {A : Type'} (P : Prop) (Q : A -> Prop) : (term99 A P Q) = (term100 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5233134 (P : Prop) (Q : real -> Prop) : (term101 P Q) = (term102 P Q).
Proof. exact (@lem5233133 real P Q). Qed.
Lemma lem5233135 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term374 x s y b) = (term375 x s y b).
Proof. exact (@lem5233134 (term295 s x y b) (term334 s y b)). Qed.
Lemma lem5233136 (s : real -> Prop) (b' : real) (y : real) (b : real) : (term376 s y b b') = (term332 s b' y b).
Proof. exact (eq_refl (term376 s y b b')). Qed.
Lemma lem5233137 (s : real -> Prop) (y : real) (b : real) : (term377 s y b) = (term334 s y b).
Proof. exact (fun_ext (fun b' : real => @lem5233136 s b' y b)). Qed.
Lemma lem5233138 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233139 (s : real -> Prop) (y : real) (b : real) : (term378 s y b) = (term335 s y b).
Proof. exact (MK_COMB (@lem5233138) (@lem5233137 s y b)). Qed.
Lemma lem5233140 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term368 s x y b) = (term368 s x y b).
Proof. exact (eq_refl (term368 s x y b)). Qed.
Lemma lem5233141 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term374 x s y b) = (term370 x s y b).
Proof. exact (MK_COMB (@lem5233140 s x y b) (@lem5233139 s y b)). Qed.
Lemma lem5233142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5233143 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term379 x s y b) = (term380 x s y b).
Proof. exact (MK_COMB (@lem5233142) (@lem5233141 x s y b)). Qed.
Lemma lem5233144 (s : real -> Prop) (b' : real) (y : real) (b : real) : (term376 s y b b') = (term332 s b' y b).
Proof. exact (eq_refl (term376 s y b b')). Qed.
Lemma lem5233145 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term368 s x y b) = (term368 s x y b).
Proof. exact (eq_refl (term368 s x y b)). Qed.
Lemma lem5233146 (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) : (term381 x s y b b') = (term382 x s b' y b).
Proof. exact (MK_COMB (@lem5233145 s x y b) (@lem5233144 s b' y b)). Qed.
Lemma lem5233147 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term383 x s y b) = (term384 x s y b).
Proof. exact (fun_ext (fun b' : real => @lem5233146 x s b' y b)). Qed.
Lemma lem5233148 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233149 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term375 x s y b) = (term385 x s y b).
Proof. exact (MK_COMB (@lem5233148) (@lem5233147 x s y b)). Qed.
Lemma lem5233150 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : ((term374 x s y b) = (term375 x s y b)) = ((term370 x s y b) = (term385 x s y b)).
Proof. exact (MK_COMB (@lem5233143 x s y b) (@lem5233149 x s y b)). Qed.
Lemma lem5233151 (x : real -> real) (s : real -> Prop) (y : real) (b : real) : (term370 x s y b) = (term385 x s y b).
Proof. exact (EQ_MP (@lem5233150 x s y b) (@lem5233135 x s y b)). Qed.
Lemma lem5233152 (s : real -> Prop) (y : real) (b : real) : (term372 s y b) = (term386 s y b).
Proof. exact (fun_ext (fun x : real -> real => @lem5233151 x s y b)). Qed.
Lemma lem5233153 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5233154 (s : real -> Prop) (y : real) (b : real) : (term373 s y b) = (term387 s y b).
Proof. exact (MK_COMB (@lem5233153) (@lem5233152 s y b)). Qed.
Lemma lem5233155 (s : real -> Prop) (y : real) (b : real) : (term353 s y b) = (term387 s y b).
Proof. exact (TRANS (@lem5233131 s y b) (@lem5233154 s y b)). Qed.
Lemma lem5233156 (s : real -> Prop) (b : real) : (term355 s b) = (term388 s b).
Proof. exact (fun_ext (fun y : real => @lem5233155 s y b)). Qed.
Lemma lem5233157 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5233158 (s : real -> Prop) (b : real) : (term356 s b) = (term389 s b).
Proof. exact (MK_COMB (@lem5233157) (@lem5233156 s b)). Qed.
Lemma lem5233159 (s : real -> Prop) (b : real) : (term338 s b) = (term389 s b).
Proof. exact (TRANS (@lem5233105 s b) (@lem5233158 s b)). Qed.
Lemma lem5233160 (s : real -> Prop) (b : real) : (term218 s b) = (term389 s b).
Proof. exact (TRANS (@lem5233078 s b) (@lem5233159 s b)). Qed.
Lemma lem5233161 (s : real -> Prop) (b : real) : (term194 s b) = (term389 s b).
Proof. exact (TRANS (@lem5232505 s b) (@lem5233160 s b)). Qed.
Lemma lem5233162 (s : real -> Prop) (b : real) : (term62 s b) = (term389 s b).
Proof. exact (TRANS (@lem5232478 s b) (@lem5233161 s b)). Qed.
Lemma lem5233163 (s : real -> Prop) (b : real) (h1 : term62 s b) : term389 s b.
Proof. exact (EQ_MP (@lem5233162 s b) (@lem5232132 s b h1)). Qed.
Lemma lem5233172 (y : real) (x : real) : (term390 y x) = (term391 y x).
Proof. exact (@lem17045 (real_le x y) (real_le y x)). Qed.
Lemma lem5233177 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5233178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5233179 (y : real) (x : real) : (term392 y x) = (term393 y x).
Proof. exact (MK_COMB (@lem5233178) (@lem5233172 y x)). Qed.
Lemma lem5233180 (x : real) (y : real) : (term394 x y) = (term395 x y).
Proof. exact (MK_COMB (@lem5233179 y x) (@lem5233177 x y)). Qed.
Lemma lem5233185 (x : real) (y : real) : (term396 x y) = (term396 x y).
Proof. exact (eq_refl (term396 x y)). Qed.
Lemma lem5233186 (x : real) (y : real) : (term397 x y) = (term398 x y).
Proof. exact (MK_COMB (@lem5233185 x y) (@lem5233180 x y)). Qed.
Lemma lem5233187 (x : real) (y : real) : ((term75 y x) = (x = y)) = (term397 x y).
Proof. exact (@lem17784 (term75 y x) (x = y)). Qed.
Lemma lem5233188 (x : real) (y : real) : ((term75 y x) = (x = y)) = (term398 x y).
Proof. exact (TRANS (@lem5233187 x y) (@lem5233186 x y)). Qed.
Lemma lem5233189 (x : real) : (term76 x) = (term399 x).
Proof. exact (fun_ext (fun y : real => @lem5233188 x y)). Qed.
Lemma lem5233190 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233191 (x : real) : (term77 x) = (term400 x).
Proof. exact (MK_COMB (@lem5233190) (@lem5233189 x)). Qed.
Lemma lem5233192 : term78 = term401.
Proof. exact (fun_ext (fun x : real => @lem5233191 x)). Qed.
Lemma lem5233193 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233194 : term79 = term402.
Proof. exact (MK_COMB (@lem5233193) (@lem5233192)). Qed.
Lemma lem5233200 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term403 A P Q) = (term404 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5233201 (P : real -> Prop) (Q : real -> Prop) : (term405 P Q) = (term406 P Q).
Proof. exact (@lem5233200 real P Q). Qed.
Lemma lem5233202 (x : real) : (term407 x) = (term408 x).
Proof. exact (@lem5233201 (term409 x) (term410 x)). Qed.
Lemma lem5233203 (x : real) (y : real) : (term411 x y) = (term412 x y).
Proof. exact (eq_refl (term411 x y)). Qed.
Lemma lem5233204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233205 (x : real) (y : real) : (term413 x y) = (term396 x y).
Proof. exact (MK_COMB (@lem5233204) (@lem5233203 x y)). Qed.
Lemma lem5233206 (x : real) (y : real) : (term414 x y) = (term395 x y).
Proof. exact (eq_refl (term414 x y)). Qed.
Lemma lem5233207 (x : real) (y : real) : (term415 x y) = (term398 x y).
Proof. exact (MK_COMB (@lem5233205 x y) (@lem5233206 x y)). Qed.
Lemma lem5233208 (x : real) : (term416 x) = (term399 x).
Proof. exact (fun_ext (fun y : real => @lem5233207 x y)). Qed.
Lemma lem5233209 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233210 (x : real) : (term407 x) = (term400 x).
Proof. exact (MK_COMB (@lem5233209) (@lem5233208 x)). Qed.
Lemma lem5233211 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5233212 (x : real) : (term417 x) = (term418 x).
Proof. exact (MK_COMB (@lem5233211) (@lem5233210 x)). Qed.
Lemma lem5233213 (x : real) (y : real) : (term411 x y) = (term412 x y).
Proof. exact (eq_refl (term411 x y)). Qed.
Lemma lem5233214 (x : real) : (term419 x) = (term409 x).
Proof. exact (fun_ext (fun y : real => @lem5233213 x y)). Qed.
Lemma lem5233215 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233216 (x : real) : (term420 x) = (term421 x).
Proof. exact (MK_COMB (@lem5233215) (@lem5233214 x)). Qed.
Lemma lem5233217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233218 (x : real) : (term422 x) = (term423 x).
Proof. exact (MK_COMB (@lem5233217) (@lem5233216 x)). Qed.
Lemma lem5233219 (x : real) (y : real) : (term414 x y) = (term395 x y).
Proof. exact (eq_refl (term414 x y)). Qed.
Lemma lem5233220 (x : real) : (term424 x) = (term410 x).
Proof. exact (fun_ext (fun y : real => @lem5233219 x y)). Qed.
Lemma lem5233221 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233222 (x : real) : (term425 x) = (term426 x).
Proof. exact (MK_COMB (@lem5233221) (@lem5233220 x)). Qed.
Lemma lem5233223 (x : real) : (term408 x) = (term427 x).
Proof. exact (MK_COMB (@lem5233218 x) (@lem5233222 x)). Qed.
Lemma lem5233224 (x : real) : ((term407 x) = (term408 x)) = ((term400 x) = (term427 x)).
Proof. exact (MK_COMB (@lem5233212 x) (@lem5233223 x)). Qed.
Lemma lem5233225 (x : real) : (term400 x) = (term427 x).
Proof. exact (EQ_MP (@lem5233224 x) (@lem5233202 x)). Qed.
Lemma lem5233322 : term401 = term428.
Proof. exact (fun_ext (fun x : real => @lem5233225 x)). Qed.
Lemma lem5233323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233324 : term402 = term429.
Proof. exact (MK_COMB (@lem5233323) (@lem5233322)). Qed.
Lemma lem5233326 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term403 A P Q) = (term404 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5233327 (P : real -> Prop) (Q : real -> Prop) : (term405 P Q) = (term406 P Q).
Proof. exact (@lem5233326 real P Q). Qed.
Lemma lem5233328 : term430 = term431.
Proof. exact (@lem5233327 term432 term433). Qed.
Lemma lem5233329 (x : real) : (term434 x) = (term421 x).
Proof. exact (eq_refl (term434 x)). Qed.
Lemma lem5233330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233331 (x : real) : (term435 x) = (term423 x).
Proof. exact (MK_COMB (@lem5233330) (@lem5233329 x)). Qed.
Lemma lem5233332 (x : real) : (term436 x) = (term426 x).
Proof. exact (eq_refl (term436 x)). Qed.
Lemma lem5233333 (x : real) : (term437 x) = (term427 x).
Proof. exact (MK_COMB (@lem5233331 x) (@lem5233332 x)). Qed.
Lemma lem5233334 : term438 = term428.
Proof. exact (fun_ext (fun x : real => @lem5233333 x)). Qed.
Lemma lem5233335 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233336 : term430 = term429.
Proof. exact (MK_COMB (@lem5233335) (@lem5233334)). Qed.
Lemma lem5233337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5233338 : term439 = term440.
Proof. exact (MK_COMB (@lem5233337) (@lem5233336)). Qed.
Lemma lem5233339 (x : real) : (term434 x) = (term421 x).
Proof. exact (eq_refl (term434 x)). Qed.
Lemma lem5233340 : term441 = term432.
Proof. exact (fun_ext (fun x : real => @lem5233339 x)). Qed.
Lemma lem5233341 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233342 : term442 = term443.
Proof. exact (MK_COMB (@lem5233341) (@lem5233340)). Qed.
Lemma lem5233343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233344 : term444 = term445.
Proof. exact (MK_COMB (@lem5233343) (@lem5233342)). Qed.
Lemma lem5233345 (x : real) : (term436 x) = (term426 x).
Proof. exact (eq_refl (term436 x)). Qed.
Lemma lem5233346 : term446 = term433.
Proof. exact (fun_ext (fun x : real => @lem5233345 x)). Qed.
Lemma lem5233347 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233348 : term447 = term448.
Proof. exact (MK_COMB (@lem5233347) (@lem5233346)). Qed.
Lemma lem5233349 : term431 = term449.
Proof. exact (MK_COMB (@lem5233344) (@lem5233348)). Qed.
Lemma lem5233350 : (term430 = term431) = (term429 = term449).
Proof. exact (MK_COMB (@lem5233338) (@lem5233349)). Qed.
Lemma lem5233351 : term429 = term449.
Proof. exact (EQ_MP (@lem5233350) (@lem5233328)). Qed.
Lemma lem5233458 : term402 = term449.
Proof. exact (TRANS (@lem5233324) (@lem5233351)). Qed.
Lemma lem5233459 : term79 = term449.
Proof. exact (TRANS (@lem5233194) (@lem5233458)). Qed.
Lemma lem5233460 (h1 : term79) : term449.
Proof. exact (EQ_MP (@lem5233459) (@lem5232133 h1)). Qed.
Lemma lem5233464 (x : real) (y : real) : (term450 x y) = (real_le x y).
Proof. exact (@lem16933 (real_le x y)). Qed.
Lemma lem5233466 (y : real) (x : real) : (real_lt y x) = (real_lt y x).
Proof. exact (eq_refl (real_lt y x)). Qed.
Lemma lem5233467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5233468 (x : real) (y : real) : (term451 x y) = (term452 x y).
Proof. exact (MK_COMB (@lem5233467) (@lem5233464 x y)). Qed.
Lemma lem5233469 (y : real) (x : real) : (term453 y x) = (term454 y x).
Proof. exact (MK_COMB (@lem5233468 x y) (@lem5233466 y x)). Qed.
Lemma lem5233474 (y : real) (x : real) : (term455 y x) = (term455 y x).
Proof. exact (eq_refl (term455 y x)). Qed.
Lemma lem5233475 (y : real) (x : real) : (term456 y x) = (term457 y x).
Proof. exact (MK_COMB (@lem5233474 y x) (@lem5233469 y x)). Qed.
Lemma lem5233476 (y : real) (x : real) : ((term71 x y) = (real_lt y x)) = (term456 y x).
Proof. exact (@lem17784 (term71 x y) (real_lt y x)). Qed.
Lemma lem5233477 (y : real) (x : real) : ((term71 x y) = (real_lt y x)) = (term457 y x).
Proof. exact (TRANS (@lem5233476 y x) (@lem5233475 y x)). Qed.
Lemma lem5233478 (x : real) : (term72 x) = (term458 x).
Proof. exact (fun_ext (fun y : real => @lem5233477 y x)). Qed.
Lemma lem5233479 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233480 (x : real) : (term73 x) = (term459 x).
Proof. exact (MK_COMB (@lem5233479) (@lem5233478 x)). Qed.
Lemma lem5233481 : term74 = term460.
Proof. exact (fun_ext (fun x : real => @lem5233480 x)). Qed.
Lemma lem5233482 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233483 : term35 = term461.
Proof. exact (MK_COMB (@lem5233482) (@lem5233481)). Qed.
Lemma lem5233489 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term403 A P Q) = (term404 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5233490 (P : real -> Prop) (Q : real -> Prop) : (term405 P Q) = (term406 P Q).
Proof. exact (@lem5233489 real P Q). Qed.
Lemma lem5233491 (x : real) : (term462 x) = (term463 x).
Proof. exact (@lem5233490 (term464 x) (term465 x)). Qed.
Lemma lem5233492 (y : real) (x : real) : (term466 x y) = (term467 y x).
Proof. exact (eq_refl (term466 x y)). Qed.
Lemma lem5233493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233494 (y : real) (x : real) : (term468 x y) = (term455 y x).
Proof. exact (MK_COMB (@lem5233493) (@lem5233492 y x)). Qed.
Lemma lem5233495 (y : real) (x : real) : (term469 x y) = (term454 y x).
Proof. exact (eq_refl (term469 x y)). Qed.
Lemma lem5233496 (y : real) (x : real) : (term470 x y) = (term457 y x).
Proof. exact (MK_COMB (@lem5233494 y x) (@lem5233495 y x)). Qed.
Lemma lem5233497 (x : real) : (term471 x) = (term458 x).
Proof. exact (fun_ext (fun y : real => @lem5233496 y x)). Qed.
Lemma lem5233498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233499 (x : real) : (term462 x) = (term459 x).
Proof. exact (MK_COMB (@lem5233498) (@lem5233497 x)). Qed.
Lemma lem5233500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5233501 (x : real) : (term472 x) = (term473 x).
Proof. exact (MK_COMB (@lem5233500) (@lem5233499 x)). Qed.
Lemma lem5233502 (y : real) (x : real) : (term466 x y) = (term467 y x).
Proof. exact (eq_refl (term466 x y)). Qed.
Lemma lem5233503 (x : real) : (term474 x) = (term464 x).
Proof. exact (fun_ext (fun y : real => @lem5233502 y x)). Qed.
Lemma lem5233504 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233505 (x : real) : (term475 x) = (term476 x).
Proof. exact (MK_COMB (@lem5233504) (@lem5233503 x)). Qed.
Lemma lem5233506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233507 (x : real) : (term477 x) = (term478 x).
Proof. exact (MK_COMB (@lem5233506) (@lem5233505 x)). Qed.
Lemma lem5233508 (y : real) (x : real) : (term469 x y) = (term454 y x).
Proof. exact (eq_refl (term469 x y)). Qed.
Lemma lem5233509 (x : real) : (term479 x) = (term465 x).
Proof. exact (fun_ext (fun y : real => @lem5233508 y x)). Qed.
Lemma lem5233510 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233511 (x : real) : (term480 x) = (term481 x).
Proof. exact (MK_COMB (@lem5233510) (@lem5233509 x)). Qed.
Lemma lem5233512 (x : real) : (term463 x) = (term482 x).
Proof. exact (MK_COMB (@lem5233507 x) (@lem5233511 x)). Qed.
Lemma lem5233513 (x : real) : ((term462 x) = (term463 x)) = ((term459 x) = (term482 x)).
Proof. exact (MK_COMB (@lem5233501 x) (@lem5233512 x)). Qed.
Lemma lem5233514 (x : real) : (term459 x) = (term482 x).
Proof. exact (EQ_MP (@lem5233513 x) (@lem5233491 x)). Qed.
Lemma lem5233611 : term460 = term483.
Proof. exact (fun_ext (fun x : real => @lem5233514 x)). Qed.
Lemma lem5233612 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233613 : term461 = term484.
Proof. exact (MK_COMB (@lem5233612) (@lem5233611)). Qed.
Lemma lem5233615 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term403 A P Q) = (term404 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5233616 (P : real -> Prop) (Q : real -> Prop) : (term405 P Q) = (term406 P Q).
Proof. exact (@lem5233615 real P Q). Qed.
Lemma lem5233617 : term485 = term486.
Proof. exact (@lem5233616 term487 term488). Qed.
Lemma lem5233618 (x : real) : (term489 x) = (term476 x).
Proof. exact (eq_refl (term489 x)). Qed.
Lemma lem5233619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233620 (x : real) : (term490 x) = (term478 x).
Proof. exact (MK_COMB (@lem5233619) (@lem5233618 x)). Qed.
Lemma lem5233621 (x : real) : (term491 x) = (term481 x).
Proof. exact (eq_refl (term491 x)). Qed.
Lemma lem5233622 (x : real) : (term492 x) = (term482 x).
Proof. exact (MK_COMB (@lem5233620 x) (@lem5233621 x)). Qed.
Lemma lem5233623 : term493 = term483.
Proof. exact (fun_ext (fun x : real => @lem5233622 x)). Qed.
Lemma lem5233624 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233625 : term485 = term484.
Proof. exact (MK_COMB (@lem5233624) (@lem5233623)). Qed.
Lemma lem5233626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5233627 : term494 = term495.
Proof. exact (MK_COMB (@lem5233626) (@lem5233625)). Qed.
Lemma lem5233628 (x : real) : (term489 x) = (term476 x).
Proof. exact (eq_refl (term489 x)). Qed.
Lemma lem5233629 : term496 = term487.
Proof. exact (fun_ext (fun x : real => @lem5233628 x)). Qed.
Lemma lem5233630 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233631 : term497 = term498.
Proof. exact (MK_COMB (@lem5233630) (@lem5233629)). Qed.
Lemma lem5233632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233633 : term499 = term500.
Proof. exact (MK_COMB (@lem5233632) (@lem5233631)). Qed.
Lemma lem5233634 (x : real) : (term491 x) = (term481 x).
Proof. exact (eq_refl (term491 x)). Qed.
Lemma lem5233635 : term501 = term488.
Proof. exact (fun_ext (fun x : real => @lem5233634 x)). Qed.
Lemma lem5233636 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233637 : term502 = term503.
Proof. exact (MK_COMB (@lem5233636) (@lem5233635)). Qed.
Lemma lem5233638 : term486 = term504.
Proof. exact (MK_COMB (@lem5233633) (@lem5233637)). Qed.
Lemma lem5233639 : (term485 = term486) = (term484 = term504).
Proof. exact (MK_COMB (@lem5233627) (@lem5233638)). Qed.
Lemma lem5233640 : term484 = term504.
Proof. exact (EQ_MP (@lem5233639) (@lem5233617)). Qed.
Lemma lem5233747 : term461 = term504.
Proof. exact (TRANS (@lem5233613) (@lem5233640)). Qed.
Lemma lem5233748 : term35 = term504.
Proof. exact (TRANS (@lem5233483) (@lem5233747)). Qed.
Lemma lem5233749 (h1 : term35) : term504.
Proof. exact (EQ_MP (@lem5233748) (@lem5232134 h1)). Qed.
Lemma lem5233750 (s : real -> Prop) (y : real) (b : real) (h1 : term387 s y b) : term387 s y b.
Proof. exact (h1). Qed.
Lemma lem5233751 (x : real -> real) (s : real -> Prop) (y : real) (b : real) (h1 : term385 x s y b) : term385 x s y b.
Proof. exact (h1). Qed.
Lemma lem5233752 (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term382 x s b' y b) : term382 x s b' y b.
Proof. exact (h1). Qed.
Lemma lem5233753 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term139 b s x'.
Proof. exact (h1). Qed.
Lemma lem5233768 (s : real -> Prop) (b : real) (x : real) : (term92 s b x) = (term92 s b x).
Proof. exact (eq_refl (term92 s b x)). Qed.
Lemma lem5233769 (s : real -> Prop) (b : real) : (term93 s b) = (term93 s b).
Proof. exact (fun_ext (fun x : real => @lem5233768 s b x)). Qed.
Lemma lem5233770 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233771 (s : real -> Prop) (b : real) : (term94 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5233770) (@lem5233769 s b)). Qed.
Lemma lem5233772 (s : real -> Prop) (b : real) (h1 : term19 s b) : term94 s b.
Proof. exact (EQ_MP (@lem5233771 s b) (@lem5232197 s b h1)). Qed.
Lemma lem5233797 (x : real) (y : real) : (term395 x y) = (term395 x y).
Proof. exact (eq_refl (term395 x y)). Qed.
Lemma lem5233798 (x : real) : (term410 x) = (term410 x).
Proof. exact (fun_ext (fun y : real => @lem5233797 x y)). Qed.
Lemma lem5233799 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233800 (x : real) : (term426 x) = (term426 x).
Proof. exact (MK_COMB (@lem5233799) (@lem5233798 x)). Qed.
Lemma lem5233801 : term433 = term433.
Proof. exact (fun_ext (fun x : real => @lem5233800 x)). Qed.
Lemma lem5233802 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233803 : term448 = term448.
Proof. exact (MK_COMB (@lem5233802) (@lem5233801)). Qed.
Lemma lem5233826 (x : real) (y : real) : (term412 x y) = (term412 x y).
Proof. exact (eq_refl (term412 x y)). Qed.
Lemma lem5233827 (x : real) : (term409 x) = (term409 x).
Proof. exact (fun_ext (fun y : real => @lem5233826 x y)). Qed.
Lemma lem5233828 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233829 (x : real) : (term421 x) = (term421 x).
Proof. exact (MK_COMB (@lem5233828) (@lem5233827 x)). Qed.
Lemma lem5233830 : term432 = term432.
Proof. exact (fun_ext (fun x : real => @lem5233829 x)). Qed.
Lemma lem5233831 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233832 : term443 = term443.
Proof. exact (MK_COMB (@lem5233831) (@lem5233830)). Qed.
Lemma lem5233833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233834 : term445 = term445.
Proof. exact (MK_COMB (@lem5233833) (@lem5233832)). Qed.
Lemma lem5233835 : term449 = term449.
Proof. exact (MK_COMB (@lem5233834) (@lem5233803)). Qed.
Lemma lem5233836 (h1 : term79) : term449.
Proof. exact (EQ_MP (@lem5233835) (@lem5233460 h1)). Qed.
Lemma lem5233849 (y : real) (x : real) : (term454 y x) = (term454 y x).
Proof. exact (eq_refl (term454 y x)). Qed.
Lemma lem5233850 (x : real) : (term465 x) = (term465 x).
Proof. exact (fun_ext (fun y : real => @lem5233849 y x)). Qed.
Lemma lem5233851 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233852 (x : real) : (term481 x) = (term481 x).
Proof. exact (MK_COMB (@lem5233851) (@lem5233850 x)). Qed.
Lemma lem5233853 : term488 = term488.
Proof. exact (fun_ext (fun x : real => @lem5233852 x)). Qed.
Lemma lem5233854 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233855 : term503 = term503.
Proof. exact (MK_COMB (@lem5233854) (@lem5233853)). Qed.
Lemma lem5233872 (y : real) (x : real) : (term467 y x) = (term467 y x).
Proof. exact (eq_refl (term467 y x)). Qed.
Lemma lem5233873 (x : real) : (term464 x) = (term464 x).
Proof. exact (fun_ext (fun y : real => @lem5233872 y x)). Qed.
Lemma lem5233874 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233875 (x : real) : (term476 x) = (term476 x).
Proof. exact (MK_COMB (@lem5233874) (@lem5233873 x)). Qed.
Lemma lem5233876 : term487 = term487.
Proof. exact (fun_ext (fun x : real => @lem5233875 x)). Qed.
Lemma lem5233877 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233878 : term498 = term498.
Proof. exact (MK_COMB (@lem5233877) (@lem5233876)). Qed.
Lemma lem5233879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233880 : term500 = term500.
Proof. exact (MK_COMB (@lem5233879) (@lem5233878)). Qed.
Lemma lem5233881 : term504 = term504.
Proof. exact (MK_COMB (@lem5233880) (@lem5233855)). Qed.
Lemma lem5233882 (h1 : term35) : term504.
Proof. exact (EQ_MP (@lem5233881) (@lem5233749 h1)). Qed.
Lemma lem5233887 (y : real) (b : real) : (y = b) = (y = b).
Proof. exact (eq_refl (y = b)). Qed.
Lemma lem5233894 (b' : real) (y : real) : (term71 b' y) = (term71 b' y).
Proof. exact (eq_refl (term71 b' y)). Qed.
Lemma lem5233909 (s : real -> Prop) (b' : real) (x : real) : (term92 s b' x) = (term92 s b' x).
Proof. exact (eq_refl (term92 s b' x)). Qed.
Lemma lem5233910 (s : real -> Prop) (b' : real) : (term93 s b') = (term93 s b').
Proof. exact (fun_ext (fun x : real => @lem5233909 s b' x)). Qed.
Lemma lem5233911 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233912 (s : real -> Prop) (b' : real) : (term94 s b') = (term94 s b').
Proof. exact (MK_COMB (@lem5233911) (@lem5233910 s b')). Qed.
Lemma lem5233913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233914 (s : real -> Prop) (b' : real) : (term154 s b') = (term154 s b').
Proof. exact (MK_COMB (@lem5233913) (@lem5233912 s b')). Qed.
Lemma lem5233915 (s : real -> Prop) (b' : real) (y : real) : (term156 s b' y) = (term156 s b' y).
Proof. exact (MK_COMB (@lem5233914 s b') (@lem5233894 b' y)). Qed.
Lemma lem5233932 (s : real -> Prop) (y : real) (b' : real) : (term232 s y b') = (term232 s y b').
Proof. exact (eq_refl (term232 s y b')). Qed.
Lemma lem5233933 (s : real -> Prop) (b' : real) (y : real) : (term310 s b' y) = (term310 s b' y).
Proof. exact (MK_COMB (@lem5233932 s y b') (@lem5233915 s b' y)). Qed.
Lemma lem5233934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233935 (s : real -> Prop) (b' : real) (y : real) : (term330 s b' y) = (term330 s b' y).
Proof. exact (MK_COMB (@lem5233934) (@lem5233933 s b' y)). Qed.
Lemma lem5233936 (s : real -> Prop) (b' : real) (y : real) (b : real) : (term332 s b' y b) = (term332 s b' y b).
Proof. exact (MK_COMB (@lem5233935 s b' y) (@lem5233887 y b)). Qed.
Lemma lem5233943 (y : real) (b : real) : (term175 y b) = (term175 y b).
Proof. exact (eq_refl (term175 y b)). Qed.
Lemma lem5233970 (s : real -> Prop) (x : real -> real) (b : real) (y : real) : (term253 s x b y) = (term253 s x b y).
Proof. exact (eq_refl (term253 s x b y)). Qed.
Lemma lem5233971 (s : real -> Prop) (x : real -> real) (y : real) : (term255 s x y) = (term255 s x y).
Proof. exact (fun_ext (fun b : real => @lem5233970 s x b y)). Qed.
Lemma lem5233972 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233973 (s : real -> Prop) (x : real -> real) (y : real) : (term257 s x y) = (term257 s x y).
Proof. exact (MK_COMB (@lem5233972) (@lem5233971 s x y)). Qed.
Lemma lem5233988 (s : real -> Prop) (y : real) (x : real) : (term92 s y x) = (term92 s y x).
Proof. exact (eq_refl (term92 s y x)). Qed.
Lemma lem5233989 (s : real -> Prop) (y : real) : (term93 s y) = (term93 s y).
Proof. exact (fun_ext (fun x : real => @lem5233988 s y x)). Qed.
Lemma lem5233990 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5233991 (s : real -> Prop) (y : real) : (term94 s y) = (term94 s y).
Proof. exact (MK_COMB (@lem5233990) (@lem5233989 s y)). Qed.
Lemma lem5233992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233993 (s : real -> Prop) (y : real) : (term154 s y) = (term154 s y).
Proof. exact (MK_COMB (@lem5233992) (@lem5233991 s y)). Qed.
Lemma lem5233994 (s : real -> Prop) (x : real -> real) (y : real) : (term274 s x y) = (term274 s x y).
Proof. exact (MK_COMB (@lem5233993 s y) (@lem5233973 s x y)). Qed.
Lemma lem5233995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5233996 (s : real -> Prop) (x : real -> real) (y : real) : (term293 s x y) = (term293 s x y).
Proof. exact (MK_COMB (@lem5233995) (@lem5233994 s x y)). Qed.
Lemma lem5233997 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term295 s x y b) = (term295 s x y b).
Proof. exact (MK_COMB (@lem5233996 s x y) (@lem5233943 y b)). Qed.
Lemma lem5233998 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5233999 (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term368 s x y b) = (term368 s x y b).
Proof. exact (MK_COMB (@lem5233998) (@lem5233997 s x y b)). Qed.
Lemma lem5234000 (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) : (term382 x s b' y b) = (term382 x s b' y b).
Proof. exact (MK_COMB (@lem5233999 s x y b) (@lem5233936 s b' y b)). Qed.
Lemma lem5234001 (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term382 x s b' y b) : term382 x s b' y b.
Proof. exact (EQ_MP (@lem5234000 x s b' y b) (@lem5233752 x s b' y b h1)). Qed.
Lemma lem5234028 (b : real) (s : real -> Prop) (x' : real -> real) (b' : real) : (term135 b s x' b') = (term135 b s x' b').
Proof. exact (eq_refl (term135 b s x' b')). Qed.
Lemma lem5234029 (b : real) (s : real -> Prop) (x' : real -> real) : (term137 b s x') = (term137 b s x').
Proof. exact (fun_ext (fun b' : real => @lem5234028 b s x' b')). Qed.
Lemma lem5234030 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234031 (b : real) (s : real -> Prop) (x' : real -> real) : (term139 b s x') = (term139 b s x').
Proof. exact (MK_COMB (@lem5234030) (@lem5234029 b s x')). Qed.
Lemma lem5234032 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term139 b s x'.
Proof. exact (EQ_MP (@lem5234031 b s x') (@lem5233753 b s x' h1)). Qed.
Lemma lem5234033 (h1 : term35) : term503.
Proof. exact (proj2 (@lem5233882 h1)). Qed.
Lemma lem5234034 (h1 : term35) : term498.
Proof. exact (proj1 (@lem5233882 h1)). Qed.
Lemma lem5234035 (h1 : term79) : term448.
Proof. exact (proj2 (@lem5233836 h1)). Qed.
Lemma lem5234037 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term295 s x y b.
Proof. exact (h1). Qed.
Lemma lem5234038 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : term332 s b' y b.
Proof. exact (h1). Qed.
Lemma lem5234040 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term274 s x y.
Proof. exact (proj1 (@lem5234037 s x y b h1)). Qed.
Lemma lem5234041 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term257 s x y.
Proof. exact (proj2 (@lem5234040 s x y b h1)). Qed.
Lemma lem5234042 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term94 s y.
Proof. exact (proj1 (@lem5234040 s x y b h1)). Qed.
Lemma lem5234044 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : term310 s b' y.
Proof. exact (proj1 (@lem5234038 s b' y b h1)). Qed.
Lemma lem5234045 (s : real -> Prop) (y : real) (b' : real) (h1 : term144 s y b') : term144 s y b'.
Proof. exact (h1). Qed.
Lemma lem5234046 (s : real -> Prop) (b' : real) (y : real) (h1 : term156 s b' y) : term156 s b' y.
Proof. exact (h1). Qed.
Lemma lem5234050 (s : real -> Prop) (b' : real) (y : real) (h1 : term156 s b' y) : term94 s b'.
Proof. exact (proj1 (@lem5234046 s b' y h1)). Qed.
Lemma lem5234058 (s : real -> Prop) (b : real) (x : real) : (term92 s b x) = (term92 s b x).
Proof. exact (eq_refl (term92 s b x)). Qed.
Lemma lem5234059 (s : real -> Prop) (b : real) : (term93 s b) = (term93 s b).
Proof. exact (fun_ext (fun x : real => @lem5234058 s b x)). Qed.
Lemma lem5234060 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234062 (s : real -> Prop) (b : real) : (term94 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5234060) (@lem5234059 s b)). Qed.
Lemma lem5234063 (s : real -> Prop) (b : real) (h1 : term19 s b) : term94 s b.
Proof. exact (EQ_MP (@lem5234062 s b) (@lem5233772 s b h1)). Qed.
Lemma lem5234081 (s : real -> Prop) (b : real) (x' : real -> real) (b' : real) : (term135 b s x' b') = (term505 s b x' b').
Proof. exact (@lem19490 (term506 x' b' s) (term105 b b') (term507 x' b')). Qed.
Lemma lem5234082 (s : real -> Prop) (b : real) (x' : real -> real) : (term137 b s x') = (term508 s b x').
Proof. exact (fun_ext (fun b' : real => @lem5234081 s b x' b')). Qed.
Lemma lem5234083 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234085 (s : real -> Prop) (b : real) (x' : real -> real) : (term139 b s x') = (term509 s b x').
Proof. exact (MK_COMB (@lem5234083) (@lem5234082 s b x')). Qed.
Lemma lem5234086 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term509 s b x'.
Proof. exact (EQ_MP (@lem5234085 s b x') (@lem5234032 b s x' h1)). Qed.
Lemma lem5234094 (y : real) (x : real) : (term467 y x) = (term467 y x).
Proof. exact (eq_refl (term467 y x)). Qed.
Lemma lem5234095 (x : real) : (term464 x) = (term464 x).
Proof. exact (fun_ext (fun y : real => @lem5234094 y x)). Qed.
Lemma lem5234096 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234097 (x : real) : (term476 x) = (term476 x).
Proof. exact (MK_COMB (@lem5234096) (@lem5234095 x)). Qed.
Lemma lem5234098 : term487 = term487.
Proof. exact (fun_ext (fun x : real => @lem5234097 x)). Qed.
Lemma lem5234099 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234101 : term498 = term498.
Proof. exact (MK_COMB (@lem5234099) (@lem5234098)). Qed.
Lemma lem5234102 (h1 : term35) : term498.
Proof. exact (EQ_MP (@lem5234101) (@lem5234034 h1)). Qed.
Lemma lem5234110 (y : real) (x : real) : (term454 y x) = (term454 y x).
Proof. exact (eq_refl (term454 y x)). Qed.
Lemma lem5234111 (x : real) : (term465 x) = (term465 x).
Proof. exact (fun_ext (fun y : real => @lem5234110 y x)). Qed.
Lemma lem5234112 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234113 (x : real) : (term481 x) = (term481 x).
Proof. exact (MK_COMB (@lem5234112) (@lem5234111 x)). Qed.
Lemma lem5234114 : term488 = term488.
Proof. exact (fun_ext (fun x : real => @lem5234113 x)). Qed.
Lemma lem5234115 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234117 : term503 = term503.
Proof. exact (MK_COMB (@lem5234115) (@lem5234114)). Qed.
Lemma lem5234118 (h1 : term35) : term503.
Proof. exact (EQ_MP (@lem5234117) (@lem5234033 h1)). Qed.
Lemma lem5234158 (x : real) (y : real) : (term395 x y) = (term395 x y).
Proof. exact (eq_refl (term395 x y)). Qed.
Lemma lem5234159 (x : real) : (term410 x) = (term410 x).
Proof. exact (fun_ext (fun y : real => @lem5234158 x y)). Qed.
Lemma lem5234160 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234161 (x : real) : (term426 x) = (term426 x).
Proof. exact (MK_COMB (@lem5234160) (@lem5234159 x)). Qed.
Lemma lem5234162 : term433 = term433.
Proof. exact (fun_ext (fun x : real => @lem5234161 x)). Qed.
Lemma lem5234163 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234165 : term448 = term448.
Proof. exact (MK_COMB (@lem5234163) (@lem5234162)). Qed.
Lemma lem5234166 (h1 : term79) : term448.
Proof. exact (EQ_MP (@lem5234165) (@lem5234035 h1)). Qed.
Lemma lem5234178 (s : real -> Prop) (y : real) (x : real) : (term92 s y x) = (term92 s y x).
Proof. exact (eq_refl (term92 s y x)). Qed.
Lemma lem5234179 (s : real -> Prop) (y : real) : (term93 s y) = (term93 s y).
Proof. exact (fun_ext (fun x : real => @lem5234178 s y x)). Qed.
Lemma lem5234180 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234182 (s : real -> Prop) (y : real) : (term94 s y) = (term94 s y).
Proof. exact (MK_COMB (@lem5234180) (@lem5234179 s y)). Qed.
Lemma lem5234183 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term94 s y.
Proof. exact (EQ_MP (@lem5234182 s y) (@lem5234042 s x y b h1)). Qed.
Lemma lem5234201 (s : real -> Prop) (x : real -> real) (b : real) (y : real) : (term253 s x b y) = (term510 s x b y).
Proof. exact (@lem19699 (term506 x b s) (term511 x b) (real_le b y)). Qed.
Lemma lem5234202 (s : real -> Prop) (x : real -> real) (y : real) : (term255 s x y) = (term512 s x y).
Proof. exact (fun_ext (fun b : real => @lem5234201 s x b y)). Qed.
Lemma lem5234203 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234205 (s : real -> Prop) (x : real -> real) (y : real) : (term257 s x y) = (term513 s x y).
Proof. exact (MK_COMB (@lem5234203) (@lem5234202 s x y)). Qed.
Lemma lem5234206 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term513 s x y.
Proof. exact (EQ_MP (@lem5234205 s x y) (@lem5234041 s x y b h1)). Qed.
Lemma lem5234214 (s : real -> Prop) (b : real) (x : real) : (term92 s b x) = (term92 s b x).
Proof. exact (eq_refl (term92 s b x)). Qed.
Lemma lem5234215 (s : real -> Prop) (b : real) : (term93 s b) = (term93 s b).
Proof. exact (fun_ext (fun x : real => @lem5234214 s b x)). Qed.
Lemma lem5234216 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234218 (s : real -> Prop) (b : real) : (term94 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5234216) (@lem5234215 s b)). Qed.
Lemma lem5234219 (s : real -> Prop) (b : real) (h1 : term19 s b) : term94 s b.
Proof. exact (EQ_MP (@lem5234218 s b) (@lem5233772 s b h1)). Qed.
Lemma lem5234365 (s : real -> Prop) (b : real) (x' : real -> real) (b' : real) : (term135 b s x' b') = (term505 s b x' b').
Proof. exact (@lem19490 (term506 x' b' s) (term105 b b') (term507 x' b')). Qed.
Lemma lem5234366 (s : real -> Prop) (b : real) (x' : real -> real) : (term137 b s x') = (term508 s b x').
Proof. exact (fun_ext (fun b' : real => @lem5234365 s b x' b')). Qed.
Lemma lem5234367 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234369 (s : real -> Prop) (b : real) (x' : real -> real) : (term139 b s x') = (term509 s b x').
Proof. exact (MK_COMB (@lem5234367) (@lem5234366 s b x')). Qed.
Lemma lem5234370 (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term509 s b x'.
Proof. exact (EQ_MP (@lem5234369 s b x') (@lem5234032 b s x' h1)). Qed.
Lemma lem5234378 (y : real) (x : real) : (term467 y x) = (term467 y x).
Proof. exact (eq_refl (term467 y x)). Qed.
Lemma lem5234379 (x : real) : (term464 x) = (term464 x).
Proof. exact (fun_ext (fun y : real => @lem5234378 y x)). Qed.
Lemma lem5234380 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234381 (x : real) : (term476 x) = (term476 x).
Proof. exact (MK_COMB (@lem5234380) (@lem5234379 x)). Qed.
Lemma lem5234382 : term487 = term487.
Proof. exact (fun_ext (fun x : real => @lem5234381 x)). Qed.
Lemma lem5234383 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234385 : term498 = term498.
Proof. exact (MK_COMB (@lem5234383) (@lem5234382)). Qed.
Lemma lem5234386 (h1 : term35) : term498.
Proof. exact (EQ_MP (@lem5234385) (@lem5234034 h1)). Qed.
Lemma lem5234394 (y : real) (x : real) : (term454 y x) = (term454 y x).
Proof. exact (eq_refl (term454 y x)). Qed.
Lemma lem5234395 (x : real) : (term465 x) = (term465 x).
Proof. exact (fun_ext (fun y : real => @lem5234394 y x)). Qed.
Lemma lem5234396 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234397 (x : real) : (term481 x) = (term481 x).
Proof. exact (MK_COMB (@lem5234396) (@lem5234395 x)). Qed.
Lemma lem5234398 : term488 = term488.
Proof. exact (fun_ext (fun x : real => @lem5234397 x)). Qed.
Lemma lem5234399 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234401 : term503 = term503.
Proof. exact (MK_COMB (@lem5234399) (@lem5234398)). Qed.
Lemma lem5234402 (h1 : term35) : term503.
Proof. exact (EQ_MP (@lem5234401) (@lem5234033 h1)). Qed.
Lemma lem5234462 (s : real -> Prop) (b' : real) (x : real) : (term92 s b' x) = (term92 s b' x).
Proof. exact (eq_refl (term92 s b' x)). Qed.
Lemma lem5234463 (s : real -> Prop) (b' : real) : (term93 s b') = (term93 s b').
Proof. exact (fun_ext (fun x : real => @lem5234462 s b' x)). Qed.
Lemma lem5234464 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5234466 (s : real -> Prop) (b' : real) : (term94 s b') = (term94 s b').
Proof. exact (MK_COMB (@lem5234464) (@lem5234463 s b')). Qed.
Lemma lem5234467 (s : real -> Prop) (b' : real) (y : real) (h1 : term156 s b' y) : term94 s b'.
Proof. exact (EQ_MP (@lem5234466 s b') (@lem5234050 s b' y h1)). Qed.
Lemma lem5234472 (_68520 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term514 s b _68520.
Proof. exact (@lem5234063 s b h1 _68520). Qed.
Lemma lem5234473 (s : real -> Prop) (b : real) (_68520 : real) : (term514 s b _68520) = (term92 s b _68520).
Proof. exact (eq_refl (term514 s b _68520)). Qed.
Lemma lem5234475 (_68521 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term515 s b x' _68521.
Proof. exact (@lem5234086 b s x' h1 _68521). Qed.
Lemma lem5234476 (s : real -> Prop) (b : real) (x' : real -> real) (_68521 : real) : (term515 s b x' _68521) = (term505 s b x' _68521).
Proof. exact (eq_refl (term515 s b x' _68521)). Qed.
Lemma lem5234477 (_68521 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term505 s b x' _68521.
Proof. exact (EQ_MP (@lem5234476 s b x' _68521) (@lem5234475 _68521 b s x' h1)). Qed.
Lemma lem5234478 (_68522 : real) (h1 : term35) : term489 _68522.
Proof. exact (@lem5234102 h1 _68522). Qed.
Lemma lem5234479 (_68522 : real) : (term489 _68522) = (term476 _68522).
Proof. exact (eq_refl (term489 _68522)). Qed.
Lemma lem5234480 (_68522 : real) (h1 : term35) : term476 _68522.
Proof. exact (EQ_MP (@lem5234479 _68522) (@lem5234478 _68522 h1)). Qed.
Lemma lem5234481 (_68522 : real) (_68523 : real) (h1 : term35) : term466 _68522 _68523.
Proof. exact (@lem5234480 _68522 h1 _68523). Qed.
Lemma lem5234482 (_68523 : real) (_68522 : real) : (term466 _68522 _68523) = (term467 _68523 _68522).
Proof. exact (eq_refl (term466 _68522 _68523)). Qed.
Lemma lem5234484 (_68524 : real) (h1 : term35) : term491 _68524.
Proof. exact (@lem5234118 h1 _68524). Qed.
Lemma lem5234485 (_68524 : real) : (term491 _68524) = (term481 _68524).
Proof. exact (eq_refl (term491 _68524)). Qed.
Lemma lem5234486 (_68524 : real) (h1 : term35) : term481 _68524.
Proof. exact (EQ_MP (@lem5234485 _68524) (@lem5234484 _68524 h1)). Qed.
Lemma lem5234487 (_68524 : real) (_68525 : real) (h1 : term35) : term469 _68524 _68525.
Proof. exact (@lem5234486 _68524 h1 _68525). Qed.
Lemma lem5234488 (_68525 : real) (_68524 : real) : (term469 _68524 _68525) = (term454 _68525 _68524).
Proof. exact (eq_refl (term469 _68524 _68525)). Qed.
Lemma lem5234496 (_68528 : real) (h1 : term79) : term436 _68528.
Proof. exact (@lem5234166 h1 _68528). Qed.
Lemma lem5234497 (_68528 : real) : (term436 _68528) = (term426 _68528).
Proof. exact (eq_refl (term436 _68528)). Qed.
Lemma lem5234498 (_68528 : real) (h1 : term79) : term426 _68528.
Proof. exact (EQ_MP (@lem5234497 _68528) (@lem5234496 _68528 h1)). Qed.
Lemma lem5234499 (_68528 : real) (_68529 : real) (h1 : term79) : term414 _68528 _68529.
Proof. exact (@lem5234498 _68528 h1 _68529). Qed.
Lemma lem5234500 (_68528 : real) (_68529 : real) : (term414 _68528 _68529) = (term395 _68528 _68529).
Proof. exact (eq_refl (term414 _68528 _68529)). Qed.
Lemma lem5234501 (_68528 : real) (_68529 : real) (h1 : term79) : term395 _68528 _68529.
Proof. exact (EQ_MP (@lem5234500 _68528 _68529) (@lem5234499 _68528 _68529 h1)). Qed.
Lemma lem5234502 (_68530 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term514 s y _68530.
Proof. exact (@lem5234183 s x y b h1 _68530). Qed.
Lemma lem5234503 (s : real -> Prop) (y : real) (_68530 : real) : (term514 s y _68530) = (term92 s y _68530).
Proof. exact (eq_refl (term514 s y _68530)). Qed.
Lemma lem5234505 (_68531 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term516 s x y _68531.
Proof. exact (@lem5234206 s x y b h1 _68531). Qed.
Lemma lem5234506 (s : real -> Prop) (x : real -> real) (_68531 : real) (y : real) : (term516 s x y _68531) = (term510 s x _68531 y).
Proof. exact (eq_refl (term516 s x y _68531)). Qed.
Lemma lem5234507 (_68531 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term510 s x _68531 y.
Proof. exact (EQ_MP (@lem5234506 s x _68531 y) (@lem5234505 _68531 s x y b h1)). Qed.
Lemma lem5234508 (_68532 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term514 s b _68532.
Proof. exact (@lem5234219 s b h1 _68532). Qed.
Lemma lem5234509 (s : real -> Prop) (b : real) (_68532 : real) : (term514 s b _68532) = (term92 s b _68532).
Proof. exact (eq_refl (term514 s b _68532)). Qed.
Lemma lem5234541 (_68543 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term515 s b x' _68543.
Proof. exact (@lem5234370 b s x' h1 _68543). Qed.
Lemma lem5234542 (s : real -> Prop) (b : real) (x' : real -> real) (_68543 : real) : (term515 s b x' _68543) = (term505 s b x' _68543).
Proof. exact (eq_refl (term515 s b x' _68543)). Qed.
Lemma lem5234543 (_68543 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term505 s b x' _68543.
Proof. exact (EQ_MP (@lem5234542 s b x' _68543) (@lem5234541 _68543 b s x' h1)). Qed.
Lemma lem5234544 (_68544 : real) (h1 : term35) : term489 _68544.
Proof. exact (@lem5234386 h1 _68544). Qed.
Lemma lem5234545 (_68544 : real) : (term489 _68544) = (term476 _68544).
Proof. exact (eq_refl (term489 _68544)). Qed.
Lemma lem5234546 (_68544 : real) (h1 : term35) : term476 _68544.
Proof. exact (EQ_MP (@lem5234545 _68544) (@lem5234544 _68544 h1)). Qed.
Lemma lem5234547 (_68544 : real) (_68545 : real) (h1 : term35) : term466 _68544 _68545.
Proof. exact (@lem5234546 _68544 h1 _68545). Qed.
Lemma lem5234548 (_68545 : real) (_68544 : real) : (term466 _68544 _68545) = (term467 _68545 _68544).
Proof. exact (eq_refl (term466 _68544 _68545)). Qed.
Lemma lem5234550 (_68546 : real) (h1 : term35) : term491 _68546.
Proof. exact (@lem5234402 h1 _68546). Qed.
Lemma lem5234551 (_68546 : real) : (term491 _68546) = (term481 _68546).
Proof. exact (eq_refl (term491 _68546)). Qed.
Lemma lem5234552 (_68546 : real) (h1 : term35) : term481 _68546.
Proof. exact (EQ_MP (@lem5234551 _68546) (@lem5234550 _68546 h1)). Qed.
Lemma lem5234553 (_68546 : real) (_68547 : real) (h1 : term35) : term469 _68546 _68547.
Proof. exact (@lem5234552 _68546 h1 _68547). Qed.
Lemma lem5234554 (_68547 : real) (_68546 : real) : (term469 _68546 _68547) = (term454 _68547 _68546).
Proof. exact (eq_refl (term469 _68546 _68547)). Qed.
Lemma lem5234568 (_68552 : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term156 s b' y) : term514 s b' _68552.
Proof. exact (@lem5234467 s b' y h1 _68552). Qed.
Lemma lem5234569 (s : real -> Prop) (b' : real) (_68552 : real) : (term514 s b' _68552) = (term92 s b' _68552).
Proof. exact (eq_refl (term514 s b' _68552)). Qed.
Lemma lem5234590 (_68520 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term92 s b _68520.
Proof. exact (EQ_MP (@lem5234473 s b _68520) (@lem5234472 _68520 s b h1)). Qed.
Lemma lem5234596 (_68523 : real) (_68522 : real) (h1 : term35) : term467 _68523 _68522.
Proof. exact (EQ_MP (@lem5234482 _68523 _68522) (@lem5234481 _68522 _68523 h1)). Qed.
Lemma lem5234602 (_68525 : real) (_68524 : real) (h1 : term35) : term454 _68525 _68524.
Proof. exact (EQ_MP (@lem5234488 _68525 _68524) (@lem5234487 _68524 _68525 h1)). Qed.
Lemma lem5234613 (_68528 : real) (_68529 : real) : (term395 _68528 _68529) = (term517 _68528 _68529).
Proof. exact (@lem5231653 (term71 _68528 _68529) (term71 _68529 _68528) (_68528 = _68529)). Qed.
Lemma lem5234614 (_68528 : real) (_68529 : real) (h1 : term79) : term517 _68528 _68529.
Proof. exact (EQ_MP (@lem5234613 _68528 _68529) (@lem5234501 _68528 _68529 h1)). Qed.
Lemma lem5234616 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term175 y b.
Proof. exact (proj2 (@lem5234037 s x y b h1)). Qed.
Lemma lem5234622 (_68530 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term92 s y _68530.
Proof. exact (EQ_MP (@lem5234503 s y _68530) (@lem5234502 _68530 s x y b h1)). Qed.
Lemma lem5234628 (_68531 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term518 x s _68531 y.
Proof. exact (proj1 (@lem5234507 _68531 s x y b h1)). Qed.
Lemma lem5234634 (_68531 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term519 x _68531 y.
Proof. exact (proj2 (@lem5234507 _68531 s x y b h1)). Qed.
Lemma lem5234652 (_68521 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term520 b x' _68521 s.
Proof. exact (proj1 (@lem5234477 _68521 b s x' h1)). Qed.
Lemma lem5234658 (_68521 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term521 b x' _68521.
Proof. exact (proj2 (@lem5234477 _68521 b s x' h1)). Qed.
Lemma lem5234690 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : y = b.
Proof. exact (proj2 (@lem5234038 s b' y b h1)). Qed.
Lemma lem5234694 (s : real -> Prop) (y : real) (b' : real) (h1 : term144 s y b') : term71 y b'.
Proof. exact (proj2 (@lem5234045 s y b' h1)). Qed.
Lemma lem5234750 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : y = b.
Proof. exact (proj2 (@lem5234038 s b' y b h1)). Qed.
Lemma lem5234758 (s : real -> Prop) (b' : real) (y : real) (h1 : term156 s b' y) : term71 b' y.
Proof. exact (proj2 (@lem5234046 s b' y h1)). Qed.
Lemma lem5234810 (_68532 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term92 s b _68532.
Proof. exact (EQ_MP (@lem5234509 s b _68532) (@lem5234508 _68532 s b h1)). Qed.
Lemma lem5234867 (b' : real) : (term522 b') = (term522 b').
Proof. exact (eq_refl (term522 b')). Qed.
Lemma lem5234868 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : (term523 b' y) = (term523 b' b).
Proof. exact (MK_COMB (@lem5234867 b') (@lem5234690 s b' y b h1)). Qed.
Lemma lem5234869 (b : real) (b' : real) : (term523 b' b) = (term71 b b').
Proof. exact (eq_refl (term523 b' b)). Qed.
Lemma lem5234870 (b' : real) (y : real) : (term524 b' y) = (term524 b' y).
Proof. exact (eq_refl (term524 b' y)). Qed.
Lemma lem5234871 (y : real) (b : real) (b' : real) : ((term523 b' y) = (term523 b' b)) = ((term523 b' y) = (term71 b b')).
Proof. exact (MK_COMB (@lem5234870 b' y) (@lem5234869 b b')). Qed.
Lemma lem5234872 (y : real) (b' : real) : (term523 b' y) = (term71 y b').
Proof. exact (eq_refl (term523 b' y)). Qed.
Lemma lem5234873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5234874 (y : real) (b' : real) : (term524 b' y) = (term525 y b').
Proof. exact (MK_COMB (@lem5234873) (@lem5234872 y b')). Qed.
Lemma lem5234875 (b : real) (b' : real) : (term71 b b') = (term71 b b').
Proof. exact (eq_refl (term71 b b')). Qed.
Lemma lem5234876 (y : real) (b : real) (b' : real) : ((term523 b' y) = (term71 b b')) = ((term71 y b') = (term71 b b')).
Proof. exact (MK_COMB (@lem5234874 y b') (@lem5234875 b b')). Qed.
Lemma lem5234877 (y : real) (b : real) (b' : real) : ((term523 b' y) = (term523 b' b)) = ((term71 y b') = (term71 b b')).
Proof. exact (TRANS (@lem5234871 y b b') (@lem5234876 y b b')). Qed.
Lemma lem5234878 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : (term71 y b') = (term71 b b').
Proof. exact (EQ_MP (@lem5234877 y b b') (@lem5234868 s b' y b h1)). Qed.
Lemma lem5234879 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term144 s y b') (h2 : term332 s b' y b) : term71 b b'.
Proof. exact (EQ_MP (@lem5234878 s b' y b h2) (@lem5234694 s y b' h1)). Qed.
Lemma lem5234977 (_68545 : real) (_68544 : real) (h1 : term35) : term467 _68545 _68544.
Proof. exact (EQ_MP (@lem5234548 _68545 _68544) (@lem5234547 _68544 _68545 h1)). Qed.
Lemma lem5234991 (_68547 : real) (_68546 : real) (h1 : term35) : term454 _68547 _68546.
Proof. exact (EQ_MP (@lem5234554 _68547 _68546) (@lem5234553 _68546 _68547 h1)). Qed.
Lemma lem5235019 (_68552 : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term156 s b' y) : term92 s b' _68552.
Proof. exact (EQ_MP (@lem5234569 s b' _68552) (@lem5234568 _68552 s b' y h1)). Qed.
Lemma lem5235020 (b' : real) : (term526 b') = (term526 b').
Proof. exact (eq_refl (term526 b')). Qed.
Lemma lem5235021 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : (term527 b' y) = (term527 b' b).
Proof. exact (MK_COMB (@lem5235020 b') (@lem5234750 s b' y b h1)). Qed.
Lemma lem5235022 (b' : real) (b : real) : (term527 b' b) = (term71 b' b).
Proof. exact (eq_refl (term527 b' b)). Qed.
Lemma lem5235023 (b' : real) (y : real) : (term528 b' y) = (term528 b' y).
Proof. exact (eq_refl (term528 b' y)). Qed.
Lemma lem5235024 (y : real) (b' : real) (b : real) : ((term527 b' y) = (term527 b' b)) = ((term527 b' y) = (term71 b' b)).
Proof. exact (MK_COMB (@lem5235023 b' y) (@lem5235022 b' b)). Qed.
Lemma lem5235025 (b' : real) (y : real) : (term527 b' y) = (term71 b' y).
Proof. exact (eq_refl (term527 b' y)). Qed.
Lemma lem5235026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5235027 (b' : real) (y : real) : (term528 b' y) = (term525 b' y).
Proof. exact (MK_COMB (@lem5235026) (@lem5235025 b' y)). Qed.
Lemma lem5235028 (b' : real) (b : real) : (term71 b' b) = (term71 b' b).
Proof. exact (eq_refl (term71 b' b)). Qed.
Lemma lem5235029 (y : real) (b' : real) (b : real) : ((term527 b' y) = (term71 b' b)) = ((term71 b' y) = (term71 b' b)).
Proof. exact (MK_COMB (@lem5235027 b' y) (@lem5235028 b' b)). Qed.
Lemma lem5235030 (y : real) (b' : real) (b : real) : ((term527 b' y) = (term527 b' b)) = ((term71 b' y) = (term71 b' b)).
Proof. exact (TRANS (@lem5235024 y b' b) (@lem5235029 y b' b)). Qed.
Lemma lem5235031 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term332 s b' y b) : (term71 b' y) = (term71 b' b).
Proof. exact (EQ_MP (@lem5235030 y b' b) (@lem5235021 s b' y b h1)). Qed.
Lemma lem5235032 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term156 s b' y) (h2 : term332 s b' y b) : term71 b' b.
Proof. exact (EQ_MP (@lem5235031 s b' y b h2) (@lem5234758 s b' y h1)). Qed.
Lemma lem5235074 (_68543 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term520 b x' _68543 s.
Proof. exact (proj1 (@lem5234543 _68543 b s x' h1)). Qed.
Lemma lem5235088 (_68543 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term521 b x' _68543.
Proof. exact (proj2 (@lem5234543 _68543 b s x' h1)). Qed.
Lemma lem5235168 (y : real) (b : real) (h1 : term71 y b) : term71 y b.
Proof. exact (h1). Qed.
Lemma lem5235169 (y : real) (b : real) (h1 : term71 y b) : term529 y b.
Proof. exact (fun h0 : real_le y b => @lem5235168 y b h1). Qed.
Lemma lem5235171 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5235172 (y : real) (b : real) : (term529 y b) = (term71 y b).
Proof. exact (@lem5235171 (real_le y b)). Qed.
Lemma lem5235173 (y : real) (b : real) (h1 : term71 y b) : term71 y b.
Proof. exact (EQ_MP (@lem5235172 y b) (@lem5235169 y b h1)). Qed.
Lemma lem5235184 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5235185 (_68525 : real) (_68524 : real) : (term531 _68524 _68525) = (term454 _68525 _68524).
Proof. exact (@lem5235184 (real_le _68524 _68525) (real_lt _68525 _68524)). Qed.
Lemma lem5235191 (_68525 : real) (_68524 : real) : (term532 _68525 _68524) = (term532 _68525 _68524).
Proof. exact (eq_refl (term532 _68525 _68524)). Qed.
Lemma lem5235192 (_68525 : real) (_68524 : real) : ((term454 _68525 _68524) = (term531 _68524 _68525)) = ((term454 _68525 _68524) = (term454 _68525 _68524)).
Proof. exact (MK_COMB (@lem5235191 _68525 _68524) (@lem5235185 _68525 _68524)). Qed.
Lemma lem5235194 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5235195 (x : Prop) : (x = x) = True.
Proof. exact (@lem5235194 Prop x). Qed.
Lemma lem5235196 (_68525 : real) (_68524 : real) : ((term454 _68525 _68524) = (term454 _68525 _68524)) = True.
Proof. exact (@lem5235195 (term454 _68525 _68524)). Qed.
Lemma lem5235197 (_68524 : real) (_68525 : real) : ((term454 _68525 _68524) = (term531 _68524 _68525)) = True.
Proof. exact (TRANS (@lem5235192 _68525 _68524) (@lem5235196 _68525 _68524)). Qed.
Lemma lem5235198 (_68524 : real) (_68525 : real) : True = ((term454 _68525 _68524) = (term531 _68524 _68525)).
Proof. exact (SYM (@lem5235197 _68524 _68525)). Qed.
Lemma lem5235199 (_68524 : real) (_68525 : real) : (term454 _68525 _68524) = (term531 _68524 _68525).
Proof. exact (EQ_MP (@lem5235198 _68524 _68525) (@lem0)). Qed.
Lemma lem5235200 (_68524 : real) (_68525 : real) (h1 : term35) : term531 _68524 _68525.
Proof. exact (EQ_MP (@lem5235199 _68524 _68525) (@lem5234602 _68525 _68524 h1)). Qed.
Lemma lem5235202 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235205 (_68525 : real) (_68524 : real) : (term531 _68524 _68525) = (term534 _68525 _68524).
Proof. exact (@lem5235202 (real_le _68524 _68525) (real_lt _68525 _68524)). Qed.
Lemma lem5235208 (_68525 : real) (_68524 : real) (h1 : term35) : term534 _68525 _68524.
Proof. exact (EQ_MP (@lem5235205 _68525 _68524) (@lem5235200 _68524 _68525 h1)). Qed.
Lemma lem5235209 (b : real) (y : real) (h1 : term35) : term534 b y.
Proof. exact (@lem5235208 b y h1). Qed.
Lemma lem5235212 (y : real) (b : real) (h1 : term35) (h2 : term71 y b) : real_lt b y.
Proof. exact (@lem5235209 b y h1 (@lem5235173 y b h2)). Qed.
Lemma lem5235213 (y : real) (b : real) (h1 : term35) (h2 : term71 y b) : term535 b y.
Proof. exact (fun h0 : term105 b y => @lem5235212 y b h1 h2). Qed.
Lemma lem5235215 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235216 (b : real) (y : real) : (term535 b y) = (real_lt b y).
Proof. exact (@lem5235215 (real_lt b y)). Qed.
Lemma lem5235217 (y : real) (b : real) (h1 : term35) (h2 : term71 y b) : real_lt b y.
Proof. exact (EQ_MP (@lem5235216 b y) (@lem5235213 y b h1 h2)). Qed.
Lemma lem5235223 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5235224 (x' : real -> real) (s : real -> Prop) (b : real) (_68521 : real) : (term520 b x' _68521 s) = (term537 x' s b _68521).
Proof. exact (@lem5235223 (term506 x' _68521 s) (term105 b _68521)). Qed.
Lemma lem5235230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5235231 (x' : real -> real) (s : real -> Prop) (b : real) (_68521 : real) : (term538 b x' _68521 s) = (term539 x' s b _68521).
Proof. exact (MK_COMB (@lem5235230) (@lem5235224 x' s b _68521)). Qed.
Lemma lem5235237 (x' : real -> real) (s : real -> Prop) (b : real) (_68521 : real) : (term537 x' s b _68521) = (term537 x' s b _68521).
Proof. exact (eq_refl (term537 x' s b _68521)). Qed.
Lemma lem5235238 (x' : real -> real) (s : real -> Prop) (b : real) (_68521 : real) : ((term520 b x' _68521 s) = (term537 x' s b _68521)) = ((term537 x' s b _68521) = (term537 x' s b _68521)).
Proof. exact (MK_COMB (@lem5235231 x' s b _68521) (@lem5235237 x' s b _68521)). Qed.
Lemma lem5235240 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5235241 (x : Prop) : (x = x) = True.
Proof. exact (@lem5235240 Prop x). Qed.
Lemma lem5235242 (x' : real -> real) (s : real -> Prop) (b : real) (_68521 : real) : ((term537 x' s b _68521) = (term537 x' s b _68521)) = True.
Proof. exact (@lem5235241 (term537 x' s b _68521)). Qed.
Lemma lem5235243 (x' : real -> real) (s : real -> Prop) (b : real) (_68521 : real) : ((term520 b x' _68521 s) = (term537 x' s b _68521)) = True.
Proof. exact (TRANS (@lem5235238 x' s b _68521) (@lem5235242 x' s b _68521)). Qed.
Lemma lem5235244 (x' : real -> real) (s : real -> Prop) (b : real) (_68521 : real) : True = ((term520 b x' _68521 s) = (term537 x' s b _68521)).
Proof. exact (SYM (@lem5235243 x' s b _68521)). Qed.
Lemma lem5235245 (x' : real -> real) (s : real -> Prop) (b : real) (_68521 : real) : (term520 b x' _68521 s) = (term537 x' s b _68521).
Proof. exact (EQ_MP (@lem5235244 x' s b _68521) (@lem0)). Qed.
Lemma lem5235246 (_68521 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term537 x' s b _68521.
Proof. exact (EQ_MP (@lem5235245 x' s b _68521) (@lem5234652 _68521 b s x' h1)). Qed.
Lemma lem5235248 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235249 (b : real) (x' : real -> real) (_68521 : real) (s : real -> Prop) : (term537 x' s b _68521) = (term540 b x' _68521 s).
Proof. exact (@lem5235248 (term105 b _68521) (term506 x' _68521 s)). Qed.
Lemma lem5235251 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5235252 (b : real) (_68521 : real) : (term542 b _68521) = (real_lt b _68521).
Proof. exact (@lem5235251 (real_lt b _68521)). Qed.
Lemma lem5235253 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5235254 (b : real) (_68521 : real) : (term543 b _68521) = (term89 b _68521).
Proof. exact (MK_COMB (@lem5235253) (@lem5235252 b _68521)). Qed.
Lemma lem5235255 (x' : real -> real) (_68521 : real) (s : real -> Prop) : (term506 x' _68521 s) = (term506 x' _68521 s).
Proof. exact (eq_refl (term506 x' _68521 s)). Qed.
Lemma lem5235256 (b : real) (x' : real -> real) (_68521 : real) (s : real -> Prop) : (term540 b x' _68521 s) = (term544 b x' _68521 s).
Proof. exact (MK_COMB (@lem5235254 b _68521) (@lem5235255 x' _68521 s)). Qed.
Lemma lem5235257 (b : real) (x' : real -> real) (_68521 : real) (s : real -> Prop) : (term537 x' s b _68521) = (term544 b x' _68521 s).
Proof. exact (TRANS (@lem5235249 b x' _68521 s) (@lem5235256 b x' _68521 s)). Qed.
Lemma lem5235260 (_68521 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term544 b x' _68521 s.
Proof. exact (EQ_MP (@lem5235257 b x' _68521 s) (@lem5235246 _68521 b s x' h1)). Qed.
Lemma lem5235261 (y : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term544 b x' y s.
Proof. exact (@lem5235260 y b s x' h1). Qed.
Lemma lem5235264 (s : real -> Prop) (x' : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) : term506 x' y s.
Proof. exact (@lem5235261 y b s x' h2 (@lem5235217 y b h1 h3)). Qed.
Lemma lem5235265 (s : real -> Prop) (x' : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) : term545 x' y s.
Proof. exact (fun h0 : term546 x' y s => @lem5235264 s x' y b h1 h2 h3). Qed.
Lemma lem5235267 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235268 (x' : real -> real) (y : real) (s : real -> Prop) : (term545 x' y s) = (term506 x' y s).
Proof. exact (@lem5235267 (term506 x' y s)). Qed.
Lemma lem5235269 (s : real -> Prop) (x' : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) : term506 x' y s.
Proof. exact (EQ_MP (@lem5235268 x' y s) (@lem5235265 s x' y b h1 h2 h3)). Qed.
Lemma lem5235275 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5235276 (y : real) (_68530 : real) (s : real -> Prop) : (term92 s y _68530) = (term547 y _68530 s).
Proof. exact (@lem5235275 (real_le y _68530) (term548 _68530 s)). Qed.
Lemma lem5235282 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5235283 (y : real) (_68530 : real) (s : real -> Prop) : (term549 s y _68530) = (term550 y _68530 s).
Proof. exact (MK_COMB (@lem5235282) (@lem5235276 y _68530 s)). Qed.
Lemma lem5235289 (y : real) (_68530 : real) (s : real -> Prop) : (term547 y _68530 s) = (term547 y _68530 s).
Proof. exact (eq_refl (term547 y _68530 s)). Qed.
Lemma lem5235290 (y : real) (_68530 : real) (s : real -> Prop) : ((term92 s y _68530) = (term547 y _68530 s)) = ((term547 y _68530 s) = (term547 y _68530 s)).
Proof. exact (MK_COMB (@lem5235283 y _68530 s) (@lem5235289 y _68530 s)). Qed.
Lemma lem5235292 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5235293 (x : Prop) : (x = x) = True.
Proof. exact (@lem5235292 Prop x). Qed.
Lemma lem5235294 (y : real) (_68530 : real) (s : real -> Prop) : ((term547 y _68530 s) = (term547 y _68530 s)) = True.
Proof. exact (@lem5235293 (term547 y _68530 s)). Qed.
Lemma lem5235295 (y : real) (_68530 : real) (s : real -> Prop) : ((term92 s y _68530) = (term547 y _68530 s)) = True.
Proof. exact (TRANS (@lem5235290 y _68530 s) (@lem5235294 y _68530 s)). Qed.
Lemma lem5235296 (y : real) (_68530 : real) (s : real -> Prop) : True = ((term92 s y _68530) = (term547 y _68530 s)).
Proof. exact (SYM (@lem5235295 y _68530 s)). Qed.
Lemma lem5235297 (y : real) (_68530 : real) (s : real -> Prop) : (term92 s y _68530) = (term547 y _68530 s).
Proof. exact (EQ_MP (@lem5235296 y _68530 s) (@lem0)). Qed.
Lemma lem5235298 (_68530 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term547 y _68530 s.
Proof. exact (EQ_MP (@lem5235297 y _68530 s) (@lem5234622 _68530 s x y b h1)). Qed.
Lemma lem5235300 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235301 (s : real -> Prop) (y : real) (_68530 : real) : (term547 y _68530 s) = (term551 s y _68530).
Proof. exact (@lem5235300 (term548 _68530 s) (real_le y _68530)). Qed.
Lemma lem5235303 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5235304 (_68530 : real) (s : real -> Prop) : (term552 _68530 s) = (@IN real _68530 s).
Proof. exact (@lem5235303 (@IN real _68530 s)). Qed.
Lemma lem5235305 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5235306 (_68530 : real) (s : real -> Prop) : (term553 _68530 s) = (term554 _68530 s).
Proof. exact (MK_COMB (@lem5235305) (@lem5235304 _68530 s)). Qed.
Lemma lem5235307 (y : real) (_68530 : real) : (real_le y _68530) = (real_le y _68530).
Proof. exact (eq_refl (real_le y _68530)). Qed.
Lemma lem5235308 (s : real -> Prop) (y : real) (_68530 : real) : (term551 s y _68530) = (term80 s y _68530).
Proof. exact (MK_COMB (@lem5235306 _68530 s) (@lem5235307 y _68530)). Qed.
Lemma lem5235309 (s : real -> Prop) (y : real) (_68530 : real) : (term547 y _68530 s) = (term80 s y _68530).
Proof. exact (TRANS (@lem5235301 s y _68530) (@lem5235308 s y _68530)). Qed.
Lemma lem5235312 (_68530 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term80 s y _68530.
Proof. exact (EQ_MP (@lem5235309 s y _68530) (@lem5235298 _68530 s x y b h1)). Qed.
Lemma lem5235313 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term555 s x' y.
Proof. exact (@lem5235312 (x' y) s x y b h1). Qed.
Lemma lem5235316 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) (h4 : term295 s x y b) : term556 x' y.
Proof. exact (@lem5235313 x' s x y b h4 (@lem5235269 s x' y b h1 h2 h3)). Qed.
Lemma lem5235317 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) (h4 : term295 s x y b) : term557 x' y.
Proof. exact (fun h0 : term511 x' y => @lem5235316 x' s x y b h1 h2 h3 h4). Qed.
Lemma lem5235319 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235320 (x' : real -> real) (y : real) : (term557 x' y) = (term556 x' y).
Proof. exact (@lem5235319 (term556 x' y)). Qed.
Lemma lem5235321 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) (h4 : term295 s x y b) : term556 x' y.
Proof. exact (EQ_MP (@lem5235320 x' y) (@lem5235317 x' s x y b h1 h2 h3 h4)). Qed.
Lemma lem5235332 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5235333 (_68523 : real) (_68522 : real) : (term558 _68522 _68523) = (term467 _68523 _68522).
Proof. exact (@lem5235332 (term71 _68522 _68523) (term105 _68523 _68522)). Qed.
Lemma lem5235339 (_68523 : real) (_68522 : real) : (term559 _68523 _68522) = (term559 _68523 _68522).
Proof. exact (eq_refl (term559 _68523 _68522)). Qed.
Lemma lem5235340 (_68523 : real) (_68522 : real) : ((term467 _68523 _68522) = (term558 _68522 _68523)) = ((term467 _68523 _68522) = (term467 _68523 _68522)).
Proof. exact (MK_COMB (@lem5235339 _68523 _68522) (@lem5235333 _68523 _68522)). Qed.
Lemma lem5235342 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5235343 (x : Prop) : (x = x) = True.
Proof. exact (@lem5235342 Prop x). Qed.
Lemma lem5235344 (_68523 : real) (_68522 : real) : ((term467 _68523 _68522) = (term467 _68523 _68522)) = True.
Proof. exact (@lem5235343 (term467 _68523 _68522)). Qed.
Lemma lem5235345 (_68522 : real) (_68523 : real) : ((term467 _68523 _68522) = (term558 _68522 _68523)) = True.
Proof. exact (TRANS (@lem5235340 _68523 _68522) (@lem5235344 _68523 _68522)). Qed.
Lemma lem5235346 (_68522 : real) (_68523 : real) : True = ((term467 _68523 _68522) = (term558 _68522 _68523)).
Proof. exact (SYM (@lem5235345 _68522 _68523)). Qed.
Lemma lem5235347 (_68522 : real) (_68523 : real) : (term467 _68523 _68522) = (term558 _68522 _68523).
Proof. exact (EQ_MP (@lem5235346 _68522 _68523) (@lem0)). Qed.
Lemma lem5235348 (_68522 : real) (_68523 : real) (h1 : term35) : term558 _68522 _68523.
Proof. exact (EQ_MP (@lem5235347 _68522 _68523) (@lem5234596 _68523 _68522 h1)). Qed.
Lemma lem5235350 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235351 (_68523 : real) (_68522 : real) : (term558 _68522 _68523) = (term560 _68523 _68522).
Proof. exact (@lem5235350 (term71 _68522 _68523) (term105 _68523 _68522)). Qed.
Lemma lem5235353 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5235354 (_68522 : real) (_68523 : real) : (term450 _68522 _68523) = (real_le _68522 _68523).
Proof. exact (@lem5235353 (real_le _68522 _68523)). Qed.
Lemma lem5235355 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5235356 (_68522 : real) (_68523 : real) : (term561 _68522 _68523) = (term562 _68522 _68523).
Proof. exact (MK_COMB (@lem5235355) (@lem5235354 _68522 _68523)). Qed.
Lemma lem5235357 (_68523 : real) (_68522 : real) : (term105 _68523 _68522) = (term105 _68523 _68522).
Proof. exact (eq_refl (term105 _68523 _68522)). Qed.
Lemma lem5235358 (_68523 : real) (_68522 : real) : (term560 _68523 _68522) = (term563 _68523 _68522).
Proof. exact (MK_COMB (@lem5235356 _68522 _68523) (@lem5235357 _68523 _68522)). Qed.
Lemma lem5235359 (_68523 : real) (_68522 : real) : (term558 _68522 _68523) = (term563 _68523 _68522).
Proof. exact (TRANS (@lem5235351 _68523 _68522) (@lem5235358 _68523 _68522)). Qed.
Lemma lem5235362 (_68523 : real) (_68522 : real) (h1 : term35) : term563 _68523 _68522.
Proof. exact (EQ_MP (@lem5235359 _68523 _68522) (@lem5235348 _68522 _68523 h1)). Qed.
Lemma lem5235363 (x' : real -> real) (y : real) (h1 : term35) : term564 x' y.
Proof. exact (@lem5235362 (x' y) y h1). Qed.
Lemma lem5235366 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) (h4 : term295 s x y b) : term565 x' y.
Proof. exact (@lem5235363 x' y h1 (@lem5235321 x' s x y b h1 h2 h3 h4)). Qed.
Lemma lem5235367 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) (h4 : term295 s x y b) : term566 x' y.
Proof. exact (fun h0 : term507 x' y => @lem5235366 x' s x y b h1 h2 h3 h4). Qed.
Lemma lem5235369 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5235370 (x' : real -> real) (y : real) : (term566 x' y) = (term565 x' y).
Proof. exact (@lem5235369 (term507 x' y)). Qed.
Lemma lem5235371 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) (h4 : term295 s x y b) : term565 x' y.
Proof. exact (EQ_MP (@lem5235370 x' y) (@lem5235367 x' s x y b h1 h2 h3 h4)). Qed.
Lemma lem5235373 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235376 (x' : real -> real) (b : real) (_68521 : real) : (term521 b x' _68521) = (term567 x' b _68521).
Proof. exact (@lem5235373 (term507 x' _68521) (term105 b _68521)). Qed.
Lemma lem5235379 (_68521 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term567 x' b _68521.
Proof. exact (EQ_MP (@lem5235376 x' b _68521) (@lem5234658 _68521 b s x' h1)). Qed.
Lemma lem5235380 (y : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term567 x' b y.
Proof. exact (@lem5235379 y b s x' h1). Qed.
Lemma lem5235383 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) (h4 : term295 s x y b) : term105 b y.
Proof. exact (@lem5235380 y b s x' h2 (@lem5235371 x' s x y b h1 h2 h3 h4)). Qed.
Lemma lem5235384 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) (h4 : term295 s x y b) : term568 b y.
Proof. exact (fun h0 : real_lt b y => @lem5235383 x' s x y b h1 h2 h3 h4). Qed.
Lemma lem5235386 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5235387 (b : real) (y : real) : (term568 b y) = (term105 b y).
Proof. exact (@lem5235386 (real_lt b y)). Qed.
Lemma lem5235388 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) (h4 : term295 s x y b) : term105 b y.
Proof. exact (EQ_MP (@lem5235387 b y) (@lem5235384 x' s x y b h1 h2 h3 h4)). Qed.
Lemma lem5235390 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235393 (_68524 : real) (_68525 : real) : (term454 _68525 _68524) = (term569 _68524 _68525).
Proof. exact (@lem5235390 (real_lt _68525 _68524) (real_le _68524 _68525)). Qed.
Lemma lem5235396 (_68524 : real) (_68525 : real) (h1 : term35) : term569 _68524 _68525.
Proof. exact (EQ_MP (@lem5235393 _68524 _68525) (@lem5234602 _68525 _68524 h1)). Qed.
Lemma lem5235397 (y : real) (b : real) (h1 : term35) : term569 y b.
Proof. exact (@lem5235396 y b h1). Qed.
Lemma lem5235400 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 y b) (h4 : term295 s x y b) : real_le y b.
Proof. exact (@lem5235397 y b h1 (@lem5235388 x' s x y b h1 h2 h3 h4)). Qed.
Lemma lem5235401 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term295 s x y b) : term570 y b.
Proof. exact (fun h0 : term71 y b => @lem5235400 x' s x y b h1 h2 h0 h3). Qed.
Lemma lem5235403 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235404 (y : real) (b : real) : (term570 y b) = (real_le y b).
Proof. exact (@lem5235403 (real_le y b)). Qed.
Lemma lem5235405 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term295 s x y b) : real_le y b.
Proof. exact (EQ_MP (@lem5235404 y b) (@lem5235401 x' s x y b h1 h2 h3)). Qed.
Lemma lem5235408 (b : real) (y : real) (h1 : term71 b y) : term71 b y.
Proof. exact (h1). Qed.
Lemma lem5235409 (b : real) (y : real) (h1 : term71 b y) : term529 b y.
Proof. exact (fun h0 : real_le b y => @lem5235408 b y h1). Qed.
Lemma lem5235411 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5235412 (b : real) (y : real) : (term529 b y) = (term71 b y).
Proof. exact (@lem5235411 (real_le b y)). Qed.
Lemma lem5235413 (b : real) (y : real) (h1 : term71 b y) : term71 b y.
Proof. exact (EQ_MP (@lem5235412 b y) (@lem5235409 b y h1)). Qed.
Lemma lem5235415 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235418 (y : real) (x : real -> real) (_68531 : real) (s : real -> Prop) : (term518 x s _68531 y) = (term571 y x _68531 s).
Proof. exact (@lem5235415 (real_le _68531 y) (term506 x _68531 s)). Qed.
Lemma lem5235421 (_68531 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term571 y x _68531 s.
Proof. exact (EQ_MP (@lem5235418 y x _68531 s) (@lem5234628 _68531 s x y b h1)). Qed.
Lemma lem5235422 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term571 y x b s.
Proof. exact (@lem5235421 b s x y b h1). Qed.
Lemma lem5235425 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term71 b y) (h2 : term295 s x y b) : term506 x b s.
Proof. exact (@lem5235422 s x y b h2 (@lem5235413 b y h1)). Qed.
Lemma lem5235426 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term71 b y) (h2 : term295 s x y b) : term545 x b s.
Proof. exact (fun h0 : term546 x b s => @lem5235425 s x y b h1 h2). Qed.
Lemma lem5235428 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235429 (x : real -> real) (b : real) (s : real -> Prop) : (term545 x b s) = (term506 x b s).
Proof. exact (@lem5235428 (term506 x b s)). Qed.
Lemma lem5235430 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term71 b y) (h2 : term295 s x y b) : term506 x b s.
Proof. exact (EQ_MP (@lem5235429 x b s) (@lem5235426 s x y b h1 h2)). Qed.
Lemma lem5235436 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5235437 (b : real) (_68520 : real) (s : real -> Prop) : (term92 s b _68520) = (term547 b _68520 s).
Proof. exact (@lem5235436 (real_le b _68520) (term548 _68520 s)). Qed.
Lemma lem5235443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5235444 (b : real) (_68520 : real) (s : real -> Prop) : (term549 s b _68520) = (term550 b _68520 s).
Proof. exact (MK_COMB (@lem5235443) (@lem5235437 b _68520 s)). Qed.
Lemma lem5235450 (b : real) (_68520 : real) (s : real -> Prop) : (term547 b _68520 s) = (term547 b _68520 s).
Proof. exact (eq_refl (term547 b _68520 s)). Qed.
Lemma lem5235451 (b : real) (_68520 : real) (s : real -> Prop) : ((term92 s b _68520) = (term547 b _68520 s)) = ((term547 b _68520 s) = (term547 b _68520 s)).
Proof. exact (MK_COMB (@lem5235444 b _68520 s) (@lem5235450 b _68520 s)). Qed.
Lemma lem5235453 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5235454 (x : Prop) : (x = x) = True.
Proof. exact (@lem5235453 Prop x). Qed.
Lemma lem5235455 (b : real) (_68520 : real) (s : real -> Prop) : ((term547 b _68520 s) = (term547 b _68520 s)) = True.
Proof. exact (@lem5235454 (term547 b _68520 s)). Qed.
Lemma lem5235456 (b : real) (_68520 : real) (s : real -> Prop) : ((term92 s b _68520) = (term547 b _68520 s)) = True.
Proof. exact (TRANS (@lem5235451 b _68520 s) (@lem5235455 b _68520 s)). Qed.
Lemma lem5235457 (b : real) (_68520 : real) (s : real -> Prop) : True = ((term92 s b _68520) = (term547 b _68520 s)).
Proof. exact (SYM (@lem5235456 b _68520 s)). Qed.
Lemma lem5235458 (b : real) (_68520 : real) (s : real -> Prop) : (term92 s b _68520) = (term547 b _68520 s).
Proof. exact (EQ_MP (@lem5235457 b _68520 s) (@lem0)). Qed.
Lemma lem5235459 (_68520 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term547 b _68520 s.
Proof. exact (EQ_MP (@lem5235458 b _68520 s) (@lem5234590 _68520 s b h1)). Qed.
Lemma lem5235461 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235462 (s : real -> Prop) (b : real) (_68520 : real) : (term547 b _68520 s) = (term551 s b _68520).
Proof. exact (@lem5235461 (term548 _68520 s) (real_le b _68520)). Qed.
Lemma lem5235464 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5235465 (_68520 : real) (s : real -> Prop) : (term552 _68520 s) = (@IN real _68520 s).
Proof. exact (@lem5235464 (@IN real _68520 s)). Qed.
Lemma lem5235466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5235467 (_68520 : real) (s : real -> Prop) : (term553 _68520 s) = (term554 _68520 s).
Proof. exact (MK_COMB (@lem5235466) (@lem5235465 _68520 s)). Qed.
Lemma lem5235468 (b : real) (_68520 : real) : (real_le b _68520) = (real_le b _68520).
Proof. exact (eq_refl (real_le b _68520)). Qed.
Lemma lem5235469 (s : real -> Prop) (b : real) (_68520 : real) : (term551 s b _68520) = (term80 s b _68520).
Proof. exact (MK_COMB (@lem5235467 _68520 s) (@lem5235468 b _68520)). Qed.
Lemma lem5235470 (s : real -> Prop) (b : real) (_68520 : real) : (term547 b _68520 s) = (term80 s b _68520).
Proof. exact (TRANS (@lem5235462 s b _68520) (@lem5235469 s b _68520)). Qed.
Lemma lem5235473 (_68520 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term80 s b _68520.
Proof. exact (EQ_MP (@lem5235470 s b _68520) (@lem5235459 _68520 s b h1)). Qed.
Lemma lem5235474 (x : real -> real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term555 s x b.
Proof. exact (@lem5235473 (x b) s b h1). Qed.
Lemma lem5235477 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term19 s b) (h2 : term71 b y) (h3 : term295 s x y b) : term556 x b.
Proof. exact (@lem5235474 x s b h1 (@lem5235430 s x y b h2 h3)). Qed.
Lemma lem5235478 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term19 s b) (h2 : term71 b y) (h3 : term295 s x y b) : term557 x b.
Proof. exact (fun h0 : term511 x b => @lem5235477 s x y b h1 h2 h3). Qed.
Lemma lem5235480 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235481 (x : real -> real) (b : real) : (term557 x b) = (term556 x b).
Proof. exact (@lem5235480 (term556 x b)). Qed.
Lemma lem5235482 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term19 s b) (h2 : term71 b y) (h3 : term295 s x y b) : term556 x b.
Proof. exact (EQ_MP (@lem5235481 x b) (@lem5235478 s x y b h1 h2 h3)). Qed.
Lemma lem5235488 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5235489 (y : real) (x : real -> real) (_68531 : real) : (term519 x _68531 y) = (term572 y x _68531).
Proof. exact (@lem5235488 (real_le _68531 y) (term511 x _68531)). Qed.
Lemma lem5235495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5235496 (y : real) (x : real -> real) (_68531 : real) : (term573 x _68531 y) = (term574 y x _68531).
Proof. exact (MK_COMB (@lem5235495) (@lem5235489 y x _68531)). Qed.
Lemma lem5235502 (y : real) (x : real -> real) (_68531 : real) : (term572 y x _68531) = (term572 y x _68531).
Proof. exact (eq_refl (term572 y x _68531)). Qed.
Lemma lem5235503 (y : real) (x : real -> real) (_68531 : real) : ((term519 x _68531 y) = (term572 y x _68531)) = ((term572 y x _68531) = (term572 y x _68531)).
Proof. exact (MK_COMB (@lem5235496 y x _68531) (@lem5235502 y x _68531)). Qed.
Lemma lem5235505 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5235506 (x : Prop) : (x = x) = True.
Proof. exact (@lem5235505 Prop x). Qed.
Lemma lem5235507 (y : real) (x : real -> real) (_68531 : real) : ((term572 y x _68531) = (term572 y x _68531)) = True.
Proof. exact (@lem5235506 (term572 y x _68531)). Qed.
Lemma lem5235508 (y : real) (x : real -> real) (_68531 : real) : ((term519 x _68531 y) = (term572 y x _68531)) = True.
Proof. exact (TRANS (@lem5235503 y x _68531) (@lem5235507 y x _68531)). Qed.
Lemma lem5235509 (y : real) (x : real -> real) (_68531 : real) : True = ((term519 x _68531 y) = (term572 y x _68531)).
Proof. exact (SYM (@lem5235508 y x _68531)). Qed.
Lemma lem5235510 (y : real) (x : real -> real) (_68531 : real) : (term519 x _68531 y) = (term572 y x _68531).
Proof. exact (EQ_MP (@lem5235509 y x _68531) (@lem0)). Qed.
Lemma lem5235511 (_68531 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term572 y x _68531.
Proof. exact (EQ_MP (@lem5235510 y x _68531) (@lem5234634 _68531 s x y b h1)). Qed.
Lemma lem5235513 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235514 (x : real -> real) (_68531 : real) (y : real) : (term572 y x _68531) = (term575 x _68531 y).
Proof. exact (@lem5235513 (term511 x _68531) (real_le _68531 y)). Qed.
Lemma lem5235516 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5235517 (x : real -> real) (_68531 : real) : (term576 x _68531) = (term556 x _68531).
Proof. exact (@lem5235516 (term556 x _68531)). Qed.
Lemma lem5235518 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5235519 (x : real -> real) (_68531 : real) : (term577 x _68531) = (term578 x _68531).
Proof. exact (MK_COMB (@lem5235518) (@lem5235517 x _68531)). Qed.
Lemma lem5235520 (_68531 : real) (y : real) : (real_le _68531 y) = (real_le _68531 y).
Proof. exact (eq_refl (real_le _68531 y)). Qed.
Lemma lem5235521 (x : real -> real) (_68531 : real) (y : real) : (term575 x _68531 y) = (term579 x _68531 y).
Proof. exact (MK_COMB (@lem5235519 x _68531) (@lem5235520 _68531 y)). Qed.
Lemma lem5235522 (x : real -> real) (_68531 : real) (y : real) : (term572 y x _68531) = (term579 x _68531 y).
Proof. exact (TRANS (@lem5235514 x _68531 y) (@lem5235521 x _68531 y)). Qed.
Lemma lem5235525 (_68531 : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term579 x _68531 y.
Proof. exact (EQ_MP (@lem5235522 x _68531 y) (@lem5235511 _68531 s x y b h1)). Qed.
Lemma lem5235526 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term579 x b y.
Proof. exact (@lem5235525 b s x y b h1). Qed.
Lemma lem5235529 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term19 s b) (h2 : term71 b y) (h3 : term295 s x y b) : real_le b y.
Proof. exact (@lem5235526 s x y b h3 (@lem5235482 s x y b h1 h2 h3)). Qed.
Lemma lem5235530 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term19 s b) (h2 : term295 s x y b) : term570 b y.
Proof. exact (fun h0 : term71 b y => @lem5235529 s x y b h1 h0 h2). Qed.
Lemma lem5235532 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235533 (b : real) (y : real) : (term570 b y) = (real_le b y).
Proof. exact (@lem5235532 (real_le b y)). Qed.
Lemma lem5235534 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term19 s b) (h2 : term295 s x y b) : real_le b y.
Proof. exact (EQ_MP (@lem5235533 b y) (@lem5235530 s x y b h1 h2)). Qed.
Lemma lem5235550 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5235551 (_68529 : real) (_68528 : real) : (term580 _68528 _68529) = (term581 _68529 _68528).
Proof. exact (@lem5235550 (_68528 = _68529) (term71 _68529 _68528)). Qed.
Lemma lem5235559 (_68528 : real) (_68529 : real) : (term582 _68528 _68529) = (term582 _68528 _68529).
Proof. exact (eq_refl (term582 _68528 _68529)). Qed.
Lemma lem5235560 (_68529 : real) (_68528 : real) : (term517 _68528 _68529) = (term583 _68529 _68528).
Proof. exact (MK_COMB (@lem5235559 _68528 _68529) (@lem5235551 _68529 _68528)). Qed.
Lemma lem5235564 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5235565 (_68529 : real) (_68528 : real) : (term583 _68529 _68528) = (term584 _68529 _68528).
Proof. exact (@lem5235564 (_68528 = _68529) (term71 _68528 _68529) (term71 _68529 _68528)). Qed.
Lemma lem5235583 (_68529 : real) (_68528 : real) : (term517 _68528 _68529) = (term584 _68529 _68528).
Proof. exact (TRANS (@lem5235560 _68529 _68528) (@lem5235565 _68529 _68528)). Qed.
Lemma lem5235584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5235585 (_68529 : real) (_68528 : real) : (term585 _68528 _68529) = (term586 _68529 _68528).
Proof. exact (MK_COMB (@lem5235584) (@lem5235583 _68529 _68528)). Qed.
Lemma lem5235603 (_68529 : real) (_68528 : real) : (term584 _68529 _68528) = (term584 _68529 _68528).
Proof. exact (eq_refl (term584 _68529 _68528)). Qed.
Lemma lem5235604 (_68529 : real) (_68528 : real) : ((term517 _68528 _68529) = (term584 _68529 _68528)) = ((term584 _68529 _68528) = (term584 _68529 _68528)).
Proof. exact (MK_COMB (@lem5235585 _68529 _68528) (@lem5235603 _68529 _68528)). Qed.
Lemma lem5235606 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5235607 (x : Prop) : (x = x) = True.
Proof. exact (@lem5235606 Prop x). Qed.
Lemma lem5235608 (_68529 : real) (_68528 : real) : ((term584 _68529 _68528) = (term584 _68529 _68528)) = True.
Proof. exact (@lem5235607 (term584 _68529 _68528)). Qed.
Lemma lem5235609 (_68529 : real) (_68528 : real) : ((term517 _68528 _68529) = (term584 _68529 _68528)) = True.
Proof. exact (TRANS (@lem5235604 _68529 _68528) (@lem5235608 _68529 _68528)). Qed.
Lemma lem5235610 (_68529 : real) (_68528 : real) : True = ((term517 _68528 _68529) = (term584 _68529 _68528)).
Proof. exact (SYM (@lem5235609 _68529 _68528)). Qed.
Lemma lem5235611 (_68529 : real) (_68528 : real) : (term517 _68528 _68529) = (term584 _68529 _68528).
Proof. exact (EQ_MP (@lem5235610 _68529 _68528) (@lem0)). Qed.
Lemma lem5235612 (_68529 : real) (_68528 : real) (h1 : term79) : term584 _68529 _68528.
Proof. exact (EQ_MP (@lem5235611 _68529 _68528) (@lem5234614 _68528 _68529 h1)). Qed.
Lemma lem5235614 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235615 (_68528 : real) (_68529 : real) : (term584 _68529 _68528) = (term587 _68528 _68529).
Proof. exact (@lem5235614 (term391 _68529 _68528) (_68528 = _68529)). Qed.
Lemma lem5235617 (a : Prop) (b : Prop) : (term588 a b) = (term589 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5235618 (_68529 : real) (_68528 : real) : (term590 _68529 _68528) = (term591 _68529 _68528).
Proof. exact (@lem5235617 (term71 _68528 _68529) (term71 _68529 _68528)). Qed.
Lemma lem5235620 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5235621 (_68528 : real) (_68529 : real) : (term450 _68528 _68529) = (real_le _68528 _68529).
Proof. exact (@lem5235620 (real_le _68528 _68529)). Qed.
Lemma lem5235622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5235623 (_68528 : real) (_68529 : real) : (term592 _68528 _68529) = (term593 _68528 _68529).
Proof. exact (MK_COMB (@lem5235622) (@lem5235621 _68528 _68529)). Qed.
Lemma lem5235625 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5235626 (_68529 : real) (_68528 : real) : (term450 _68529 _68528) = (real_le _68529 _68528).
Proof. exact (@lem5235625 (real_le _68529 _68528)). Qed.
Lemma lem5235627 (_68529 : real) (_68528 : real) : (term591 _68529 _68528) = (term75 _68529 _68528).
Proof. exact (MK_COMB (@lem5235623 _68528 _68529) (@lem5235626 _68529 _68528)). Qed.
Lemma lem5235628 (_68529 : real) (_68528 : real) : (term590 _68529 _68528) = (term75 _68529 _68528).
Proof. exact (TRANS (@lem5235618 _68529 _68528) (@lem5235627 _68529 _68528)). Qed.
Lemma lem5235629 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5235630 (_68529 : real) (_68528 : real) : (term594 _68529 _68528) = (term595 _68529 _68528).
Proof. exact (MK_COMB (@lem5235629) (@lem5235628 _68529 _68528)). Qed.
Lemma lem5235631 (_68528 : real) (_68529 : real) : (_68528 = _68529) = (_68528 = _68529).
Proof. exact (eq_refl (_68528 = _68529)). Qed.
Lemma lem5235632 (_68528 : real) (_68529 : real) : (term587 _68528 _68529) = (term596 _68528 _68529).
Proof. exact (MK_COMB (@lem5235630 _68529 _68528) (@lem5235631 _68528 _68529)). Qed.
Lemma lem5235633 (_68528 : real) (_68529 : real) : (term584 _68529 _68528) = (term596 _68528 _68529).
Proof. exact (TRANS (@lem5235615 _68528 _68529) (@lem5235632 _68528 _68529)). Qed.
Lemma lem5235635 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term19 s b) (h3 : term139 b s x') (h4 : term295 s x y b) : term75 b y.
Proof. exact (conj (@lem5235405 x' s x y b h1 h3 h4) (@lem5235534 s x y b h2 h4)). Qed.
Lemma lem5235637 (_68528 : real) (_68529 : real) (h1 : term79) : term596 _68528 _68529.
Proof. exact (EQ_MP (@lem5235633 _68528 _68529) (@lem5235612 _68529 _68528 h1)). Qed.
Lemma lem5235638 (y : real) (b : real) (h1 : term79) : term596 y b.
Proof. exact (@lem5235637 y b h1). Qed.
Lemma lem5235641 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term295 s x y b) : y = b.
Proof. exact (@lem5235638 y b h2 (@lem5235635 x' s x y b h1 h3 h4 h5)). Qed.
Lemma lem5235642 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term295 s x y b) : term597 y b.
Proof. exact (fun h0 : term175 y b => @lem5235641 x' s x y b h1 h2 h3 h4 h5). Qed.
Lemma lem5235644 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235645 (y : real) (b : real) : (term597 y b) = (y = b).
Proof. exact (@lem5235644 (y = b)). Qed.
Lemma lem5235646 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term295 s x y b) : y = b.
Proof. exact (EQ_MP (@lem5235645 y b) (@lem5235642 x' s x y b h1 h2 h3 h4 h5)). Qed.
Lemma lem5235649 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5235651 (y : real) (b : real) : (term175 y b) = (term598 y b).
Proof. exact (@lem5235649 (y = b)). Qed.
Lemma lem5235654 (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term295 s x y b) : term598 y b.
Proof. exact (EQ_MP (@lem5235651 y b) (@lem5234616 s x y b h1)). Qed.
Lemma lem5235657 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term295 s x y b) : False.
Proof. exact (@lem5235654 s x y b h5 (@lem5235646 x' s x y b h1 h2 h3 h4 h5)). Qed.
Lemma lem5235658 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term295 s x y b) : term599.
Proof. exact (fun h0 : ~ False => @lem5235657 x' s x y b h1 h2 h3 h4 h5). Qed.
Lemma lem5235660 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235661 : term599 = False.
Proof. exact (@lem5235660 False). Qed.
Lemma lem5235662 (x' : real -> real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term295 s x y b) : False.
Proof. exact (EQ_MP (@lem5235661) (@lem5235658 x' s x y b h1 h2 h3 h4 h5)). Qed.
Lemma lem5235733 (s : real -> Prop) (y : real) (b' : real) (h1 : term144 s y b') : @IN real b' s.
Proof. exact (proj1 (@lem5234045 s y b' h1)). Qed.
Lemma lem5235734 (s : real -> Prop) (y : real) (b' : real) (h1 : term144 s y b') : term600 b' s.
Proof. exact (fun h0 : term548 b' s => @lem5235733 s y b' h1). Qed.
Lemma lem5235736 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235737 (b' : real) (s : real -> Prop) : (term600 b' s) = (@IN real b' s).
Proof. exact (@lem5235736 (@IN real b' s)). Qed.
Lemma lem5235738 (s : real -> Prop) (y : real) (b' : real) (h1 : term144 s y b') : @IN real b' s.
Proof. exact (EQ_MP (@lem5235737 b' s) (@lem5235734 s y b' h1)). Qed.
Lemma lem5235744 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5235745 (b : real) (_68532 : real) (s : real -> Prop) : (term92 s b _68532) = (term547 b _68532 s).
Proof. exact (@lem5235744 (real_le b _68532) (term548 _68532 s)). Qed.
Lemma lem5235751 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5235752 (b : real) (_68532 : real) (s : real -> Prop) : (term549 s b _68532) = (term550 b _68532 s).
Proof. exact (MK_COMB (@lem5235751) (@lem5235745 b _68532 s)). Qed.
Lemma lem5235758 (b : real) (_68532 : real) (s : real -> Prop) : (term547 b _68532 s) = (term547 b _68532 s).
Proof. exact (eq_refl (term547 b _68532 s)). Qed.
Lemma lem5235759 (b : real) (_68532 : real) (s : real -> Prop) : ((term92 s b _68532) = (term547 b _68532 s)) = ((term547 b _68532 s) = (term547 b _68532 s)).
Proof. exact (MK_COMB (@lem5235752 b _68532 s) (@lem5235758 b _68532 s)). Qed.
Lemma lem5235761 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5235762 (x : Prop) : (x = x) = True.
Proof. exact (@lem5235761 Prop x). Qed.
Lemma lem5235763 (b : real) (_68532 : real) (s : real -> Prop) : ((term547 b _68532 s) = (term547 b _68532 s)) = True.
Proof. exact (@lem5235762 (term547 b _68532 s)). Qed.
Lemma lem5235764 (b : real) (_68532 : real) (s : real -> Prop) : ((term92 s b _68532) = (term547 b _68532 s)) = True.
Proof. exact (TRANS (@lem5235759 b _68532 s) (@lem5235763 b _68532 s)). Qed.
Lemma lem5235765 (b : real) (_68532 : real) (s : real -> Prop) : True = ((term92 s b _68532) = (term547 b _68532 s)).
Proof. exact (SYM (@lem5235764 b _68532 s)). Qed.
Lemma lem5235766 (b : real) (_68532 : real) (s : real -> Prop) : (term92 s b _68532) = (term547 b _68532 s).
Proof. exact (EQ_MP (@lem5235765 b _68532 s) (@lem0)). Qed.
Lemma lem5235767 (_68532 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term547 b _68532 s.
Proof. exact (EQ_MP (@lem5235766 b _68532 s) (@lem5234810 _68532 s b h1)). Qed.
Lemma lem5235769 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235770 (s : real -> Prop) (b : real) (_68532 : real) : (term547 b _68532 s) = (term551 s b _68532).
Proof. exact (@lem5235769 (term548 _68532 s) (real_le b _68532)). Qed.
Lemma lem5235772 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5235773 (_68532 : real) (s : real -> Prop) : (term552 _68532 s) = (@IN real _68532 s).
Proof. exact (@lem5235772 (@IN real _68532 s)). Qed.
Lemma lem5235774 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5235775 (_68532 : real) (s : real -> Prop) : (term553 _68532 s) = (term554 _68532 s).
Proof. exact (MK_COMB (@lem5235774) (@lem5235773 _68532 s)). Qed.
Lemma lem5235776 (b : real) (_68532 : real) : (real_le b _68532) = (real_le b _68532).
Proof. exact (eq_refl (real_le b _68532)). Qed.
Lemma lem5235777 (s : real -> Prop) (b : real) (_68532 : real) : (term551 s b _68532) = (term80 s b _68532).
Proof. exact (MK_COMB (@lem5235775 _68532 s) (@lem5235776 b _68532)). Qed.
Lemma lem5235778 (s : real -> Prop) (b : real) (_68532 : real) : (term547 b _68532 s) = (term80 s b _68532).
Proof. exact (TRANS (@lem5235770 s b _68532) (@lem5235777 s b _68532)). Qed.
Lemma lem5235781 (_68532 : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term80 s b _68532.
Proof. exact (EQ_MP (@lem5235778 s b _68532) (@lem5235767 _68532 s b h1)). Qed.
Lemma lem5235782 (b' : real) (s : real -> Prop) (b : real) (h1 : term19 s b) : term80 s b b'.
Proof. exact (@lem5235781 b' s b h1). Qed.
Lemma lem5235785 (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term19 s b) (h2 : term144 s y b') : real_le b b'.
Proof. exact (@lem5235782 b' s b h1 (@lem5235738 s y b' h2)). Qed.
Lemma lem5235786 (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term19 s b) (h2 : term144 s y b') : term570 b b'.
Proof. exact (fun h0 : term71 b b' => @lem5235785 b s y b' h1 h2). Qed.
Lemma lem5235788 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235789 (b : real) (b' : real) : (term570 b b') = (real_le b b').
Proof. exact (@lem5235788 (real_le b b')). Qed.
Lemma lem5235790 (b : real) (s : real -> Prop) (y : real) (b' : real) (h1 : term19 s b) (h2 : term144 s y b') : real_le b b'.
Proof. exact (EQ_MP (@lem5235789 b b') (@lem5235786 b s y b' h1 h2)). Qed.
Lemma lem5235793 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5235795 (b : real) (b' : real) : (term71 b b') = (term601 b b').
Proof. exact (@lem5235793 (real_le b b')). Qed.
Lemma lem5235798 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term144 s y b') (h2 : term332 s b' y b) : term601 b b'.
Proof. exact (EQ_MP (@lem5235795 b b') (@lem5234879 s b' y b h1 h2)). Qed.
Lemma lem5235801 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term19 s b) (h2 : term144 s y b') (h3 : term332 s b' y b) : False.
Proof. exact (@lem5235798 s b' y b h2 h3 (@lem5235790 b s y b' h1 h2)). Qed.
Lemma lem5235802 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term19 s b) (h2 : term144 s y b') (h3 : term332 s b' y b) : term599.
Proof. exact (fun h0 : ~ False => @lem5235801 s b' y b h1 h2 h3). Qed.
Lemma lem5235804 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235805 : term599 = False.
Proof. exact (@lem5235804 False). Qed.
Lemma lem5235878 (b' : real) (b : real) (h1 : term71 b' b) : term71 b' b.
Proof. exact (h1). Qed.
Lemma lem5235879 (b' : real) (b : real) (h1 : term71 b' b) : term529 b' b.
Proof. exact (fun h0 : real_le b' b => @lem5235878 b' b h1). Qed.
Lemma lem5235881 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5235882 (b' : real) (b : real) : (term529 b' b) = (term71 b' b).
Proof. exact (@lem5235881 (real_le b' b)). Qed.
Lemma lem5235883 (b' : real) (b : real) (h1 : term71 b' b) : term71 b' b.
Proof. exact (EQ_MP (@lem5235882 b' b) (@lem5235879 b' b h1)). Qed.
Lemma lem5235894 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5235895 (_68547 : real) (_68546 : real) : (term531 _68546 _68547) = (term454 _68547 _68546).
Proof. exact (@lem5235894 (real_le _68546 _68547) (real_lt _68547 _68546)). Qed.
Lemma lem5235901 (_68547 : real) (_68546 : real) : (term532 _68547 _68546) = (term532 _68547 _68546).
Proof. exact (eq_refl (term532 _68547 _68546)). Qed.
Lemma lem5235902 (_68547 : real) (_68546 : real) : ((term454 _68547 _68546) = (term531 _68546 _68547)) = ((term454 _68547 _68546) = (term454 _68547 _68546)).
Proof. exact (MK_COMB (@lem5235901 _68547 _68546) (@lem5235895 _68547 _68546)). Qed.
Lemma lem5235904 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5235905 (x : Prop) : (x = x) = True.
Proof. exact (@lem5235904 Prop x). Qed.
Lemma lem5235906 (_68547 : real) (_68546 : real) : ((term454 _68547 _68546) = (term454 _68547 _68546)) = True.
Proof. exact (@lem5235905 (term454 _68547 _68546)). Qed.
Lemma lem5235907 (_68546 : real) (_68547 : real) : ((term454 _68547 _68546) = (term531 _68546 _68547)) = True.
Proof. exact (TRANS (@lem5235902 _68547 _68546) (@lem5235906 _68547 _68546)). Qed.
Lemma lem5235908 (_68546 : real) (_68547 : real) : True = ((term454 _68547 _68546) = (term531 _68546 _68547)).
Proof. exact (SYM (@lem5235907 _68546 _68547)). Qed.
Lemma lem5235909 (_68546 : real) (_68547 : real) : (term454 _68547 _68546) = (term531 _68546 _68547).
Proof. exact (EQ_MP (@lem5235908 _68546 _68547) (@lem0)). Qed.
Lemma lem5235910 (_68546 : real) (_68547 : real) (h1 : term35) : term531 _68546 _68547.
Proof. exact (EQ_MP (@lem5235909 _68546 _68547) (@lem5234991 _68547 _68546 h1)). Qed.
Lemma lem5235912 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235915 (_68547 : real) (_68546 : real) : (term531 _68546 _68547) = (term534 _68547 _68546).
Proof. exact (@lem5235912 (real_le _68546 _68547) (real_lt _68547 _68546)). Qed.
Lemma lem5235918 (_68547 : real) (_68546 : real) (h1 : term35) : term534 _68547 _68546.
Proof. exact (EQ_MP (@lem5235915 _68547 _68546) (@lem5235910 _68546 _68547 h1)). Qed.
Lemma lem5235919 (b : real) (b' : real) (h1 : term35) : term534 b b'.
Proof. exact (@lem5235918 b b' h1). Qed.
Lemma lem5235922 (b' : real) (b : real) (h1 : term35) (h2 : term71 b' b) : real_lt b b'.
Proof. exact (@lem5235919 b b' h1 (@lem5235883 b' b h2)). Qed.
Lemma lem5235923 (b' : real) (b : real) (h1 : term35) (h2 : term71 b' b) : term535 b b'.
Proof. exact (fun h0 : term105 b b' => @lem5235922 b' b h1 h2). Qed.
Lemma lem5235925 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235926 (b : real) (b' : real) : (term535 b b') = (real_lt b b').
Proof. exact (@lem5235925 (real_lt b b')). Qed.
Lemma lem5235927 (b' : real) (b : real) (h1 : term35) (h2 : term71 b' b) : real_lt b b'.
Proof. exact (EQ_MP (@lem5235926 b b') (@lem5235923 b' b h1 h2)). Qed.
Lemma lem5235933 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5235934 (x' : real -> real) (s : real -> Prop) (b : real) (_68543 : real) : (term520 b x' _68543 s) = (term537 x' s b _68543).
Proof. exact (@lem5235933 (term506 x' _68543 s) (term105 b _68543)). Qed.
Lemma lem5235940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5235941 (x' : real -> real) (s : real -> Prop) (b : real) (_68543 : real) : (term538 b x' _68543 s) = (term539 x' s b _68543).
Proof. exact (MK_COMB (@lem5235940) (@lem5235934 x' s b _68543)). Qed.
Lemma lem5235947 (x' : real -> real) (s : real -> Prop) (b : real) (_68543 : real) : (term537 x' s b _68543) = (term537 x' s b _68543).
Proof. exact (eq_refl (term537 x' s b _68543)). Qed.
Lemma lem5235948 (x' : real -> real) (s : real -> Prop) (b : real) (_68543 : real) : ((term520 b x' _68543 s) = (term537 x' s b _68543)) = ((term537 x' s b _68543) = (term537 x' s b _68543)).
Proof. exact (MK_COMB (@lem5235941 x' s b _68543) (@lem5235947 x' s b _68543)). Qed.
Lemma lem5235950 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5235951 (x : Prop) : (x = x) = True.
Proof. exact (@lem5235950 Prop x). Qed.
Lemma lem5235952 (x' : real -> real) (s : real -> Prop) (b : real) (_68543 : real) : ((term537 x' s b _68543) = (term537 x' s b _68543)) = True.
Proof. exact (@lem5235951 (term537 x' s b _68543)). Qed.
Lemma lem5235953 (x' : real -> real) (s : real -> Prop) (b : real) (_68543 : real) : ((term520 b x' _68543 s) = (term537 x' s b _68543)) = True.
Proof. exact (TRANS (@lem5235948 x' s b _68543) (@lem5235952 x' s b _68543)). Qed.
Lemma lem5235954 (x' : real -> real) (s : real -> Prop) (b : real) (_68543 : real) : True = ((term520 b x' _68543 s) = (term537 x' s b _68543)).
Proof. exact (SYM (@lem5235953 x' s b _68543)). Qed.
Lemma lem5235955 (x' : real -> real) (s : real -> Prop) (b : real) (_68543 : real) : (term520 b x' _68543 s) = (term537 x' s b _68543).
Proof. exact (EQ_MP (@lem5235954 x' s b _68543) (@lem0)). Qed.
Lemma lem5235956 (_68543 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term537 x' s b _68543.
Proof. exact (EQ_MP (@lem5235955 x' s b _68543) (@lem5235074 _68543 b s x' h1)). Qed.
Lemma lem5235958 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5235959 (b : real) (x' : real -> real) (_68543 : real) (s : real -> Prop) : (term537 x' s b _68543) = (term540 b x' _68543 s).
Proof. exact (@lem5235958 (term105 b _68543) (term506 x' _68543 s)). Qed.
Lemma lem5235961 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5235962 (b : real) (_68543 : real) : (term542 b _68543) = (real_lt b _68543).
Proof. exact (@lem5235961 (real_lt b _68543)). Qed.
Lemma lem5235963 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5235964 (b : real) (_68543 : real) : (term543 b _68543) = (term89 b _68543).
Proof. exact (MK_COMB (@lem5235963) (@lem5235962 b _68543)). Qed.
Lemma lem5235965 (x' : real -> real) (_68543 : real) (s : real -> Prop) : (term506 x' _68543 s) = (term506 x' _68543 s).
Proof. exact (eq_refl (term506 x' _68543 s)). Qed.
Lemma lem5235966 (b : real) (x' : real -> real) (_68543 : real) (s : real -> Prop) : (term540 b x' _68543 s) = (term544 b x' _68543 s).
Proof. exact (MK_COMB (@lem5235964 b _68543) (@lem5235965 x' _68543 s)). Qed.
Lemma lem5235967 (b : real) (x' : real -> real) (_68543 : real) (s : real -> Prop) : (term537 x' s b _68543) = (term544 b x' _68543 s).
Proof. exact (TRANS (@lem5235959 b x' _68543 s) (@lem5235966 b x' _68543 s)). Qed.
Lemma lem5235970 (_68543 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term544 b x' _68543 s.
Proof. exact (EQ_MP (@lem5235967 b x' _68543 s) (@lem5235956 _68543 b s x' h1)). Qed.
Lemma lem5235971 (b' : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term544 b x' b' s.
Proof. exact (@lem5235970 b' b s x' h1). Qed.
Lemma lem5235974 (s : real -> Prop) (x' : real -> real) (b' : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) : term506 x' b' s.
Proof. exact (@lem5235971 b' b s x' h2 (@lem5235927 b' b h1 h3)). Qed.
Lemma lem5235975 (s : real -> Prop) (x' : real -> real) (b' : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) : term545 x' b' s.
Proof. exact (fun h0 : term546 x' b' s => @lem5235974 s x' b' b h1 h2 h3). Qed.
Lemma lem5235977 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5235978 (x' : real -> real) (b' : real) (s : real -> Prop) : (term545 x' b' s) = (term506 x' b' s).
Proof. exact (@lem5235977 (term506 x' b' s)). Qed.
Lemma lem5235979 (s : real -> Prop) (x' : real -> real) (b' : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) : term506 x' b' s.
Proof. exact (EQ_MP (@lem5235978 x' b' s) (@lem5235975 s x' b' b h1 h2 h3)). Qed.
Lemma lem5235985 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5235986 (b' : real) (_68552 : real) (s : real -> Prop) : (term92 s b' _68552) = (term547 b' _68552 s).
Proof. exact (@lem5235985 (real_le b' _68552) (term548 _68552 s)). Qed.
Lemma lem5235992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5235993 (b' : real) (_68552 : real) (s : real -> Prop) : (term549 s b' _68552) = (term550 b' _68552 s).
Proof. exact (MK_COMB (@lem5235992) (@lem5235986 b' _68552 s)). Qed.
Lemma lem5235999 (b' : real) (_68552 : real) (s : real -> Prop) : (term547 b' _68552 s) = (term547 b' _68552 s).
Proof. exact (eq_refl (term547 b' _68552 s)). Qed.
Lemma lem5236000 (b' : real) (_68552 : real) (s : real -> Prop) : ((term92 s b' _68552) = (term547 b' _68552 s)) = ((term547 b' _68552 s) = (term547 b' _68552 s)).
Proof. exact (MK_COMB (@lem5235993 b' _68552 s) (@lem5235999 b' _68552 s)). Qed.
Lemma lem5236002 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5236003 (x : Prop) : (x = x) = True.
Proof. exact (@lem5236002 Prop x). Qed.
Lemma lem5236004 (b' : real) (_68552 : real) (s : real -> Prop) : ((term547 b' _68552 s) = (term547 b' _68552 s)) = True.
Proof. exact (@lem5236003 (term547 b' _68552 s)). Qed.
Lemma lem5236005 (b' : real) (_68552 : real) (s : real -> Prop) : ((term92 s b' _68552) = (term547 b' _68552 s)) = True.
Proof. exact (TRANS (@lem5236000 b' _68552 s) (@lem5236004 b' _68552 s)). Qed.
Lemma lem5236006 (b' : real) (_68552 : real) (s : real -> Prop) : True = ((term92 s b' _68552) = (term547 b' _68552 s)).
Proof. exact (SYM (@lem5236005 b' _68552 s)). Qed.
Lemma lem5236007 (b' : real) (_68552 : real) (s : real -> Prop) : (term92 s b' _68552) = (term547 b' _68552 s).
Proof. exact (EQ_MP (@lem5236006 b' _68552 s) (@lem0)). Qed.
Lemma lem5236008 (_68552 : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term156 s b' y) : term547 b' _68552 s.
Proof. exact (EQ_MP (@lem5236007 b' _68552 s) (@lem5235019 _68552 s b' y h1)). Qed.
Lemma lem5236010 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5236011 (s : real -> Prop) (b' : real) (_68552 : real) : (term547 b' _68552 s) = (term551 s b' _68552).
Proof. exact (@lem5236010 (term548 _68552 s) (real_le b' _68552)). Qed.
Lemma lem5236013 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5236014 (_68552 : real) (s : real -> Prop) : (term552 _68552 s) = (@IN real _68552 s).
Proof. exact (@lem5236013 (@IN real _68552 s)). Qed.
Lemma lem5236015 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5236016 (_68552 : real) (s : real -> Prop) : (term553 _68552 s) = (term554 _68552 s).
Proof. exact (MK_COMB (@lem5236015) (@lem5236014 _68552 s)). Qed.
Lemma lem5236017 (b' : real) (_68552 : real) : (real_le b' _68552) = (real_le b' _68552).
Proof. exact (eq_refl (real_le b' _68552)). Qed.
Lemma lem5236018 (s : real -> Prop) (b' : real) (_68552 : real) : (term551 s b' _68552) = (term80 s b' _68552).
Proof. exact (MK_COMB (@lem5236016 _68552 s) (@lem5236017 b' _68552)). Qed.
Lemma lem5236019 (s : real -> Prop) (b' : real) (_68552 : real) : (term547 b' _68552 s) = (term80 s b' _68552).
Proof. exact (TRANS (@lem5236011 s b' _68552) (@lem5236018 s b' _68552)). Qed.
Lemma lem5236022 (_68552 : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term156 s b' y) : term80 s b' _68552.
Proof. exact (EQ_MP (@lem5236019 s b' _68552) (@lem5236008 _68552 s b' y h1)). Qed.
Lemma lem5236023 (x' : real -> real) (s : real -> Prop) (b' : real) (y : real) (h1 : term156 s b' y) : term555 s x' b'.
Proof. exact (@lem5236022 (x' b') s b' y h1). Qed.
Lemma lem5236026 (x' : real -> real) (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) (h4 : term156 s b' y) : term556 x' b'.
Proof. exact (@lem5236023 x' s b' y h4 (@lem5235979 s x' b' b h1 h2 h3)). Qed.
Lemma lem5236027 (x' : real -> real) (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) (h4 : term156 s b' y) : term557 x' b'.
Proof. exact (fun h0 : term511 x' b' => @lem5236026 x' b s b' y h1 h2 h3 h4). Qed.
Lemma lem5236029 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5236030 (x' : real -> real) (b' : real) : (term557 x' b') = (term556 x' b').
Proof. exact (@lem5236029 (term556 x' b')). Qed.
Lemma lem5236031 (x' : real -> real) (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) (h4 : term156 s b' y) : term556 x' b'.
Proof. exact (EQ_MP (@lem5236030 x' b') (@lem5236027 x' b s b' y h1 h2 h3 h4)). Qed.
Lemma lem5236042 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5236043 (_68545 : real) (_68544 : real) : (term558 _68544 _68545) = (term467 _68545 _68544).
Proof. exact (@lem5236042 (term71 _68544 _68545) (term105 _68545 _68544)). Qed.
Lemma lem5236049 (_68545 : real) (_68544 : real) : (term559 _68545 _68544) = (term559 _68545 _68544).
Proof. exact (eq_refl (term559 _68545 _68544)). Qed.
Lemma lem5236050 (_68545 : real) (_68544 : real) : ((term467 _68545 _68544) = (term558 _68544 _68545)) = ((term467 _68545 _68544) = (term467 _68545 _68544)).
Proof. exact (MK_COMB (@lem5236049 _68545 _68544) (@lem5236043 _68545 _68544)). Qed.
Lemma lem5236052 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5236053 (x : Prop) : (x = x) = True.
Proof. exact (@lem5236052 Prop x). Qed.
Lemma lem5236054 (_68545 : real) (_68544 : real) : ((term467 _68545 _68544) = (term467 _68545 _68544)) = True.
Proof. exact (@lem5236053 (term467 _68545 _68544)). Qed.
Lemma lem5236055 (_68544 : real) (_68545 : real) : ((term467 _68545 _68544) = (term558 _68544 _68545)) = True.
Proof. exact (TRANS (@lem5236050 _68545 _68544) (@lem5236054 _68545 _68544)). Qed.
Lemma lem5236056 (_68544 : real) (_68545 : real) : True = ((term467 _68545 _68544) = (term558 _68544 _68545)).
Proof. exact (SYM (@lem5236055 _68544 _68545)). Qed.
Lemma lem5236057 (_68544 : real) (_68545 : real) : (term467 _68545 _68544) = (term558 _68544 _68545).
Proof. exact (EQ_MP (@lem5236056 _68544 _68545) (@lem0)). Qed.
Lemma lem5236058 (_68544 : real) (_68545 : real) (h1 : term35) : term558 _68544 _68545.
Proof. exact (EQ_MP (@lem5236057 _68544 _68545) (@lem5234977 _68545 _68544 h1)). Qed.
Lemma lem5236060 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5236061 (_68545 : real) (_68544 : real) : (term558 _68544 _68545) = (term560 _68545 _68544).
Proof. exact (@lem5236060 (term71 _68544 _68545) (term105 _68545 _68544)). Qed.
Lemma lem5236063 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5236064 (_68544 : real) (_68545 : real) : (term450 _68544 _68545) = (real_le _68544 _68545).
Proof. exact (@lem5236063 (real_le _68544 _68545)). Qed.
Lemma lem5236065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5236066 (_68544 : real) (_68545 : real) : (term561 _68544 _68545) = (term562 _68544 _68545).
Proof. exact (MK_COMB (@lem5236065) (@lem5236064 _68544 _68545)). Qed.
Lemma lem5236067 (_68545 : real) (_68544 : real) : (term105 _68545 _68544) = (term105 _68545 _68544).
Proof. exact (eq_refl (term105 _68545 _68544)). Qed.
Lemma lem5236068 (_68545 : real) (_68544 : real) : (term560 _68545 _68544) = (term563 _68545 _68544).
Proof. exact (MK_COMB (@lem5236066 _68544 _68545) (@lem5236067 _68545 _68544)). Qed.
Lemma lem5236069 (_68545 : real) (_68544 : real) : (term558 _68544 _68545) = (term563 _68545 _68544).
Proof. exact (TRANS (@lem5236061 _68545 _68544) (@lem5236068 _68545 _68544)). Qed.
Lemma lem5236072 (_68545 : real) (_68544 : real) (h1 : term35) : term563 _68545 _68544.
Proof. exact (EQ_MP (@lem5236069 _68545 _68544) (@lem5236058 _68544 _68545 h1)). Qed.
Lemma lem5236073 (x' : real -> real) (b' : real) (h1 : term35) : term564 x' b'.
Proof. exact (@lem5236072 (x' b') b' h1). Qed.
Lemma lem5236076 (x' : real -> real) (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) (h4 : term156 s b' y) : term565 x' b'.
Proof. exact (@lem5236073 x' b' h1 (@lem5236031 x' b s b' y h1 h2 h3 h4)). Qed.
Lemma lem5236077 (x' : real -> real) (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) (h4 : term156 s b' y) : term566 x' b'.
Proof. exact (fun h0 : term507 x' b' => @lem5236076 x' b s b' y h1 h2 h3 h4). Qed.
Lemma lem5236079 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5236080 (x' : real -> real) (b' : real) : (term566 x' b') = (term565 x' b').
Proof. exact (@lem5236079 (term507 x' b')). Qed.
Lemma lem5236081 (x' : real -> real) (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) (h4 : term156 s b' y) : term565 x' b'.
Proof. exact (EQ_MP (@lem5236080 x' b') (@lem5236077 x' b s b' y h1 h2 h3 h4)). Qed.
Lemma lem5236083 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5236086 (x' : real -> real) (b : real) (_68543 : real) : (term521 b x' _68543) = (term567 x' b _68543).
Proof. exact (@lem5236083 (term507 x' _68543) (term105 b _68543)). Qed.
Lemma lem5236089 (_68543 : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term567 x' b _68543.
Proof. exact (EQ_MP (@lem5236086 x' b _68543) (@lem5235088 _68543 b s x' h1)). Qed.
Lemma lem5236090 (b' : real) (b : real) (s : real -> Prop) (x' : real -> real) (h1 : term139 b s x') : term567 x' b b'.
Proof. exact (@lem5236089 b' b s x' h1). Qed.
Lemma lem5236093 (x' : real -> real) (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) (h4 : term156 s b' y) : term105 b b'.
Proof. exact (@lem5236090 b' b s x' h2 (@lem5236081 x' b s b' y h1 h2 h3 h4)). Qed.
Lemma lem5236094 (x' : real -> real) (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) (h4 : term156 s b' y) : term568 b b'.
Proof. exact (fun h0 : real_lt b b' => @lem5236093 x' b s b' y h1 h2 h3 h4). Qed.
Lemma lem5236096 (p : Prop) : (term530 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5236097 (b : real) (b' : real) : (term568 b b') = (term105 b b').
Proof. exact (@lem5236096 (real_lt b b')). Qed.
Lemma lem5236098 (x' : real -> real) (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) (h4 : term156 s b' y) : term105 b b'.
Proof. exact (EQ_MP (@lem5236097 b b') (@lem5236094 x' b s b' y h1 h2 h3 h4)). Qed.
Lemma lem5236100 (b : Prop) (a : Prop) : (a \/ b) = (term533 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5236103 (_68546 : real) (_68547 : real) : (term454 _68547 _68546) = (term569 _68546 _68547).
Proof. exact (@lem5236100 (real_lt _68547 _68546) (real_le _68546 _68547)). Qed.
Lemma lem5236106 (_68546 : real) (_68547 : real) (h1 : term35) : term569 _68546 _68547.
Proof. exact (EQ_MP (@lem5236103 _68546 _68547) (@lem5234991 _68547 _68546 h1)). Qed.
Lemma lem5236107 (b' : real) (b : real) (h1 : term35) : term569 b' b.
Proof. exact (@lem5236106 b' b h1). Qed.
Lemma lem5236110 (x' : real -> real) (b : real) (s : real -> Prop) (b' : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term71 b' b) (h4 : term156 s b' y) : real_le b' b.
Proof. exact (@lem5236107 b' b h1 (@lem5236098 x' b s b' y h1 h2 h3 h4)). Qed.
Lemma lem5236111 (b : real) (x' : real -> real) (s : real -> Prop) (b' : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term156 s b' y) : term570 b' b.
Proof. exact (fun h0 : term71 b' b => @lem5236110 x' b s b' y h1 h2 h0 h3). Qed.
Lemma lem5236113 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5236114 (b' : real) (b : real) : (term570 b' b) = (real_le b' b).
Proof. exact (@lem5236113 (real_le b' b)). Qed.
Lemma lem5236115 (b : real) (x' : real -> real) (s : real -> Prop) (b' : real) (y : real) (h1 : term35) (h2 : term139 b s x') (h3 : term156 s b' y) : real_le b' b.
Proof. exact (EQ_MP (@lem5236114 b' b) (@lem5236111 b x' s b' y h1 h2 h3)). Qed.
Lemma lem5236118 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5236120 (b' : real) (b : real) : (term71 b' b) = (term601 b' b).
Proof. exact (@lem5236118 (real_le b' b)). Qed.
Lemma lem5236123 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term156 s b' y) (h2 : term332 s b' y b) : term601 b' b.
Proof. exact (EQ_MP (@lem5236120 b' b) (@lem5235032 s b' y b h1 h2)). Qed.
Lemma lem5236126 (x' : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term156 s b' y) (h4 : term332 s b' y b) : False.
Proof. exact (@lem5236123 s b' y b h3 h4 (@lem5236115 b x' s b' y h1 h2 h3)). Qed.
Lemma lem5236127 (x' : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term156 s b' y) (h4 : term332 s b' y b) : term599.
Proof. exact (fun h0 : ~ False => @lem5236126 x' s b' y b h1 h2 h3 h4). Qed.
Lemma lem5236129 (p : Prop) : (term536 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5236130 : term599 = False.
Proof. exact (@lem5236129 False). Qed.
Lemma lem5236132 (x' : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term139 b s x') (h3 : term156 s b' y) (h4 : term332 s b' y b) : False.
Proof. exact (EQ_MP (@lem5236130) (@lem5236127 x' s b' y b h1 h2 h3 h4)). Qed.
Lemma lem5236133 (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term19 s b) (h2 : term144 s y b') (h3 : term332 s b' y b) : False.
Proof. exact (EQ_MP (@lem5235805) (@lem5235802 s b' y b h1 h2 h3)). Qed.
Lemma lem5236134 (x' : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term19 s b) (h3 : term139 b s x') (h4 : term332 s b' y b) : False.
Proof. exact (or_elim (@lem5234044 s b' y b h4) (fun h0 : term144 s y b' => @lem5236133 s b' y b h2 h0 h4) (fun h0 : term156 s b' y => @lem5236132 x' s b' y b h1 h3 h0 h4)). Qed.
Lemma lem5236135 (x' : real -> real) (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term382 x s b' y b) : False.
Proof. exact (or_elim (@lem5234001 x s b' y b h5) (fun h0 : term295 s x y b => @lem5235662 x' s x y b h1 h2 h3 h4 h0) (fun h0 : term332 s b' y b => @lem5236134 x' s b' y b h1 h3 h4 h0)). Qed.
Lemma lem5236136 (x' : real -> real) (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term382 x s b' y b) : (term139 b s x') = False.
Proof. exact (prop_ext (fun h6 : term139 b s x' => @lem5236135 x' x s b' y b h1 h2 h3 h4 h5) (fun h6 : False => @lem5234032 b s x' h4)). Qed.
Lemma lem5236137 (x' : real -> real) (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term382 x s b' y b) : False.
Proof. exact (EQ_MP (@lem5236136 x' x s b' y b h1 h2 h3 h4 h5) (@lem5234032 b s x' h4)). Qed.
Lemma lem5236138 (x' : real -> real) (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term382 x s b' y b) : (term382 x s b' y b) = False.
Proof. exact (prop_ext (fun h6 : term382 x s b' y b => @lem5236137 x' x s b' y b h1 h2 h3 h4 h5) (fun h6 : False => @lem5234001 x s b' y b h5)). Qed.
Lemma lem5236139 (x' : real -> real) (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term139 b s x') (h5 : term382 x s b' y b) : False.
Proof. exact (EQ_MP (@lem5236138 x' x s b' y b h1 h2 h3 h4 h5) (@lem5234001 x s b' y b h5)). Qed.
Lemma lem5236140 (x : real -> real) (s : real -> Prop) (b' : real) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term18 b s) (h5 : term382 x s b' y b) : False.
Proof. exact (ex_elim (@lem5232368 b s h4) (fun x' : real -> real => fun h0 : term141 b s x' => @lem5236139 x' x s b' y b h1 h2 h3 h0 h5)). Qed.
Lemma lem5236141 (x : real -> real) (s : real -> Prop) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term18 b s) (h5 : term385 x s y b) : False.
Proof. exact (ex_elim (@lem5233751 x s y b h5) (fun b' : real => fun h0 : term384 x s y b b' => @lem5236140 x s b' y b h1 h2 h3 h4 h0)). Qed.
Lemma lem5236142 (s : real -> Prop) (y : real) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term18 b s) (h5 : term387 s y b) : False.
Proof. exact (ex_elim (@lem5233750 s y b h5) (fun x : real -> real => fun h0 : term386 s y b x => @lem5236141 x s y b h1 h2 h3 h4 h0)). Qed.
Lemma lem5236143 (s : real -> Prop) (b : real) (h1 : term35) (h2 : term79) (h3 : term19 s b) (h4 : term18 b s) (h5 : term62 s b) : False.
Proof. exact (ex_elim (@lem5233163 s b h5) (fun y : real => fun h0 : term388 s b y => @lem5236142 s y b h1 h2 h3 h4 h0)). Qed.
Lemma lem5236144 (s : real -> Prop) (b : real) (h1 : term79) (h2 : term19 s b) (h3 : term18 b s) (h4 : term62 s b) : term33.
Proof. exact (fun h0 : term35 => @lem5236143 s b h0 h1 h2 h3 h4). Qed.
Lemma lem5236145 : term33 = term34.
Proof. exact (@lem69 term35). Qed.
Lemma lem5236146 (s : real -> Prop) (b : real) (h1 : term79) (h2 : term19 s b) (h3 : term18 b s) (h4 : term62 s b) : term34.
Proof. exact (EQ_MP (@lem5236145) (@lem5236144 s b h1 h2 h3 h4)). Qed.
Lemma lem5236147 (s : real -> Prop) (b : real) (h1 : term19 s b) (h2 : term18 b s) (h3 : term62 s b) : term38.
Proof. exact (fun h0 : term79 => @lem5236146 s b h0 h1 h2 h3). Qed.
Lemma lem5236148 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : term64 s b.
Proof. exact (fun h0 : term62 s b => @lem5236147 s b h1 h2 h0). Qed.
Lemma lem5236149 (s : real -> Prop) (b : real) (h1 : term19 s b) : term65 s b.
Proof. exact (fun h0 : term18 b s => @lem5236148 b s h1 h0). Qed.
Lemma lem5236150 (s : real -> Prop) (b : real) : term66 s b.
Proof. exact (fun h0 : term19 s b => @lem5236149 s b h0). Qed.
Lemma lem5236155 (b : real) : term68 b.
Proof. exact (fun s : real -> Prop => @lem5236150 s b). Qed.
Lemma lem5236160 : term70.
Proof. exact (fun b : real => @lem5236155 b). Qed.
Lemma lem5236161 : term53.
Proof. exact (EQ_MP (@lem5232129) (@lem5236160)). Qed.
Lemma lem5236162 (b : real) : term602 b.
Proof. exact (@lem5236161 b). Qed.
Lemma lem5236163 (b : real) : (term602 b) = (term49 b).
Proof. exact (eq_refl (term602 b)). Qed.
Lemma lem5236164 (b : real) : term49 b.
Proof. exact (EQ_MP (@lem5236163 b) (@lem5236162 b)). Qed.
Lemma lem5236165 (b : real) (s : real -> Prop) : term603 b s.
Proof. exact (@lem5236164 b s). Qed.
Lemma lem5236166 (s : real -> Prop) (b : real) : (term603 b s) = (term29 s b).
Proof. exact (eq_refl (term603 b s)). Qed.
Lemma lem5236167 (s : real -> Prop) (b : real) : term29 s b.
Proof. exact (EQ_MP (@lem5236166 s b) (@lem5236165 b s)). Qed.
Lemma lem5236169 (s : real -> Prop) (b : real) : term29 s b.
Proof. exact (@lem5231737 s b (@lem5236167 s b)). Qed.
Lemma lem5236170 (s : real -> Prop) (b : real) (h1 : term19 s b) : term43 s b.
Proof. exact (@lem5236169 s b (@lem5231682 s b h1)). Qed.
Lemma lem5236171 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : term40 s b.
Proof. exact (@lem5236170 s b h1 (@lem5231681 b s h2)). Qed.
Lemma lem5236172 (s : real -> Prop) (b : real) (h1 : term19 s b) (h2 : term18 b s) (h3 : term28 s b) : term37.
Proof. exact (@lem5236171 b s h1 h2 (@lem5231722 s b h3)). Qed.
Lemma lem5236173 (s : real -> Prop) (b : real) (h1 : term19 s b) (h2 : term18 b s) (h3 : term28 s b) : term33.
Proof. exact (@lem5236172 s b h1 h2 h3 (@lem1339379)). Qed.
Lemma lem5236174 (s : real -> Prop) (b : real) (h1 : term19 s b) (h2 : term18 b s) (h3 : term28 s b) : False.
Proof. exact (@lem5236173 s b h1 h2 h3 (@lem1495933)). Qed.
Lemma lem5236175 (s : real -> Prop) (b : real) (h1 : term19 s b) (h2 : term18 b s) (h3 : term28 s b) : (term28 s b) = False.
Proof. exact (prop_ext (fun h4 : term28 s b => @lem5236174 s b h1 h2 h3) (fun h4 : False => @lem5231722 s b h3)). Qed.
Lemma lem5236176 (s : real -> Prop) (b : real) (h1 : term19 s b) (h2 : term18 b s) (h3 : term28 s b) : False.
Proof. exact (EQ_MP (@lem5236175 s b h1 h2 h3) (@lem5231722 s b h3)). Qed.
Lemma lem5236177 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : term27 s b.
Proof. exact (fun h0 : term28 s b => @lem5236176 s b h1 h2 h0). Qed.
Lemma lem5236178 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : term26 s b.
Proof. exact (EQ_MP (@lem5231721 s b) (@lem5236177 b s h1 h2)). Qed.
Lemma lem5236179 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : (term16 s) = b.
Proof. exact (@lem5231717 s b (@lem5236178 b s h1 h2)). Qed.
Lemma lem5236180 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : (inf s) = b.
Proof. exact (EQ_MP (@lem5231713 s b) (@lem5236179 b s h1 h2)). Qed.
Lemma lem5236181 (b : real) (s : real -> Prop) (h1 : term17 b s) : term18 b s.
Proof. exact (proj2 (@lem5231680 b s h1)). Qed.
Lemma lem5236182 (b : real) (s : real -> Prop) (h1 : term17 b s) : term19 s b.
Proof. exact (proj1 (@lem5231680 b s h1)). Qed.
Lemma lem5236183 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : (term18 b s) = ((inf s) = b).
Proof. exact (prop_ext (fun h3 : term18 b s => @lem5236180 b s h1 h2) (fun h3 : (inf s) = b => @lem5231681 b s h2)). Qed.
Lemma lem5236184 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : (inf s) = b.
Proof. exact (EQ_MP (@lem5236183 b s h1 h2) (@lem5231681 b s h2)). Qed.
Lemma lem5236185 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : (term19 s b) = ((inf s) = b).
Proof. exact (prop_ext (fun h3 : term19 s b => @lem5236184 b s h1 h2) (fun h3 : (inf s) = b => @lem5231682 s b h1)). Qed.
Lemma lem5236186 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term18 b s) : (inf s) = b.
Proof. exact (EQ_MP (@lem5236185 b s h1 h2) (@lem5231682 s b h1)). Qed.
Lemma lem5236187 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term17 b s) : (term18 b s) = ((inf s) = b).
Proof. exact (prop_ext (fun h3 : term18 b s => @lem5236186 b s h1 h3) (fun h3 : (inf s) = b => @lem5236181 b s h2)). Qed.
Lemma lem5236188 (b : real) (s : real -> Prop) (h1 : term19 s b) (h2 : term17 b s) : (inf s) = b.
Proof. exact (EQ_MP (@lem5236187 b s h1 h2) (@lem5236181 b s h2)). Qed.
Lemma lem5236189 (b : real) (s : real -> Prop) (h1 : term17 b s) : (term19 s b) = ((inf s) = b).
Proof. exact (prop_ext (fun h2 : term19 s b => @lem5236188 b s h2 h1) (fun h2 : (inf s) = b => @lem5236182 b s h1)). Qed.
Lemma lem5236190 (b : real) (s : real -> Prop) (h1 : term17 b s) : (inf s) = b.
Proof. exact (EQ_MP (@lem5236189 b s h1) (@lem5236182 b s h1)). Qed.
Lemma lem5236191 (s : real -> Prop) (b : real) : term604 s b.
Proof. exact (fun h0 : term17 b s => @lem5236190 b s h0). Qed.
Lemma lem5236196 (s : real -> Prop) : term605 s.
Proof. exact (fun b : real => @lem5236191 s b). Qed.
Lemma lem5236201 : term606.
Proof. exact (fun s : real -> Prop => @lem5236196 s). Qed.
