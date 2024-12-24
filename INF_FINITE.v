Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INF_spec.
Require Import INF_FINITE_LEMMA_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339379_spec.
Require Import thm1339697_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
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
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem5217582 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5217583 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5217584 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5217583 t1) (@lem5217582 t1)). Qed.
Lemma lem5217585 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5217584 t1 t2). Qed.
Lemma lem5217586 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5217587 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5217586 t1 t2) (@lem5217585 t1 t2)). Qed.
Lemma lem5217588 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5217587 t1 t2 t3). Qed.
Lemma lem5217589 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5217590 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5217589 t1 t2 t3) (@lem5217588 t1 t2 t3)). Qed.
Lemma lem5217591 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5217590 t1 t2 t3)). Qed.
Lemma lem5217592 (s : real -> Prop) : term7 s.
Proof. exact (@lem5217581 s). Qed.
Lemma lem5217593 (s : real -> Prop) : (term7 s) = (term8 s).
Proof. exact (eq_refl (term7 s)). Qed.
Lemma lem5217595 (s : real -> Prop) (h1 : term9 s) : term9 s.
Proof. exact (h1). Qed.
Lemma lem5217597 (s : real -> Prop) : term8 s.
Proof. exact (EQ_MP (@lem5217593 s) (@lem5217592 s)). Qed.
Lemma lem5217598 (s : real -> Prop) (h1 : term9 s) : term10 s.
Proof. exact (@lem5217597 s (@lem5217595 s h1)). Qed.
Lemma lem5217600 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5217601 (s : real -> Prop) : (term12 s) = (term13 s).
Proof. exact (@lem5217600 (term12 s)). Qed.
Lemma lem5217602 (s : real -> Prop) : (term13 s) = (term12 s).
Proof. exact (SYM (@lem5217601 s)). Qed.
Lemma lem5217603 (s : real -> Prop) (h1 : term14 s) : term14 s.
Proof. exact (h1). Qed.
Lemma lem5217606 (s : real -> Prop) (h1 : term15 s) : term15 s.
Proof. exact (h1). Qed.
Lemma lem5217607 (s : real -> Prop) : term16 s.
Proof. exact (fun h0 : term15 s => @lem5217606 s h0). Qed.
Lemma lem5217608 (s : real -> Prop) (h1 : term16 s) : term16 s.
Proof. exact (h1). Qed.
Lemma lem5217609 (s : real -> Prop) (h1 : term15 s) : term15 s.
Proof. exact (h1). Qed.
Lemma lem5217610 (s : real -> Prop) (h1 : term15 s) (h2 : term16 s) : term15 s.
Proof. exact (@lem5217608 s h2 (@lem5217609 s h1)). Qed.
Lemma lem5217611 (s : real -> Prop) (h1 : term15 s) : term17 s.
Proof. exact (fun h0 : term16 s => @lem5217610 s h1 h0). Qed.
Lemma lem5217612 (s : real -> Prop) (h1 : term16 s) : term16 s.
Proof. exact (h1). Qed.
Lemma lem5217613 (s : real -> Prop) (h1 : term15 s) (h2 : term16 s) : term15 s.
Proof. exact (@lem5217611 s h1 (@lem5217612 s h2)). Qed.
Lemma lem5217614 (s : real -> Prop) (h1 : term16 s) : term16 s.
Proof. exact (fun h0 : term15 s => @lem5217613 s h0 h1). Qed.
Lemma lem5217615 (s : real -> Prop) : term18 s.
Proof. exact (fun h0 : term16 s => @lem5217614 s h0). Qed.
Lemma lem5217618 (s : real -> Prop) : term16 s.
Proof. exact (@lem5217615 s (@lem5217607 s)). Qed.
Lemma lem5217792 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5217793 : term19 = term20.
Proof. exact (@lem5217792 term21). Qed.
Lemma lem5217804 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem5217805 : term23 = term24.
Proof. exact (MK_COMB (@lem5217804) (@lem5217793)). Qed.
Lemma lem5217808 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem5217809 : term26 = term27.
Proof. exact (MK_COMB (@lem5217808) (@lem5217805)). Qed.
Lemma lem5217812 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5217813 (s : real -> Prop) : (term29 s) = (term30 s).
Proof. exact (MK_COMB (@lem5217812 s) (@lem5217809)). Qed.
Lemma lem5217816 (s : real -> Prop) : (term31 s) = (term31 s).
Proof. exact (eq_refl (term31 s)). Qed.
Lemma lem5217817 (s : real -> Prop) : (term15 s) = (term32 s).
Proof. exact (MK_COMB (@lem5217816 s) (@lem5217813 s)). Qed.
Lemma lem5217820 : term33 = term34.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5217817 s)). Qed.
Lemma lem5217821 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5217830 : term35 = term36.
Proof. exact (MK_COMB (@lem5217821) (@lem5217820)). Qed.
Lemma lem5217839 (x : real) (y : real) : ((term37 y x) = (x = y)) = ((term37 y x) = (x = y)).
Proof. exact (eq_refl ((term37 y x) = (x = y))). Qed.
Lemma lem5217840 (x : real) : (term38 x) = (term38 x).
Proof. exact (fun_ext (fun y : real => @lem5217839 x y)). Qed.
Lemma lem5217841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5217842 (x : real) : (term39 x) = (term39 x).
Proof. exact (MK_COMB (@lem5217841) (@lem5217840 x)). Qed.
Lemma lem5217843 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem5217842 x)). Qed.
Lemma lem5217844 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5217845 : term21 = term21.
Proof. exact (MK_COMB (@lem5217844) (@lem5217843)). Qed.
Lemma lem5217846 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5217847 : term20 = term20.
Proof. exact (MK_COMB (@lem5217846) (@lem5217845)). Qed.
Lemma lem5217852 (y : real) (x : real) : (term41 y x) = (term41 y x).
Proof. exact (eq_refl (term41 y x)). Qed.
Lemma lem5217853 (x : real) : (term42 x) = (term42 x).
Proof. exact (fun_ext (fun y : real => @lem5217852 y x)). Qed.
Lemma lem5217854 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5217855 (x : real) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem5217854) (@lem5217853 x)). Qed.
Lemma lem5217856 : term44 = term44.
Proof. exact (fun_ext (fun x : real => @lem5217855 x)). Qed.
Lemma lem5217857 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5217858 : term45 = term45.
Proof. exact (MK_COMB (@lem5217857) (@lem5217856)). Qed.
Lemma lem5217859 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5217860 : term22 = term22.
Proof. exact (MK_COMB (@lem5217859) (@lem5217858)). Qed.
Lemma lem5217861 : term24 = term24.
Proof. exact (MK_COMB (@lem5217860) (@lem5217847)). Qed.
Lemma lem5217862 (b : real) (s : real -> Prop) : (term46 b s) = (term46 b s).
Proof. exact (eq_refl (term46 b s)). Qed.
Lemma lem5217867 (s : real -> Prop) (b : real) (x : real) : (term47 s b x) = (term47 s b x).
Proof. exact (eq_refl (term47 s b x)). Qed.
Lemma lem5217868 (s : real -> Prop) (b : real) : (term48 s b) = (term48 s b).
Proof. exact (fun_ext (fun x : real => @lem5217867 s b x)). Qed.
Lemma lem5217869 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5217870 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (MK_COMB (@lem5217869) (@lem5217868 s b)). Qed.
Lemma lem5217871 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5217872 (s : real -> Prop) (b : real) : (term50 s b) = (term50 s b).
Proof. exact (MK_COMB (@lem5217871) (@lem5217870 s b)). Qed.
Lemma lem5217873 (b : real) (s : real -> Prop) : (term51 b s) = (term51 b s).
Proof. exact (MK_COMB (@lem5217872 s b) (@lem5217862 b s)). Qed.
Lemma lem5217874 (s : real -> Prop) : (term52 s) = (term52 s).
Proof. exact (fun_ext (fun b : real => @lem5217873 b s)). Qed.
Lemma lem5217875 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5217876 (s : real -> Prop) : (term53 s) = (term53 s).
Proof. exact (MK_COMB (@lem5217875) (@lem5217874 s)). Qed.
Lemma lem5217881 (s : real -> Prop) (x : real) : (term54 s x) = (term54 s x).
Proof. exact (eq_refl (term54 s x)). Qed.
Lemma lem5217882 (s : real -> Prop) : (term55 s) = (term55 s).
Proof. exact (fun_ext (fun x : real => @lem5217881 s x)). Qed.
Lemma lem5217883 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5217884 (s : real -> Prop) : (term56 s) = (term56 s).
Proof. exact (MK_COMB (@lem5217883) (@lem5217882 s)). Qed.
Lemma lem5217885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5217886 (s : real -> Prop) : (term57 s) = (term57 s).
Proof. exact (MK_COMB (@lem5217885) (@lem5217884 s)). Qed.
Lemma lem5217887 (s : real -> Prop) : (term58 s) = (term58 s).
Proof. exact (MK_COMB (@lem5217886 s) (@lem5217876 s)). Qed.
Lemma lem5217892 (s : real -> Prop) (b : real) (x : real) : (term47 s b x) = (term47 s b x).
Proof. exact (eq_refl (term47 s b x)). Qed.
Lemma lem5217893 (s : real -> Prop) (b : real) : (term48 s b) = (term48 s b).
Proof. exact (fun_ext (fun x : real => @lem5217892 s b x)). Qed.
Lemma lem5217894 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5217895 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (MK_COMB (@lem5217894) (@lem5217893 s b)). Qed.
Lemma lem5217896 (s : real -> Prop) : (term59 s) = (term59 s).
Proof. exact (fun_ext (fun b : real => @lem5217895 s b)). Qed.
Lemma lem5217897 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5217898 (s : real -> Prop) : (term60 s) = (term60 s).
Proof. exact (MK_COMB (@lem5217897) (@lem5217896 s)). Qed.
Lemma lem5217903 (s : real -> Prop) : (term61 s) = (term61 s).
Proof. exact (eq_refl (term61 s)). Qed.
Lemma lem5217904 (s : real -> Prop) : (term62 s) = (term62 s).
Proof. exact (MK_COMB (@lem5217903 s) (@lem5217898 s)). Qed.
Lemma lem5217905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5217906 (s : real -> Prop) : (term63 s) = (term63 s).
Proof. exact (MK_COMB (@lem5217905) (@lem5217904 s)). Qed.
Lemma lem5217907 (s : real -> Prop) : (term64 s) = (term64 s).
Proof. exact (MK_COMB (@lem5217906 s) (@lem5217887 s)). Qed.
Lemma lem5217908 : term65 = term65.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5217907 s)). Qed.
Lemma lem5217909 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5217910 : term66 = term66.
Proof. exact (MK_COMB (@lem5217909) (@lem5217908)). Qed.
Lemma lem5217911 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5217912 : term25 = term25.
Proof. exact (MK_COMB (@lem5217911) (@lem5217910)). Qed.
Lemma lem5217913 : term27 = term27.
Proof. exact (MK_COMB (@lem5217912) (@lem5217861)). Qed.
Lemma lem5217918 (s : real -> Prop) (x : real) : (term54 s x) = (term54 s x).
Proof. exact (eq_refl (term54 s x)). Qed.
Lemma lem5217919 (s : real -> Prop) : (term55 s) = (term55 s).
Proof. exact (fun_ext (fun x : real => @lem5217918 s x)). Qed.
Lemma lem5217920 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5217921 (s : real -> Prop) : (term56 s) = (term56 s).
Proof. exact (MK_COMB (@lem5217920) (@lem5217919 s)). Qed.
Lemma lem5217924 (s : real -> Prop) : (term67 s) = (term67 s).
Proof. exact (eq_refl (term67 s)). Qed.
Lemma lem5217925 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (MK_COMB (@lem5217924 s) (@lem5217921 s)). Qed.
Lemma lem5217930 (s : real -> Prop) (b : real) (x : real) : (term47 s b x) = (term47 s b x).
Proof. exact (eq_refl (term47 s b x)). Qed.
Lemma lem5217931 (s : real -> Prop) (b : real) : (term48 s b) = (term48 s b).
Proof. exact (fun_ext (fun x : real => @lem5217930 s b x)). Qed.
Lemma lem5217932 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5217933 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (MK_COMB (@lem5217932) (@lem5217931 s b)). Qed.
Lemma lem5217936 (b : real) (s : real -> Prop) : (term69 b s) = (term69 b s).
Proof. exact (eq_refl (term69 b s)). Qed.
Lemma lem5217937 (s : real -> Prop) (b : real) : (term70 s b) = (term70 s b).
Proof. exact (MK_COMB (@lem5217936 b s) (@lem5217933 s b)). Qed.
Lemma lem5217938 (s : real -> Prop) : (term71 s) = (term71 s).
Proof. exact (fun_ext (fun b : real => @lem5217937 s b)). Qed.
Lemma lem5217939 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5217940 (s : real -> Prop) : (term10 s) = (term10 s).
Proof. exact (MK_COMB (@lem5217939) (@lem5217938 s)). Qed.
Lemma lem5217941 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5217942 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (MK_COMB (@lem5217941) (@lem5217940 s)). Qed.
Lemma lem5217943 (s : real -> Prop) : (term12 s) = (term12 s).
Proof. exact (MK_COMB (@lem5217942 s) (@lem5217925 s)). Qed.
Lemma lem5217944 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5217945 (s : real -> Prop) : (term14 s) = (term14 s).
Proof. exact (MK_COMB (@lem5217944) (@lem5217943 s)). Qed.
Lemma lem5217946 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5217947 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (MK_COMB (@lem5217946) (@lem5217945 s)). Qed.
Lemma lem5217948 (s : real -> Prop) : (term30 s) = (term30 s).
Proof. exact (MK_COMB (@lem5217947 s) (@lem5217913)). Qed.
Lemma lem5217957 (s : real -> Prop) : (term31 s) = (term31 s).
Proof. exact (eq_refl (term31 s)). Qed.
Lemma lem5217958 (s : real -> Prop) : (term32 s) = (term32 s).
Proof. exact (MK_COMB (@lem5217957 s) (@lem5217948 s)). Qed.
Lemma lem5217959 : term34 = term34.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5217958 s)). Qed.
Lemma lem5217960 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5217961 : term36 = term36.
Proof. exact (MK_COMB (@lem5217960) (@lem5217959)). Qed.
Lemma lem5218086 : term35 = term36.
Proof. exact (TRANS (@lem5217830) (@lem5217961)). Qed.
Lemma lem5218087 : term36 = term35.
Proof. exact (SYM (@lem5218086)). Qed.
Lemma lem5218089 (s : real -> Prop) (h1 : term14 s) : term14 s.
Proof. exact (h1). Qed.
Lemma lem5218090 (h1 : term66) : term66.
Proof. exact (h1). Qed.
Lemma lem5218092 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem5218102 (s : real -> Prop) (h1 : term9 s) : term9 s.
Proof. exact (h1). Qed.
Lemma lem5218110 (s : real -> Prop) (b : real) (x : real) : (term47 s b x) = (term73 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5218111 (s : real -> Prop) (b : real) : (term48 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5218110 s b x)). Qed.
Lemma lem5218112 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5218113 (s : real -> Prop) (b : real) : (term49 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5218112) (@lem5218111 s b)). Qed.
Lemma lem5218115 (b : real) (s : real -> Prop) : (term69 b s) = (term69 b s).
Proof. exact (eq_refl (term69 b s)). Qed.
Lemma lem5218116 (s : real -> Prop) (b : real) : (term70 s b) = (term76 s b).
Proof. exact (MK_COMB (@lem5218115 b s) (@lem5218113 s b)). Qed.
Lemma lem5218117 (s : real -> Prop) : (term71 s) = (term77 s).
Proof. exact (fun_ext (fun b : real => @lem5218116 s b)). Qed.
Lemma lem5218118 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218119 (s : real -> Prop) : (term10 s) = (term78 s).
Proof. exact (MK_COMB (@lem5218118) (@lem5218117 s)). Qed.
Lemma lem5218127 (s : real -> Prop) (x : real) : (term79 s x) = (term80 s x).
Proof. exact (@lem17362 (@IN real x s) (term81 s x)). Qed.
Lemma lem5218128 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5218129 (s : real -> Prop) : (term84 s) = (term85 s).
Proof. exact (@lem5218128 (term55 s)). Qed.
Lemma lem5218130 (s : real -> Prop) (x : real) : (term86 s x) = (term54 s x).
Proof. exact (eq_refl (term86 s x)). Qed.
Lemma lem5218131 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5218132 (s : real -> Prop) (x : real) : (term87 s x) = (term79 s x).
Proof. exact (MK_COMB (@lem5218131) (@lem5218130 s x)). Qed.
Lemma lem5218133 (s : real -> Prop) (x : real) : (term87 s x) = (term80 s x).
Proof. exact (TRANS (@lem5218132 s x) (@lem5218127 s x)). Qed.
Lemma lem5218134 (s : real -> Prop) : (term88 s) = (term89 s).
Proof. exact (fun_ext (fun x : real => @lem5218133 s x)). Qed.
Lemma lem5218135 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218136 (s : real -> Prop) : (term85 s) = (term90 s).
Proof. exact (MK_COMB (@lem5218135) (@lem5218134 s)). Qed.
Lemma lem5218137 (s : real -> Prop) : (term84 s) = (term90 s).
Proof. exact (TRANS (@lem5218129 s) (@lem5218136 s)). Qed.
Lemma lem5218139 (s : real -> Prop) : (term91 s) = (term91 s).
Proof. exact (eq_refl (term91 s)). Qed.
Lemma lem5218140 (s : real -> Prop) : (term92 s) = (term93 s).
Proof. exact (MK_COMB (@lem5218139 s) (@lem5218137 s)). Qed.
Lemma lem5218141 (s : real -> Prop) : (term94 s) = (term92 s).
Proof. exact (@lem17045 (term95 s) (term56 s)). Qed.
Lemma lem5218142 (s : real -> Prop) : (term94 s) = (term93 s).
Proof. exact (TRANS (@lem5218141 s) (@lem5218140 s)). Qed.
Lemma lem5218143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5218144 (s : real -> Prop) : (term96 s) = (term97 s).
Proof. exact (MK_COMB (@lem5218143) (@lem5218119 s)). Qed.
Lemma lem5218145 (s : real -> Prop) : (term98 s) = (term99 s).
Proof. exact (MK_COMB (@lem5218144 s) (@lem5218142 s)). Qed.
Lemma lem5218146 (s : real -> Prop) : (term14 s) = (term98 s).
Proof. exact (@lem17362 (term10 s) (term68 s)). Qed.
Lemma lem5218147 (s : real -> Prop) : (term14 s) = (term99 s).
Proof. exact (TRANS (@lem5218146 s) (@lem5218145 s)). Qed.
Lemma lem5218294 {A : Type'} (P : Prop) (Q : A -> Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5218295 (P : Prop) (Q : real -> Prop) : (term102 P Q) = (term103 P Q).
Proof. exact (@lem5218294 real P Q). Qed.
Lemma lem5218296 (s : real -> Prop) : (term104 s) = (term105 s).
Proof. exact (@lem5218295 (term106 s) (term89 s)). Qed.
Lemma lem5218297 (s : real -> Prop) (x : real) : (term107 s x) = (term80 s x).
Proof. exact (eq_refl (term107 s x)). Qed.
Lemma lem5218298 (s : real -> Prop) : (term108 s) = (term89 s).
Proof. exact (fun_ext (fun x : real => @lem5218297 s x)). Qed.
Lemma lem5218299 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218300 (s : real -> Prop) : (term109 s) = (term90 s).
Proof. exact (MK_COMB (@lem5218299) (@lem5218298 s)). Qed.
Lemma lem5218301 (s : real -> Prop) : (term91 s) = (term91 s).
Proof. exact (eq_refl (term91 s)). Qed.
Lemma lem5218302 (s : real -> Prop) : (term104 s) = (term93 s).
Proof. exact (MK_COMB (@lem5218301 s) (@lem5218300 s)). Qed.
Lemma lem5218303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5218304 (s : real -> Prop) : (term110 s) = (term111 s).
Proof. exact (MK_COMB (@lem5218303) (@lem5218302 s)). Qed.
Lemma lem5218305 (s : real -> Prop) (x : real) : (term107 s x) = (term80 s x).
Proof. exact (eq_refl (term107 s x)). Qed.
Lemma lem5218306 (s : real -> Prop) : (term91 s) = (term91 s).
Proof. exact (eq_refl (term91 s)). Qed.
Lemma lem5218307 (s : real -> Prop) (x : real) : (term112 s x) = (term113 s x).
Proof. exact (MK_COMB (@lem5218306 s) (@lem5218305 s x)). Qed.
Lemma lem5218308 (s : real -> Prop) : (term114 s) = (term115 s).
Proof. exact (fun_ext (fun x : real => @lem5218307 s x)). Qed.
Lemma lem5218309 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218310 (s : real -> Prop) : (term105 s) = (term116 s).
Proof. exact (MK_COMB (@lem5218309) (@lem5218308 s)). Qed.
Lemma lem5218311 (s : real -> Prop) : ((term104 s) = (term105 s)) = ((term93 s) = (term116 s)).
Proof. exact (MK_COMB (@lem5218304 s) (@lem5218310 s)). Qed.
Lemma lem5218312 (s : real -> Prop) : (term93 s) = (term116 s).
Proof. exact (EQ_MP (@lem5218311 s) (@lem5218296 s)). Qed.
Lemma lem5218313 (s : real -> Prop) : (term97 s) = (term97 s).
Proof. exact (eq_refl (term97 s)). Qed.
Lemma lem5218314 (s : real -> Prop) : (term99 s) = (term117 s).
Proof. exact (MK_COMB (@lem5218313 s) (@lem5218312 s)). Qed.
Lemma lem5218316 {A : Type'} (P : A -> Prop) (Q : Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5218317 (P : real -> Prop) (Q : Prop) : (term120 P Q) = (term121 P Q).
Proof. exact (@lem5218316 real P Q). Qed.
Lemma lem5218318 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (@lem5218317 (term77 s) (term116 s)). Qed.
Lemma lem5218319 (s : real -> Prop) (b : real) : (term124 s b) = (term76 s b).
Proof. exact (eq_refl (term124 s b)). Qed.
Lemma lem5218320 (s : real -> Prop) : (term125 s) = (term77 s).
Proof. exact (fun_ext (fun b : real => @lem5218319 s b)). Qed.
Lemma lem5218321 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218322 (s : real -> Prop) : (term126 s) = (term78 s).
Proof. exact (MK_COMB (@lem5218321) (@lem5218320 s)). Qed.
Lemma lem5218323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5218324 (s : real -> Prop) : (term127 s) = (term97 s).
Proof. exact (MK_COMB (@lem5218323) (@lem5218322 s)). Qed.
Lemma lem5218325 (s : real -> Prop) : (term116 s) = (term116 s).
Proof. exact (eq_refl (term116 s)). Qed.
Lemma lem5218326 (s : real -> Prop) : (term122 s) = (term117 s).
Proof. exact (MK_COMB (@lem5218324 s) (@lem5218325 s)). Qed.
Lemma lem5218327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5218328 (s : real -> Prop) : (term128 s) = (term129 s).
Proof. exact (MK_COMB (@lem5218327) (@lem5218326 s)). Qed.
Lemma lem5218329 (s : real -> Prop) (b : real) : (term124 s b) = (term76 s b).
Proof. exact (eq_refl (term124 s b)). Qed.
Lemma lem5218330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5218331 (s : real -> Prop) (b : real) : (term130 s b) = (term131 s b).
Proof. exact (MK_COMB (@lem5218330) (@lem5218329 s b)). Qed.
Lemma lem5218332 (s : real -> Prop) : (term116 s) = (term116 s).
Proof. exact (eq_refl (term116 s)). Qed.
Lemma lem5218333 (b : real) (s : real -> Prop) : (term132 b s) = (term133 b s).
Proof. exact (MK_COMB (@lem5218331 s b) (@lem5218332 s)). Qed.
Lemma lem5218334 (s : real -> Prop) : (term134 s) = (term135 s).
Proof. exact (fun_ext (fun b : real => @lem5218333 b s)). Qed.
Lemma lem5218335 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218336 (s : real -> Prop) : (term123 s) = (term136 s).
Proof. exact (MK_COMB (@lem5218335) (@lem5218334 s)). Qed.
Lemma lem5218337 (s : real -> Prop) : ((term122 s) = (term123 s)) = ((term117 s) = (term136 s)).
Proof. exact (MK_COMB (@lem5218328 s) (@lem5218336 s)). Qed.
Lemma lem5218338 (s : real -> Prop) : (term117 s) = (term136 s).
Proof. exact (EQ_MP (@lem5218337 s) (@lem5218318 s)). Qed.
Lemma lem5218340 {A : Type'} (P : Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5218341 (P : Prop) (Q : real -> Prop) : (term139 P Q) = (term140 P Q).
Proof. exact (@lem5218340 real P Q). Qed.
Lemma lem5218342 (b : real) (s : real -> Prop) : (term141 b s) = (term142 b s).
Proof. exact (@lem5218341 (term76 s b) (term115 s)). Qed.
Lemma lem5218343 (s : real -> Prop) (x : real) : (term143 s x) = (term113 s x).
Proof. exact (eq_refl (term143 s x)). Qed.
Lemma lem5218344 (s : real -> Prop) : (term144 s) = (term115 s).
Proof. exact (fun_ext (fun x : real => @lem5218343 s x)). Qed.
Lemma lem5218345 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218346 (s : real -> Prop) : (term145 s) = (term116 s).
Proof. exact (MK_COMB (@lem5218345) (@lem5218344 s)). Qed.
Lemma lem5218347 (s : real -> Prop) (b : real) : (term131 s b) = (term131 s b).
Proof. exact (eq_refl (term131 s b)). Qed.
Lemma lem5218348 (b : real) (s : real -> Prop) : (term141 b s) = (term133 b s).
Proof. exact (MK_COMB (@lem5218347 s b) (@lem5218346 s)). Qed.
Lemma lem5218349 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5218350 (b : real) (s : real -> Prop) : (term146 b s) = (term147 b s).
Proof. exact (MK_COMB (@lem5218349) (@lem5218348 b s)). Qed.
Lemma lem5218351 (s : real -> Prop) (x : real) : (term143 s x) = (term113 s x).
Proof. exact (eq_refl (term143 s x)). Qed.
Lemma lem5218352 (s : real -> Prop) (b : real) : (term131 s b) = (term131 s b).
Proof. exact (eq_refl (term131 s b)). Qed.
Lemma lem5218353 (b : real) (s : real -> Prop) (x : real) : (term148 b s x) = (term149 b s x).
Proof. exact (MK_COMB (@lem5218352 s b) (@lem5218351 s x)). Qed.
Lemma lem5218354 (b : real) (s : real -> Prop) : (term150 b s) = (term151 b s).
Proof. exact (fun_ext (fun x : real => @lem5218353 b s x)). Qed.
Lemma lem5218355 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218356 (b : real) (s : real -> Prop) : (term142 b s) = (term152 b s).
Proof. exact (MK_COMB (@lem5218355) (@lem5218354 b s)). Qed.
Lemma lem5218357 (b : real) (s : real -> Prop) : ((term141 b s) = (term142 b s)) = ((term133 b s) = (term152 b s)).
Proof. exact (MK_COMB (@lem5218350 b s) (@lem5218356 b s)). Qed.
Lemma lem5218358 (b : real) (s : real -> Prop) : (term133 b s) = (term152 b s).
Proof. exact (EQ_MP (@lem5218357 b s) (@lem5218342 b s)). Qed.
Lemma lem5218359 (s : real -> Prop) : (term135 s) = (term153 s).
Proof. exact (fun_ext (fun b : real => @lem5218358 b s)). Qed.
Lemma lem5218360 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218361 (s : real -> Prop) : (term136 s) = (term154 s).
Proof. exact (MK_COMB (@lem5218360) (@lem5218359 s)). Qed.
Lemma lem5218362 (s : real -> Prop) : (term117 s) = (term154 s).
Proof. exact (TRANS (@lem5218338 s) (@lem5218361 s)). Qed.
Lemma lem5218364 (s : real -> Prop) : (term99 s) = (term154 s).
Proof. exact (TRANS (@lem5218314 s) (@lem5218362 s)). Qed.
Lemma lem5218365 (s : real -> Prop) : (term14 s) = (term154 s).
Proof. exact (TRANS (@lem5218147 s) (@lem5218364 s)). Qed.
Lemma lem5218366 (s : real -> Prop) (h1 : term14 s) : term154 s.
Proof. exact (EQ_MP (@lem5218365 s) (@lem5218089 s h1)). Qed.
Lemma lem5218369 (s : real -> Prop) : (term155 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5218376 (s : real -> Prop) (b : real) (x : real) : (term156 s b x) = (term157 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5218377 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5218378 (s : real -> Prop) (b : real) : (term158 s b) = (term159 s b).
Proof. exact (@lem5218377 (term48 s b)). Qed.
Lemma lem5218379 (s : real -> Prop) (b : real) (x : real) : (term160 s b x) = (term47 s b x).
Proof. exact (eq_refl (term160 s b x)). Qed.
Lemma lem5218380 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5218381 (s : real -> Prop) (b : real) (x : real) : (term161 s b x) = (term156 s b x).
Proof. exact (MK_COMB (@lem5218380) (@lem5218379 s b x)). Qed.
Lemma lem5218382 (s : real -> Prop) (b : real) (x : real) : (term161 s b x) = (term157 s b x).
Proof. exact (TRANS (@lem5218381 s b x) (@lem5218376 s b x)). Qed.
Lemma lem5218383 (s : real -> Prop) (b : real) : (term162 s b) = (term163 s b).
Proof. exact (fun_ext (fun x : real => @lem5218382 s b x)). Qed.
Lemma lem5218384 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218385 (s : real -> Prop) (b : real) : (term159 s b) = (term164 s b).
Proof. exact (MK_COMB (@lem5218384) (@lem5218383 s b)). Qed.
Lemma lem5218386 (s : real -> Prop) (b : real) : (term158 s b) = (term164 s b).
Proof. exact (TRANS (@lem5218378 s b) (@lem5218385 s b)). Qed.
Lemma lem5218387 (P : real -> Prop) : (term165 P) = (term166 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5218388 (s : real -> Prop) : (term167 s) = (term168 s).
Proof. exact (@lem5218387 (term59 s)). Qed.
Lemma lem5218389 (s : real -> Prop) (b : real) : (term169 s b) = (term49 s b).
Proof. exact (eq_refl (term169 s b)). Qed.
Lemma lem5218390 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5218391 (s : real -> Prop) (b : real) : (term170 s b) = (term158 s b).
Proof. exact (MK_COMB (@lem5218390) (@lem5218389 s b)). Qed.
Lemma lem5218392 (s : real -> Prop) (b : real) : (term170 s b) = (term164 s b).
Proof. exact (TRANS (@lem5218391 s b) (@lem5218386 s b)). Qed.
Lemma lem5218393 (s : real -> Prop) : (term171 s) = (term172 s).
Proof. exact (fun_ext (fun b : real => @lem5218392 s b)). Qed.
Lemma lem5218394 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5218395 (s : real -> Prop) : (term168 s) = (term173 s).
Proof. exact (MK_COMB (@lem5218394) (@lem5218393 s)). Qed.
Lemma lem5218396 (s : real -> Prop) : (term167 s) = (term173 s).
Proof. exact (TRANS (@lem5218388 s) (@lem5218395 s)). Qed.
Lemma lem5218397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5218398 (s : real -> Prop) : (term174 s) = (term175 s).
Proof. exact (MK_COMB (@lem5218397) (@lem5218369 s)). Qed.
Lemma lem5218399 (s : real -> Prop) : (term176 s) = (term177 s).
Proof. exact (MK_COMB (@lem5218398 s) (@lem5218396 s)). Qed.
Lemma lem5218400 (s : real -> Prop) : (term178 s) = (term176 s).
Proof. exact (@lem17045 (term179 s) (term60 s)). Qed.
Lemma lem5218401 (s : real -> Prop) : (term178 s) = (term177 s).
Proof. exact (TRANS (@lem5218400 s) (@lem5218399 s)). Qed.
Lemma lem5218408 (s : real -> Prop) (x : real) : (term54 s x) = (term180 s x).
Proof. exact (@lem17265 (@IN real x s) (term81 s x)). Qed.
Lemma lem5218409 (s : real -> Prop) : (term55 s) = (term181 s).
Proof. exact (fun_ext (fun x : real => @lem5218408 s x)). Qed.
Lemma lem5218410 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5218411 (s : real -> Prop) : (term56 s) = (term182 s).
Proof. exact (MK_COMB (@lem5218410) (@lem5218409 s)). Qed.
Lemma lem5218418 (s : real -> Prop) (b : real) (x : real) : (term156 s b x) = (term157 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5218419 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5218420 (s : real -> Prop) (b : real) : (term158 s b) = (term159 s b).
Proof. exact (@lem5218419 (term48 s b)). Qed.
Lemma lem5218421 (s : real -> Prop) (b : real) (x : real) : (term160 s b x) = (term47 s b x).
Proof. exact (eq_refl (term160 s b x)). Qed.
Lemma lem5218422 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5218423 (s : real -> Prop) (b : real) (x : real) : (term161 s b x) = (term156 s b x).
Proof. exact (MK_COMB (@lem5218422) (@lem5218421 s b x)). Qed.
Lemma lem5218424 (s : real -> Prop) (b : real) (x : real) : (term161 s b x) = (term157 s b x).
Proof. exact (TRANS (@lem5218423 s b x) (@lem5218418 s b x)). Qed.
Lemma lem5218425 (s : real -> Prop) (b : real) : (term162 s b) = (term163 s b).
Proof. exact (fun_ext (fun x : real => @lem5218424 s b x)). Qed.
Lemma lem5218426 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218427 (s : real -> Prop) (b : real) : (term159 s b) = (term164 s b).
Proof. exact (MK_COMB (@lem5218426) (@lem5218425 s b)). Qed.
Lemma lem5218428 (s : real -> Prop) (b : real) : (term158 s b) = (term164 s b).
Proof. exact (TRANS (@lem5218420 s b) (@lem5218427 s b)). Qed.
Lemma lem5218429 (b : real) (s : real -> Prop) : (term46 b s) = (term46 b s).
Proof. exact (eq_refl (term46 b s)). Qed.
Lemma lem5218430 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5218431 (s : real -> Prop) (b : real) : (term183 s b) = (term184 s b).
Proof. exact (MK_COMB (@lem5218430) (@lem5218428 s b)). Qed.
Lemma lem5218432 (b : real) (s : real -> Prop) : (term185 b s) = (term186 b s).
Proof. exact (MK_COMB (@lem5218431 s b) (@lem5218429 b s)). Qed.
Lemma lem5218433 (b : real) (s : real -> Prop) : (term51 b s) = (term185 b s).
Proof. exact (@lem17265 (term49 s b) (term46 b s)). Qed.
Lemma lem5218434 (b : real) (s : real -> Prop) : (term51 b s) = (term186 b s).
Proof. exact (TRANS (@lem5218433 b s) (@lem5218432 b s)). Qed.
Lemma lem5218435 (s : real -> Prop) : (term52 s) = (term187 s).
Proof. exact (fun_ext (fun b : real => @lem5218434 b s)). Qed.
Lemma lem5218436 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5218437 (s : real -> Prop) : (term53 s) = (term188 s).
Proof. exact (MK_COMB (@lem5218436) (@lem5218435 s)). Qed.
Lemma lem5218438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5218439 (s : real -> Prop) : (term57 s) = (term189 s).
Proof. exact (MK_COMB (@lem5218438) (@lem5218411 s)). Qed.
Lemma lem5218440 (s : real -> Prop) : (term58 s) = (term190 s).
Proof. exact (MK_COMB (@lem5218439 s) (@lem5218437 s)). Qed.
Lemma lem5218441 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5218442 (s : real -> Prop) : (term191 s) = (term192 s).
Proof. exact (MK_COMB (@lem5218441) (@lem5218401 s)). Qed.
Lemma lem5218443 (s : real -> Prop) : (term193 s) = (term194 s).
Proof. exact (MK_COMB (@lem5218442 s) (@lem5218440 s)). Qed.
Lemma lem5218444 (s : real -> Prop) : (term64 s) = (term193 s).
Proof. exact (@lem17265 (term62 s) (term58 s)). Qed.
Lemma lem5218445 (s : real -> Prop) : (term64 s) = (term194 s).
Proof. exact (TRANS (@lem5218444 s) (@lem5218443 s)). Qed.
Lemma lem5218446 : term65 = term195.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5218445 s)). Qed.
Lemma lem5218447 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5218448 : term66 = term196.
Proof. exact (MK_COMB (@lem5218447) (@lem5218446)). Qed.
Lemma lem5218695 {A B : Type'} (P : type1413 A B) : (term197 A B P) = (term198 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5218696 (P : type1626) : (term199 P) = (term200 P).
Proof. exact (@lem5218695 real real P). Qed.
Lemma lem5218697 (s : real -> Prop) : (term201 s) = (term202 s).
Proof. exact (@lem5218696 (term203 s)). Qed.
Lemma lem5218698 (s : real -> Prop) (b : real) : (term204 s b) = (term163 s b).
Proof. exact (eq_refl (term204 s b)). Qed.
Lemma lem5218699 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5218700 (s : real -> Prop) (b : real) (x : real) : (term205 s b x) = (term206 s b x).
Proof. exact (MK_COMB (@lem5218698 s b) (@lem5218699 x)). Qed.
Lemma lem5218701 (s : real -> Prop) (b : real) (x : real) : (term206 s b x) = (term157 s b x).
Proof. exact (eq_refl (term206 s b x)). Qed.
Lemma lem5218702 (s : real -> Prop) (b : real) (x : real) : (term205 s b x) = (term157 s b x).
Proof. exact (TRANS (@lem5218700 s b x) (@lem5218701 s b x)). Qed.
Lemma lem5218703 (s : real -> Prop) (b : real) : (term207 s b) = (term163 s b).
Proof. exact (fun_ext (fun x : real => @lem5218702 s b x)). Qed.
Lemma lem5218704 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218705 (s : real -> Prop) (b : real) : (term208 s b) = (term164 s b).
Proof. exact (MK_COMB (@lem5218704) (@lem5218703 s b)). Qed.
Lemma lem5218706 (s : real -> Prop) : (term209 s) = (term172 s).
Proof. exact (fun_ext (fun b : real => @lem5218705 s b)). Qed.
Lemma lem5218707 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5218708 (s : real -> Prop) : (term201 s) = (term173 s).
Proof. exact (MK_COMB (@lem5218707) (@lem5218706 s)). Qed.
Lemma lem5218709 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5218710 (s : real -> Prop) : (term210 s) = (term211 s).
Proof. exact (MK_COMB (@lem5218709) (@lem5218708 s)). Qed.
Lemma lem5218711 (s : real -> Prop) (b : real) : (term204 s b) = (term163 s b).
Proof. exact (eq_refl (term204 s b)). Qed.
Lemma lem5218712 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5218713 (s : real -> Prop) (x : real -> real) (b : real) : (term212 s x b) = (term213 s x b).
Proof. exact (MK_COMB (@lem5218711 s b) (@lem5218712 x b)). Qed.
Lemma lem5218714 (s : real -> Prop) (x : real -> real) (b : real) : (term213 s x b) = (term214 s x b).
Proof. exact (eq_refl (term213 s x b)). Qed.
Lemma lem5218715 (s : real -> Prop) (x : real -> real) (b : real) : (term212 s x b) = (term214 s x b).
Proof. exact (TRANS (@lem5218713 s x b) (@lem5218714 s x b)). Qed.
Lemma lem5218716 (s : real -> Prop) (x : real -> real) : (term215 s x) = (term216 s x).
Proof. exact (fun_ext (fun b : real => @lem5218715 s x b)). Qed.
Lemma lem5218717 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5218718 (s : real -> Prop) (x : real -> real) : (term217 s x) = (term218 s x).
Proof. exact (MK_COMB (@lem5218717) (@lem5218716 s x)). Qed.
Lemma lem5218719 (s : real -> Prop) : (term219 s) = (term220 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5218718 s x)). Qed.
Lemma lem5218720 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5218721 (s : real -> Prop) : (term202 s) = (term221 s).
Proof. exact (MK_COMB (@lem5218720) (@lem5218719 s)). Qed.
Lemma lem5218722 (s : real -> Prop) : ((term201 s) = (term202 s)) = ((term173 s) = (term221 s)).
Proof. exact (MK_COMB (@lem5218710 s) (@lem5218721 s)). Qed.
Lemma lem5218723 (s : real -> Prop) : (term173 s) = (term221 s).
Proof. exact (EQ_MP (@lem5218722 s) (@lem5218697 s)). Qed.
Lemma lem5218724 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5218725 (s : real -> Prop) : (term177 s) = (term222 s).
Proof. exact (MK_COMB (@lem5218724 s) (@lem5218723 s)). Qed.
Lemma lem5218727 {A : Type'} (P : Prop) (Q : A -> Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5218728 (P : Prop) (Q : type1028) : (term223 P Q) = (term224 P Q).
Proof. exact (@lem5218727 (real -> real) P Q). Qed.
Lemma lem5218729 (s : real -> Prop) : (term225 s) = (term226 s).
Proof. exact (@lem5218728 (s = (@EMPTY real)) (term220 s)). Qed.
Lemma lem5218730 (s : real -> Prop) (x : real -> real) : (term227 s x) = (term218 s x).
Proof. exact (eq_refl (term227 s x)). Qed.
Lemma lem5218731 (s : real -> Prop) : (term228 s) = (term220 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5218730 s x)). Qed.
Lemma lem5218732 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5218733 (s : real -> Prop) : (term229 s) = (term221 s).
Proof. exact (MK_COMB (@lem5218732) (@lem5218731 s)). Qed.
Lemma lem5218734 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5218735 (s : real -> Prop) : (term225 s) = (term222 s).
Proof. exact (MK_COMB (@lem5218734 s) (@lem5218733 s)). Qed.
Lemma lem5218736 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5218737 (s : real -> Prop) : (term230 s) = (term231 s).
Proof. exact (MK_COMB (@lem5218736) (@lem5218735 s)). Qed.
Lemma lem5218738 (s : real -> Prop) (x : real -> real) : (term227 s x) = (term218 s x).
Proof. exact (eq_refl (term227 s x)). Qed.
Lemma lem5218739 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5218740 (s : real -> Prop) (x : real -> real) : (term232 s x) = (term233 s x).
Proof. exact (MK_COMB (@lem5218739 s) (@lem5218738 s x)). Qed.
Lemma lem5218741 (s : real -> Prop) : (term234 s) = (term235 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5218740 s x)). Qed.
Lemma lem5218742 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5218743 (s : real -> Prop) : (term226 s) = (term236 s).
Proof. exact (MK_COMB (@lem5218742) (@lem5218741 s)). Qed.
Lemma lem5218744 (s : real -> Prop) : ((term225 s) = (term226 s)) = ((term222 s) = (term236 s)).
Proof. exact (MK_COMB (@lem5218737 s) (@lem5218743 s)). Qed.
Lemma lem5218745 (s : real -> Prop) : (term222 s) = (term236 s).
Proof. exact (EQ_MP (@lem5218744 s) (@lem5218729 s)). Qed.
Lemma lem5218746 (s : real -> Prop) : (term177 s) = (term236 s).
Proof. exact (TRANS (@lem5218725 s) (@lem5218745 s)). Qed.
Lemma lem5218747 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5218748 (s : real -> Prop) : (term192 s) = (term237 s).
Proof. exact (MK_COMB (@lem5218747) (@lem5218746 s)). Qed.
Lemma lem5218750 {A : Type'} (P : A -> Prop) (Q : Prop) : (term238 A P Q) = (term239 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5218751 (P : real -> Prop) (Q : Prop) : (term240 P Q) = (term241 P Q).
Proof. exact (@lem5218750 real P Q). Qed.
Lemma lem5218752 (b : real) (s : real -> Prop) : (term242 b s) = (term243 b s).
Proof. exact (@lem5218751 (term163 s b) (term46 b s)). Qed.
Lemma lem5218753 (s : real -> Prop) (b : real) (x : real) : (term206 s b x) = (term157 s b x).
Proof. exact (eq_refl (term206 s b x)). Qed.
Lemma lem5218754 (s : real -> Prop) (b : real) : (term244 s b) = (term163 s b).
Proof. exact (fun_ext (fun x : real => @lem5218753 s b x)). Qed.
Lemma lem5218755 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218756 (s : real -> Prop) (b : real) : (term245 s b) = (term164 s b).
Proof. exact (MK_COMB (@lem5218755) (@lem5218754 s b)). Qed.
Lemma lem5218757 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5218758 (s : real -> Prop) (b : real) : (term246 s b) = (term184 s b).
Proof. exact (MK_COMB (@lem5218757) (@lem5218756 s b)). Qed.
Lemma lem5218759 (b : real) (s : real -> Prop) : (term46 b s) = (term46 b s).
Proof. exact (eq_refl (term46 b s)). Qed.
Lemma lem5218760 (b : real) (s : real -> Prop) : (term242 b s) = (term186 b s).
Proof. exact (MK_COMB (@lem5218758 s b) (@lem5218759 b s)). Qed.
Lemma lem5218761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5218762 (b : real) (s : real -> Prop) : (term247 b s) = (term248 b s).
Proof. exact (MK_COMB (@lem5218761) (@lem5218760 b s)). Qed.
Lemma lem5218763 (s : real -> Prop) (b : real) (x : real) : (term206 s b x) = (term157 s b x).
Proof. exact (eq_refl (term206 s b x)). Qed.
Lemma lem5218764 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5218765 (s : real -> Prop) (b : real) (x : real) : (term249 s b x) = (term250 s b x).
Proof. exact (MK_COMB (@lem5218764) (@lem5218763 s b x)). Qed.
Lemma lem5218766 (b : real) (s : real -> Prop) : (term46 b s) = (term46 b s).
Proof. exact (eq_refl (term46 b s)). Qed.
Lemma lem5218767 (x : real) (b : real) (s : real -> Prop) : (term251 x b s) = (term252 x b s).
Proof. exact (MK_COMB (@lem5218765 s b x) (@lem5218766 b s)). Qed.
Lemma lem5218768 (b : real) (s : real -> Prop) : (term253 b s) = (term254 b s).
Proof. exact (fun_ext (fun x : real => @lem5218767 x b s)). Qed.
Lemma lem5218769 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218770 (b : real) (s : real -> Prop) : (term243 b s) = (term255 b s).
Proof. exact (MK_COMB (@lem5218769) (@lem5218768 b s)). Qed.
Lemma lem5218771 (b : real) (s : real -> Prop) : ((term242 b s) = (term243 b s)) = ((term186 b s) = (term255 b s)).
Proof. exact (MK_COMB (@lem5218762 b s) (@lem5218770 b s)). Qed.
Lemma lem5218772 (b : real) (s : real -> Prop) : (term186 b s) = (term255 b s).
Proof. exact (EQ_MP (@lem5218771 b s) (@lem5218752 b s)). Qed.
Lemma lem5218773 (s : real -> Prop) : (term187 s) = (term256 s).
Proof. exact (fun_ext (fun b : real => @lem5218772 b s)). Qed.
Lemma lem5218774 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5218775 (s : real -> Prop) : (term188 s) = (term257 s).
Proof. exact (MK_COMB (@lem5218774) (@lem5218773 s)). Qed.
Lemma lem5218777 {A B : Type'} (P : type1413 A B) : (term197 A B P) = (term198 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5218778 (P : type1626) : (term199 P) = (term200 P).
Proof. exact (@lem5218777 real real P). Qed.
Lemma lem5218779 (s : real -> Prop) : (term258 s) = (term259 s).
Proof. exact (@lem5218778 (term260 s)). Qed.
Lemma lem5218780 (b : real) (s : real -> Prop) : (term261 s b) = (term254 b s).
Proof. exact (eq_refl (term261 s b)). Qed.
Lemma lem5218781 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5218782 (b : real) (s : real -> Prop) (x : real) : (term262 s b x) = (term263 b s x).
Proof. exact (MK_COMB (@lem5218780 b s) (@lem5218781 x)). Qed.
Lemma lem5218783 (x : real) (b : real) (s : real -> Prop) : (term263 b s x) = (term252 x b s).
Proof. exact (eq_refl (term263 b s x)). Qed.
Lemma lem5218784 (x : real) (b : real) (s : real -> Prop) : (term262 s b x) = (term252 x b s).
Proof. exact (TRANS (@lem5218782 b s x) (@lem5218783 x b s)). Qed.
Lemma lem5218785 (b : real) (s : real -> Prop) : (term264 s b) = (term254 b s).
Proof. exact (fun_ext (fun x : real => @lem5218784 x b s)). Qed.
Lemma lem5218786 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5218787 (b : real) (s : real -> Prop) : (term265 s b) = (term255 b s).
Proof. exact (MK_COMB (@lem5218786) (@lem5218785 b s)). Qed.
Lemma lem5218788 (s : real -> Prop) : (term266 s) = (term256 s).
Proof. exact (fun_ext (fun b : real => @lem5218787 b s)). Qed.
Lemma lem5218789 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5218790 (s : real -> Prop) : (term258 s) = (term257 s).
Proof. exact (MK_COMB (@lem5218789) (@lem5218788 s)). Qed.
Lemma lem5218791 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5218792 (s : real -> Prop) : (term267 s) = (term268 s).
Proof. exact (MK_COMB (@lem5218791) (@lem5218790 s)). Qed.
Lemma lem5218793 (b : real) (s : real -> Prop) : (term261 s b) = (term254 b s).
Proof. exact (eq_refl (term261 s b)). Qed.
Lemma lem5218794 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5218795 (s : real -> Prop) (x : real -> real) (b : real) : (term269 s x b) = (term270 s x b).
Proof. exact (MK_COMB (@lem5218793 b s) (@lem5218794 x b)). Qed.
Lemma lem5218796 (x : real -> real) (b : real) (s : real -> Prop) : (term270 s x b) = (term271 x b s).
Proof. exact (eq_refl (term270 s x b)). Qed.
Lemma lem5218797 (x : real -> real) (b : real) (s : real -> Prop) : (term269 s x b) = (term271 x b s).
Proof. exact (TRANS (@lem5218795 s x b) (@lem5218796 x b s)). Qed.
Lemma lem5218798 (x : real -> real) (s : real -> Prop) : (term272 s x) = (term273 x s).
Proof. exact (fun_ext (fun b : real => @lem5218797 x b s)). Qed.
Lemma lem5218799 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5218800 (x : real -> real) (s : real -> Prop) : (term274 s x) = (term275 x s).
Proof. exact (MK_COMB (@lem5218799) (@lem5218798 x s)). Qed.
Lemma lem5218801 (s : real -> Prop) : (term276 s) = (term277 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5218800 x s)). Qed.
Lemma lem5218802 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5218803 (s : real -> Prop) : (term259 s) = (term278 s).
Proof. exact (MK_COMB (@lem5218802) (@lem5218801 s)). Qed.
Lemma lem5218804 (s : real -> Prop) : ((term258 s) = (term259 s)) = ((term257 s) = (term278 s)).
Proof. exact (MK_COMB (@lem5218792 s) (@lem5218803 s)). Qed.
Lemma lem5218805 (s : real -> Prop) : (term257 s) = (term278 s).
Proof. exact (EQ_MP (@lem5218804 s) (@lem5218779 s)). Qed.
Lemma lem5218806 (s : real -> Prop) : (term188 s) = (term278 s).
Proof. exact (TRANS (@lem5218775 s) (@lem5218805 s)). Qed.
Lemma lem5218807 (s : real -> Prop) : (term189 s) = (term189 s).
Proof. exact (eq_refl (term189 s)). Qed.
Lemma lem5218808 (s : real -> Prop) : (term190 s) = (term279 s).
Proof. exact (MK_COMB (@lem5218807 s) (@lem5218806 s)). Qed.
Lemma lem5218810 {A : Type'} (P : Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5218811 (P : Prop) (Q : type1028) : (term280 P Q) = (term281 P Q).
Proof. exact (@lem5218810 (real -> real) P Q). Qed.
Lemma lem5218812 (s : real -> Prop) : (term282 s) = (term283 s).
Proof. exact (@lem5218811 (term182 s) (term277 s)). Qed.
Lemma lem5218813 (x : real -> real) (s : real -> Prop) : (term284 s x) = (term275 x s).
Proof. exact (eq_refl (term284 s x)). Qed.
Lemma lem5218814 (s : real -> Prop) : (term285 s) = (term277 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5218813 x s)). Qed.
Lemma lem5218815 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5218816 (s : real -> Prop) : (term286 s) = (term278 s).
Proof. exact (MK_COMB (@lem5218815) (@lem5218814 s)). Qed.
Lemma lem5218817 (s : real -> Prop) : (term189 s) = (term189 s).
Proof. exact (eq_refl (term189 s)). Qed.
Lemma lem5218818 (s : real -> Prop) : (term282 s) = (term279 s).
Proof. exact (MK_COMB (@lem5218817 s) (@lem5218816 s)). Qed.
Lemma lem5218819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5218820 (s : real -> Prop) : (term287 s) = (term288 s).
Proof. exact (MK_COMB (@lem5218819) (@lem5218818 s)). Qed.
Lemma lem5218821 (x : real -> real) (s : real -> Prop) : (term284 s x) = (term275 x s).
Proof. exact (eq_refl (term284 s x)). Qed.
Lemma lem5218822 (s : real -> Prop) : (term189 s) = (term189 s).
Proof. exact (eq_refl (term189 s)). Qed.
Lemma lem5218823 (x : real -> real) (s : real -> Prop) : (term289 s x) = (term290 x s).
Proof. exact (MK_COMB (@lem5218822 s) (@lem5218821 x s)). Qed.
Lemma lem5218824 (s : real -> Prop) : (term291 s) = (term292 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5218823 x s)). Qed.
Lemma lem5218825 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5218826 (s : real -> Prop) : (term283 s) = (term293 s).
Proof. exact (MK_COMB (@lem5218825) (@lem5218824 s)). Qed.
Lemma lem5218827 (s : real -> Prop) : ((term282 s) = (term283 s)) = ((term279 s) = (term293 s)).
Proof. exact (MK_COMB (@lem5218820 s) (@lem5218826 s)). Qed.
Lemma lem5218828 (s : real -> Prop) : (term279 s) = (term293 s).
Proof. exact (EQ_MP (@lem5218827 s) (@lem5218812 s)). Qed.
Lemma lem5218829 (s : real -> Prop) : (term190 s) = (term293 s).
Proof. exact (TRANS (@lem5218808 s) (@lem5218828 s)). Qed.
Lemma lem5218830 (s : real -> Prop) : (term194 s) = (term294 s).
Proof. exact (MK_COMB (@lem5218748 s) (@lem5218829 s)). Qed.
Lemma lem5218832 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term295 A P Q) = (term296 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5218833 (P : type1028) (Q : type1028) : (term297 P Q) = (term298 P Q).
Proof. exact (@lem5218832 (real -> real) P Q). Qed.
Lemma lem5218834 (s : real -> Prop) : (term299 s) = (term300 s).
Proof. exact (@lem5218833 (term235 s) (term292 s)). Qed.
Lemma lem5218835 (s : real -> Prop) (x : real -> real) : (term301 s x) = (term233 s x).
Proof. exact (eq_refl (term301 s x)). Qed.
Lemma lem5218836 (s : real -> Prop) : (term302 s) = (term235 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5218835 s x)). Qed.
Lemma lem5218837 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5218838 (s : real -> Prop) : (term303 s) = (term236 s).
Proof. exact (MK_COMB (@lem5218837) (@lem5218836 s)). Qed.
Lemma lem5218839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5218840 (s : real -> Prop) : (term304 s) = (term237 s).
Proof. exact (MK_COMB (@lem5218839) (@lem5218838 s)). Qed.
Lemma lem5218841 (x : real -> real) (s : real -> Prop) : (term305 s x) = (term290 x s).
Proof. exact (eq_refl (term305 s x)). Qed.
Lemma lem5218842 (s : real -> Prop) : (term306 s) = (term292 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5218841 x s)). Qed.
Lemma lem5218843 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5218844 (s : real -> Prop) : (term307 s) = (term293 s).
Proof. exact (MK_COMB (@lem5218843) (@lem5218842 s)). Qed.
Lemma lem5218845 (s : real -> Prop) : (term299 s) = (term294 s).
Proof. exact (MK_COMB (@lem5218840 s) (@lem5218844 s)). Qed.
Lemma lem5218846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5218847 (s : real -> Prop) : (term308 s) = (term309 s).
Proof. exact (MK_COMB (@lem5218846) (@lem5218845 s)). Qed.
Lemma lem5218848 (s : real -> Prop) (x : real -> real) : (term301 s x) = (term233 s x).
Proof. exact (eq_refl (term301 s x)). Qed.
Lemma lem5218849 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5218850 (s : real -> Prop) (x : real -> real) : (term310 s x) = (term311 s x).
Proof. exact (MK_COMB (@lem5218849) (@lem5218848 s x)). Qed.
Lemma lem5218851 (x : real -> real) (s : real -> Prop) : (term305 s x) = (term290 x s).
Proof. exact (eq_refl (term305 s x)). Qed.
Lemma lem5218852 (x : real -> real) (s : real -> Prop) : (term312 s x) = (term313 x s).
Proof. exact (MK_COMB (@lem5218850 s x) (@lem5218851 x s)). Qed.
Lemma lem5218853 (s : real -> Prop) : (term314 s) = (term315 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5218852 x s)). Qed.
Lemma lem5218854 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5218855 (s : real -> Prop) : (term300 s) = (term316 s).
Proof. exact (MK_COMB (@lem5218854) (@lem5218853 s)). Qed.
Lemma lem5218856 (s : real -> Prop) : ((term299 s) = (term300 s)) = ((term294 s) = (term316 s)).
Proof. exact (MK_COMB (@lem5218847 s) (@lem5218855 s)). Qed.
Lemma lem5218857 (s : real -> Prop) : (term294 s) = (term316 s).
Proof. exact (EQ_MP (@lem5218856 s) (@lem5218834 s)). Qed.
Lemma lem5218858 (s : real -> Prop) : (term194 s) = (term316 s).
Proof. exact (TRANS (@lem5218830 s) (@lem5218857 s)). Qed.
Lemma lem5218859 : term195 = term317.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5218858 s)). Qed.
Lemma lem5218860 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5218861 : term196 = term318.
Proof. exact (MK_COMB (@lem5218860) (@lem5218859)). Qed.
Lemma lem5218863 {A B : Type'} (P : type1413 A B) : (term197 A B P) = (term198 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5218864 (P : type1017) : (term319 P) = (term320 P).
Proof. exact (@lem5218863 (real -> Prop) (real -> real) P). Qed.
Lemma lem5218865 : term321 = term322.
Proof. exact (@lem5218864 term323). Qed.
Lemma lem5218866 (s : real -> Prop) : (term324 s) = (term315 s).
Proof. exact (eq_refl (term324 s)). Qed.
Lemma lem5218867 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5218868 (s : real -> Prop) (x : real -> real) : (term325 s x) = (term326 s x).
Proof. exact (MK_COMB (@lem5218866 s) (@lem5218867 x)). Qed.
Lemma lem5218869 (x : real -> real) (s : real -> Prop) : (term326 s x) = (term313 x s).
Proof. exact (eq_refl (term326 s x)). Qed.
Lemma lem5218870 (x : real -> real) (s : real -> Prop) : (term325 s x) = (term313 x s).
Proof. exact (TRANS (@lem5218868 s x) (@lem5218869 x s)). Qed.
Lemma lem5218871 (s : real -> Prop) : (term327 s) = (term315 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5218870 x s)). Qed.
Lemma lem5218872 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5218873 (s : real -> Prop) : (term328 s) = (term316 s).
Proof. exact (MK_COMB (@lem5218872) (@lem5218871 s)). Qed.
Lemma lem5218874 : term329 = term317.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5218873 s)). Qed.
Lemma lem5218875 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5218876 : term321 = term318.
Proof. exact (MK_COMB (@lem5218875) (@lem5218874)). Qed.
Lemma lem5218877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5218878 : term330 = term331.
Proof. exact (MK_COMB (@lem5218877) (@lem5218876)). Qed.
Lemma lem5218879 (s : real -> Prop) : (term324 s) = (term315 s).
Proof. exact (eq_refl (term324 s)). Qed.
Lemma lem5218880 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5218881 (x : type1021) (s : real -> Prop) : (term332 x s) = (term333 x s).
Proof. exact (MK_COMB (@lem5218879 s) (@lem5218880 x s)). Qed.
Lemma lem5218882 (x : type1021) (s : real -> Prop) : (term333 x s) = (term334 x s).
Proof. exact (eq_refl (term333 x s)). Qed.
Lemma lem5218883 (x : type1021) (s : real -> Prop) : (term332 x s) = (term334 x s).
Proof. exact (TRANS (@lem5218881 x s) (@lem5218882 x s)). Qed.
Lemma lem5218884 (x : type1021) : (term335 x) = (term336 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5218883 x s)). Qed.
Lemma lem5218885 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5218886 (x : type1021) : (term337 x) = (term338 x).
Proof. exact (MK_COMB (@lem5218885) (@lem5218884 x)). Qed.
Lemma lem5218887 : term339 = term340.
Proof. exact (fun_ext (fun x : type1021 => @lem5218886 x)). Qed.
Lemma lem5218888 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5218889 : term322 = term341.
Proof. exact (MK_COMB (@lem5218888) (@lem5218887)). Qed.
Lemma lem5218890 : (term321 = term322) = (term318 = term341).
Proof. exact (MK_COMB (@lem5218878) (@lem5218889)). Qed.
Lemma lem5218891 : term318 = term341.
Proof. exact (EQ_MP (@lem5218890) (@lem5218865)). Qed.
Lemma lem5218893 : term196 = term341.
Proof. exact (TRANS (@lem5218861) (@lem5218891)). Qed.
Lemma lem5218894 : term66 = term341.
Proof. exact (TRANS (@lem5218448) (@lem5218893)). Qed.
Lemma lem5218895 (h1 : term66) : term341.
Proof. exact (EQ_MP (@lem5218894) (@lem5218090 h1)). Qed.
Lemma lem5218972 (y : real) (x : real) : (term342 y x) = (term343 y x).
Proof. exact (@lem17045 (real_le x y) (real_le y x)). Qed.
Lemma lem5218977 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5218978 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5218979 (y : real) (x : real) : (term344 y x) = (term345 y x).
Proof. exact (MK_COMB (@lem5218978) (@lem5218972 y x)). Qed.
Lemma lem5218980 (x : real) (y : real) : (term346 x y) = (term347 x y).
Proof. exact (MK_COMB (@lem5218979 y x) (@lem5218977 x y)). Qed.
Lemma lem5218985 (x : real) (y : real) : (term348 x y) = (term348 x y).
Proof. exact (eq_refl (term348 x y)). Qed.
Lemma lem5218986 (x : real) (y : real) : (term349 x y) = (term350 x y).
Proof. exact (MK_COMB (@lem5218985 x y) (@lem5218980 x y)). Qed.
Lemma lem5218987 (x : real) (y : real) : ((term37 y x) = (x = y)) = (term349 x y).
Proof. exact (@lem17784 (term37 y x) (x = y)). Qed.
Lemma lem5218988 (x : real) (y : real) : ((term37 y x) = (x = y)) = (term350 x y).
Proof. exact (TRANS (@lem5218987 x y) (@lem5218986 x y)). Qed.
Lemma lem5218989 (x : real) : (term38 x) = (term351 x).
Proof. exact (fun_ext (fun y : real => @lem5218988 x y)). Qed.
Lemma lem5218990 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5218991 (x : real) : (term39 x) = (term352 x).
Proof. exact (MK_COMB (@lem5218990) (@lem5218989 x)). Qed.
Lemma lem5218992 : term40 = term353.
Proof. exact (fun_ext (fun x : real => @lem5218991 x)). Qed.
Lemma lem5218993 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5218994 : term21 = term354.
Proof. exact (MK_COMB (@lem5218993) (@lem5218992)). Qed.
Lemma lem5219000 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term355 A P Q) = (term356 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5219001 (P : real -> Prop) (Q : real -> Prop) : (term357 P Q) = (term358 P Q).
Proof. exact (@lem5219000 real P Q). Qed.
Lemma lem5219002 (x : real) : (term359 x) = (term360 x).
Proof. exact (@lem5219001 (term361 x) (term362 x)). Qed.
Lemma lem5219003 (x : real) (y : real) : (term363 x y) = (term364 x y).
Proof. exact (eq_refl (term363 x y)). Qed.
Lemma lem5219004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219005 (x : real) (y : real) : (term365 x y) = (term348 x y).
Proof. exact (MK_COMB (@lem5219004) (@lem5219003 x y)). Qed.
Lemma lem5219006 (x : real) (y : real) : (term366 x y) = (term347 x y).
Proof. exact (eq_refl (term366 x y)). Qed.
Lemma lem5219007 (x : real) (y : real) : (term367 x y) = (term350 x y).
Proof. exact (MK_COMB (@lem5219005 x y) (@lem5219006 x y)). Qed.
Lemma lem5219008 (x : real) : (term368 x) = (term351 x).
Proof. exact (fun_ext (fun y : real => @lem5219007 x y)). Qed.
Lemma lem5219009 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219010 (x : real) : (term359 x) = (term352 x).
Proof. exact (MK_COMB (@lem5219009) (@lem5219008 x)). Qed.
Lemma lem5219011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5219012 (x : real) : (term369 x) = (term370 x).
Proof. exact (MK_COMB (@lem5219011) (@lem5219010 x)). Qed.
Lemma lem5219013 (x : real) (y : real) : (term363 x y) = (term364 x y).
Proof. exact (eq_refl (term363 x y)). Qed.
Lemma lem5219014 (x : real) : (term371 x) = (term361 x).
Proof. exact (fun_ext (fun y : real => @lem5219013 x y)). Qed.
Lemma lem5219015 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219016 (x : real) : (term372 x) = (term373 x).
Proof. exact (MK_COMB (@lem5219015) (@lem5219014 x)). Qed.
Lemma lem5219017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219018 (x : real) : (term374 x) = (term375 x).
Proof. exact (MK_COMB (@lem5219017) (@lem5219016 x)). Qed.
Lemma lem5219019 (x : real) (y : real) : (term366 x y) = (term347 x y).
Proof. exact (eq_refl (term366 x y)). Qed.
Lemma lem5219020 (x : real) : (term376 x) = (term362 x).
Proof. exact (fun_ext (fun y : real => @lem5219019 x y)). Qed.
Lemma lem5219021 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219022 (x : real) : (term377 x) = (term378 x).
Proof. exact (MK_COMB (@lem5219021) (@lem5219020 x)). Qed.
Lemma lem5219023 (x : real) : (term360 x) = (term379 x).
Proof. exact (MK_COMB (@lem5219018 x) (@lem5219022 x)). Qed.
Lemma lem5219024 (x : real) : ((term359 x) = (term360 x)) = ((term352 x) = (term379 x)).
Proof. exact (MK_COMB (@lem5219012 x) (@lem5219023 x)). Qed.
Lemma lem5219025 (x : real) : (term352 x) = (term379 x).
Proof. exact (EQ_MP (@lem5219024 x) (@lem5219002 x)). Qed.
Lemma lem5219122 : term353 = term380.
Proof. exact (fun_ext (fun x : real => @lem5219025 x)). Qed.
Lemma lem5219123 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219124 : term354 = term381.
Proof. exact (MK_COMB (@lem5219123) (@lem5219122)). Qed.
Lemma lem5219126 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term355 A P Q) = (term356 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5219127 (P : real -> Prop) (Q : real -> Prop) : (term357 P Q) = (term358 P Q).
Proof. exact (@lem5219126 real P Q). Qed.
Lemma lem5219128 : term382 = term383.
Proof. exact (@lem5219127 term384 term385). Qed.
Lemma lem5219129 (x : real) : (term386 x) = (term373 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem5219130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219131 (x : real) : (term387 x) = (term375 x).
Proof. exact (MK_COMB (@lem5219130) (@lem5219129 x)). Qed.
Lemma lem5219132 (x : real) : (term388 x) = (term378 x).
Proof. exact (eq_refl (term388 x)). Qed.
Lemma lem5219133 (x : real) : (term389 x) = (term379 x).
Proof. exact (MK_COMB (@lem5219131 x) (@lem5219132 x)). Qed.
Lemma lem5219134 : term390 = term380.
Proof. exact (fun_ext (fun x : real => @lem5219133 x)). Qed.
Lemma lem5219135 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219136 : term382 = term381.
Proof. exact (MK_COMB (@lem5219135) (@lem5219134)). Qed.
Lemma lem5219137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5219138 : term391 = term392.
Proof. exact (MK_COMB (@lem5219137) (@lem5219136)). Qed.
Lemma lem5219139 (x : real) : (term386 x) = (term373 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem5219140 : term393 = term384.
Proof. exact (fun_ext (fun x : real => @lem5219139 x)). Qed.
Lemma lem5219141 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219142 : term394 = term395.
Proof. exact (MK_COMB (@lem5219141) (@lem5219140)). Qed.
Lemma lem5219143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219144 : term396 = term397.
Proof. exact (MK_COMB (@lem5219143) (@lem5219142)). Qed.
Lemma lem5219145 (x : real) : (term388 x) = (term378 x).
Proof. exact (eq_refl (term388 x)). Qed.
Lemma lem5219146 : term398 = term385.
Proof. exact (fun_ext (fun x : real => @lem5219145 x)). Qed.
Lemma lem5219147 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219148 : term399 = term400.
Proof. exact (MK_COMB (@lem5219147) (@lem5219146)). Qed.
Lemma lem5219149 : term383 = term401.
Proof. exact (MK_COMB (@lem5219144) (@lem5219148)). Qed.
Lemma lem5219150 : (term382 = term383) = (term381 = term401).
Proof. exact (MK_COMB (@lem5219138) (@lem5219149)). Qed.
Lemma lem5219151 : term381 = term401.
Proof. exact (EQ_MP (@lem5219150) (@lem5219128)). Qed.
Lemma lem5219258 : term354 = term401.
Proof. exact (TRANS (@lem5219124) (@lem5219151)). Qed.
Lemma lem5219259 : term21 = term401.
Proof. exact (TRANS (@lem5218994) (@lem5219258)). Qed.
Lemma lem5219260 (h1 : term21) : term401.
Proof. exact (EQ_MP (@lem5219259) (@lem5218092 h1)). Qed.
Lemma lem5219261 (x : type1021) (h1 : term338 x) : term338 x.
Proof. exact (h1). Qed.
Lemma lem5219262 (b : real) (s : real -> Prop) (h1 : term152 b s) : term152 b s.
Proof. exact (h1). Qed.
Lemma lem5219263 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term149 b s x'.
Proof. exact (h1). Qed.
Lemma lem5219277 (s : real -> Prop) (h1 : term9 s) : term9 s.
Proof. exact (h1). Qed.
Lemma lem5219322 (x : real) (y : real) : (term347 x y) = (term347 x y).
Proof. exact (eq_refl (term347 x y)). Qed.
Lemma lem5219323 (x : real) : (term362 x) = (term362 x).
Proof. exact (fun_ext (fun y : real => @lem5219322 x y)). Qed.
Lemma lem5219324 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219325 (x : real) : (term378 x) = (term378 x).
Proof. exact (MK_COMB (@lem5219324) (@lem5219323 x)). Qed.
Lemma lem5219326 : term385 = term385.
Proof. exact (fun_ext (fun x : real => @lem5219325 x)). Qed.
Lemma lem5219327 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219328 : term400 = term400.
Proof. exact (MK_COMB (@lem5219327) (@lem5219326)). Qed.
Lemma lem5219351 (x : real) (y : real) : (term364 x y) = (term364 x y).
Proof. exact (eq_refl (term364 x y)). Qed.
Lemma lem5219352 (x : real) : (term361 x) = (term361 x).
Proof. exact (fun_ext (fun y : real => @lem5219351 x y)). Qed.
Lemma lem5219353 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219354 (x : real) : (term373 x) = (term373 x).
Proof. exact (MK_COMB (@lem5219353) (@lem5219352 x)). Qed.
Lemma lem5219355 : term384 = term384.
Proof. exact (fun_ext (fun x : real => @lem5219354 x)). Qed.
Lemma lem5219356 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219357 : term395 = term395.
Proof. exact (MK_COMB (@lem5219356) (@lem5219355)). Qed.
Lemma lem5219358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219359 : term397 = term397.
Proof. exact (MK_COMB (@lem5219358) (@lem5219357)). Qed.
Lemma lem5219360 : term401 = term401.
Proof. exact (MK_COMB (@lem5219359) (@lem5219328)). Qed.
Lemma lem5219361 (h1 : term21) : term401.
Proof. exact (EQ_MP (@lem5219360) (@lem5219260 h1)). Qed.
Lemma lem5219394 (x : type1021) (b : real) (s : real -> Prop) : (term402 x b s) = (term402 x b s).
Proof. exact (eq_refl (term402 x b s)). Qed.
Lemma lem5219395 (x : type1021) (s : real -> Prop) : (term403 x s) = (term403 x s).
Proof. exact (fun_ext (fun b : real => @lem5219394 x b s)). Qed.
Lemma lem5219396 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219397 (x : type1021) (s : real -> Prop) : (term404 x s) = (term404 x s).
Proof. exact (MK_COMB (@lem5219396) (@lem5219395 x s)). Qed.
Lemma lem5219414 (s : real -> Prop) (x : real) : (term180 s x) = (term180 s x).
Proof. exact (eq_refl (term180 s x)). Qed.
Lemma lem5219415 (s : real -> Prop) : (term181 s) = (term181 s).
Proof. exact (fun_ext (fun x : real => @lem5219414 s x)). Qed.
Lemma lem5219416 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219417 (s : real -> Prop) : (term182 s) = (term182 s).
Proof. exact (MK_COMB (@lem5219416) (@lem5219415 s)). Qed.
Lemma lem5219418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219419 (s : real -> Prop) : (term189 s) = (term189 s).
Proof. exact (MK_COMB (@lem5219418) (@lem5219417 s)). Qed.
Lemma lem5219420 (x : type1021) (s : real -> Prop) : (term405 x s) = (term405 x s).
Proof. exact (MK_COMB (@lem5219419 s) (@lem5219397 x s)). Qed.
Lemma lem5219443 (x : type1021) (s : real -> Prop) (b : real) : (term406 x s b) = (term406 x s b).
Proof. exact (eq_refl (term406 x s b)). Qed.
Lemma lem5219444 (x : type1021) (s : real -> Prop) : (term407 x s) = (term407 x s).
Proof. exact (fun_ext (fun b : real => @lem5219443 x s b)). Qed.
Lemma lem5219445 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219446 (x : type1021) (s : real -> Prop) : (term408 x s) = (term408 x s).
Proof. exact (MK_COMB (@lem5219445) (@lem5219444 x s)). Qed.
Lemma lem5219453 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5219454 (x : type1021) (s : real -> Prop) : (term409 x s) = (term409 x s).
Proof. exact (MK_COMB (@lem5219453 s) (@lem5219446 x s)). Qed.
Lemma lem5219455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5219456 (x : type1021) (s : real -> Prop) : (term410 x s) = (term410 x s).
Proof. exact (MK_COMB (@lem5219455) (@lem5219454 x s)). Qed.
Lemma lem5219457 (x : type1021) (s : real -> Prop) : (term334 x s) = (term334 x s).
Proof. exact (MK_COMB (@lem5219456 x s) (@lem5219420 x s)). Qed.
Lemma lem5219458 (x : type1021) : (term336 x) = (term336 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5219457 x s)). Qed.
Lemma lem5219459 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5219460 (x : type1021) : (term338 x) = (term338 x).
Proof. exact (MK_COMB (@lem5219459) (@lem5219458 x)). Qed.
Lemma lem5219461 (x : type1021) (h1 : term338 x) : term338 x.
Proof. exact (EQ_MP (@lem5219460 x) (@lem5219261 x h1)). Qed.
Lemma lem5219490 (s : real -> Prop) (x' : real) : (term113 s x') = (term113 s x').
Proof. exact (eq_refl (term113 s x')). Qed.
Lemma lem5219505 (s : real -> Prop) (b : real) (x : real) : (term73 s b x) = (term73 s b x).
Proof. exact (eq_refl (term73 s b x)). Qed.
Lemma lem5219506 (s : real -> Prop) (b : real) : (term74 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5219505 s b x)). Qed.
Lemma lem5219507 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219508 (s : real -> Prop) (b : real) : (term75 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5219507) (@lem5219506 s b)). Qed.
Lemma lem5219515 (b : real) (s : real -> Prop) : (term69 b s) = (term69 b s).
Proof. exact (eq_refl (term69 b s)). Qed.
Lemma lem5219516 (s : real -> Prop) (b : real) : (term76 s b) = (term76 s b).
Proof. exact (MK_COMB (@lem5219515 b s) (@lem5219508 s b)). Qed.
Lemma lem5219517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219518 (s : real -> Prop) (b : real) : (term131 s b) = (term131 s b).
Proof. exact (MK_COMB (@lem5219517) (@lem5219516 s b)). Qed.
Lemma lem5219519 (b : real) (s : real -> Prop) (x' : real) : (term149 b s x') = (term149 b s x').
Proof. exact (MK_COMB (@lem5219518 s b) (@lem5219490 s x')). Qed.
Lemma lem5219520 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term149 b s x'.
Proof. exact (EQ_MP (@lem5219519 b s x') (@lem5219263 b s x' h1)). Qed.
Lemma lem5219521 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term113 s x'.
Proof. exact (proj2 (@lem5219520 b s x' h1)). Qed.
Lemma lem5219522 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term76 s b.
Proof. exact (proj1 (@lem5219520 b s x' h1)). Qed.
Lemma lem5219523 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term75 s b.
Proof. exact (proj2 (@lem5219522 b s x' h1)). Qed.
Lemma lem5219525 (h1 : term21) : term400.
Proof. exact (proj2 (@lem5219361 h1)). Qed.
Lemma lem5219530 (s : real -> Prop) (x' : real) (h1 : term80 s x') : term80 s x'.
Proof. exact (h1). Qed.
Lemma lem5219550 {A : Type'} (P : Prop) (Q : A -> Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5219551 (P : Prop) (Q : real -> Prop) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem5219550 real P Q). Qed.
Lemma lem5219552 (x : type1021) (s : real -> Prop) : (term415 x s) = (term416 x s).
Proof. exact (@lem5219551 (s = (@EMPTY real)) (term407 x s)). Qed.
Lemma lem5219553 (x : type1021) (s : real -> Prop) (b : real) : (term417 x s b) = (term406 x s b).
Proof. exact (eq_refl (term417 x s b)). Qed.
Lemma lem5219554 (x : type1021) (s : real -> Prop) : (term418 x s) = (term407 x s).
Proof. exact (fun_ext (fun b : real => @lem5219553 x s b)). Qed.
Lemma lem5219555 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219556 (x : type1021) (s : real -> Prop) : (term419 x s) = (term408 x s).
Proof. exact (MK_COMB (@lem5219555) (@lem5219554 x s)). Qed.
Lemma lem5219557 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5219558 (x : type1021) (s : real -> Prop) : (term415 x s) = (term409 x s).
Proof. exact (MK_COMB (@lem5219557 s) (@lem5219556 x s)). Qed.
Lemma lem5219559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5219560 (x : type1021) (s : real -> Prop) : (term420 x s) = (term421 x s).
Proof. exact (MK_COMB (@lem5219559) (@lem5219558 x s)). Qed.
Lemma lem5219561 (x : type1021) (s : real -> Prop) (b : real) : (term417 x s b) = (term406 x s b).
Proof. exact (eq_refl (term417 x s b)). Qed.
Lemma lem5219562 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5219563 (x : type1021) (s : real -> Prop) (b : real) : (term422 x s b) = (term423 x s b).
Proof. exact (MK_COMB (@lem5219562 s) (@lem5219561 x s b)). Qed.
Lemma lem5219564 (x : type1021) (s : real -> Prop) : (term424 x s) = (term425 x s).
Proof. exact (fun_ext (fun b : real => @lem5219563 x s b)). Qed.
Lemma lem5219565 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219566 (x : type1021) (s : real -> Prop) : (term416 x s) = (term426 x s).
Proof. exact (MK_COMB (@lem5219565) (@lem5219564 x s)). Qed.
Lemma lem5219567 (x : type1021) (s : real -> Prop) : ((term415 x s) = (term416 x s)) = ((term409 x s) = (term426 x s)).
Proof. exact (MK_COMB (@lem5219560 x s) (@lem5219566 x s)). Qed.
Lemma lem5219568 (x : type1021) (s : real -> Prop) : (term409 x s) = (term426 x s).
Proof. exact (EQ_MP (@lem5219567 x s) (@lem5219552 x s)). Qed.
Lemma lem5219569 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5219570 (x : type1021) (s : real -> Prop) : (term410 x s) = (term427 x s).
Proof. exact (MK_COMB (@lem5219569) (@lem5219568 x s)). Qed.
Lemma lem5219572 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term356 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5219573 (P : real -> Prop) (Q : real -> Prop) : (term358 P Q) = (term357 P Q).
Proof. exact (@lem5219572 real P Q). Qed.
Lemma lem5219574 (x : type1021) (s : real -> Prop) : (term428 x s) = (term429 x s).
Proof. exact (@lem5219573 (term181 s) (term403 x s)). Qed.
Lemma lem5219575 (s : real -> Prop) (b : real) : (term430 s b) = (term180 s b).
Proof. exact (eq_refl (term430 s b)). Qed.
Lemma lem5219576 (s : real -> Prop) : (term431 s) = (term181 s).
Proof. exact (fun_ext (fun b : real => @lem5219575 s b)). Qed.
Lemma lem5219577 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219578 (s : real -> Prop) : (term432 s) = (term182 s).
Proof. exact (MK_COMB (@lem5219577) (@lem5219576 s)). Qed.
Lemma lem5219579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219580 (s : real -> Prop) : (term433 s) = (term189 s).
Proof. exact (MK_COMB (@lem5219579) (@lem5219578 s)). Qed.
Lemma lem5219581 (x : type1021) (b : real) (s : real -> Prop) : (term434 x s b) = (term402 x b s).
Proof. exact (eq_refl (term434 x s b)). Qed.
Lemma lem5219582 (x : type1021) (s : real -> Prop) : (term435 x s) = (term403 x s).
Proof. exact (fun_ext (fun b : real => @lem5219581 x b s)). Qed.
Lemma lem5219583 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219584 (x : type1021) (s : real -> Prop) : (term436 x s) = (term404 x s).
Proof. exact (MK_COMB (@lem5219583) (@lem5219582 x s)). Qed.
Lemma lem5219585 (x : type1021) (s : real -> Prop) : (term428 x s) = (term405 x s).
Proof. exact (MK_COMB (@lem5219580 s) (@lem5219584 x s)). Qed.
Lemma lem5219586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5219587 (x : type1021) (s : real -> Prop) : (term437 x s) = (term438 x s).
Proof. exact (MK_COMB (@lem5219586) (@lem5219585 x s)). Qed.
Lemma lem5219588 (s : real -> Prop) (b : real) : (term430 s b) = (term180 s b).
Proof. exact (eq_refl (term430 s b)). Qed.
Lemma lem5219589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219590 (s : real -> Prop) (b : real) : (term439 s b) = (term440 s b).
Proof. exact (MK_COMB (@lem5219589) (@lem5219588 s b)). Qed.
Lemma lem5219591 (x : type1021) (b : real) (s : real -> Prop) : (term434 x s b) = (term402 x b s).
Proof. exact (eq_refl (term434 x s b)). Qed.
Lemma lem5219592 (x : type1021) (b : real) (s : real -> Prop) : (term441 x s b) = (term442 x b s).
Proof. exact (MK_COMB (@lem5219590 s b) (@lem5219591 x b s)). Qed.
Lemma lem5219593 (x : type1021) (s : real -> Prop) : (term443 x s) = (term444 x s).
Proof. exact (fun_ext (fun b : real => @lem5219592 x b s)). Qed.
Lemma lem5219594 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219595 (x : type1021) (s : real -> Prop) : (term429 x s) = (term445 x s).
Proof. exact (MK_COMB (@lem5219594) (@lem5219593 x s)). Qed.
Lemma lem5219596 (x : type1021) (s : real -> Prop) : ((term428 x s) = (term429 x s)) = ((term405 x s) = (term445 x s)).
Proof. exact (MK_COMB (@lem5219587 x s) (@lem5219595 x s)). Qed.
Lemma lem5219597 (x : type1021) (s : real -> Prop) : (term405 x s) = (term445 x s).
Proof. exact (EQ_MP (@lem5219596 x s) (@lem5219574 x s)). Qed.
Lemma lem5219600 (x : type1021) (s : real -> Prop) : (term446 x s) = (term446 x s).
Proof. exact (eq_refl (term446 x s)). Qed.
Lemma lem5219601 (x : type1021) (s : real -> Prop) : (term446 x s) = ((term405 x s) = (term445 x s)).
Proof. exact (eq_refl (term446 x s)). Qed.
Lemma lem5219602 (x : type1021) (s : real -> Prop) : (term447 x s) = (term447 x s).
Proof. exact (eq_refl (term447 x s)). Qed.
Lemma lem5219603 (x : type1021) (s : real -> Prop) : ((term446 x s) = (term446 x s)) = ((term446 x s) = ((term405 x s) = (term445 x s))).
Proof. exact (MK_COMB (@lem5219602 x s) (@lem5219601 x s)). Qed.
Lemma lem5219604 (x : type1021) (s : real -> Prop) : (term446 x s) = ((term405 x s) = (term445 x s)).
Proof. exact (eq_refl (term446 x s)). Qed.
Lemma lem5219605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5219606 (x : type1021) (s : real -> Prop) : (term447 x s) = (term448 x s).
Proof. exact (MK_COMB (@lem5219605) (@lem5219604 x s)). Qed.
Lemma lem5219607 (x : type1021) (s : real -> Prop) : ((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s)).
Proof. exact (eq_refl ((term405 x s) = (term445 x s))). Qed.
Lemma lem5219608 (x : type1021) (s : real -> Prop) : ((term446 x s) = ((term405 x s) = (term445 x s))) = (((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s))).
Proof. exact (MK_COMB (@lem5219606 x s) (@lem5219607 x s)). Qed.
Lemma lem5219609 (x : type1021) (s : real -> Prop) : ((term446 x s) = (term446 x s)) = (((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s))).
Proof. exact (TRANS (@lem5219603 x s) (@lem5219608 x s)). Qed.
Lemma lem5219610 (x : type1021) (s : real -> Prop) : ((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s)).
Proof. exact (EQ_MP (@lem5219609 x s) (@lem5219600 x s)). Qed.
Lemma lem5219611 (x : type1021) (s : real -> Prop) : (term405 x s) = (term445 x s).
Proof. exact (EQ_MP (@lem5219610 x s) (@lem5219597 x s)). Qed.
Lemma lem5219612 (x : type1021) (s : real -> Prop) : (term334 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5219570 x s) (@lem5219611 x s)). Qed.
Lemma lem5219614 {A : Type'} (P : A -> Prop) (Q : Prop) : (term450 A P Q) = (term451 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5219615 (P : real -> Prop) (Q : Prop) : (term452 P Q) = (term453 P Q).
Proof. exact (@lem5219614 real P Q). Qed.
Lemma lem5219616 (x : type1021) (s : real -> Prop) : (term454 x s) = (term455 x s).
Proof. exact (@lem5219615 (term425 x s) (term445 x s)). Qed.
Lemma lem5219617 (x : type1021) (s : real -> Prop) (b : real) : (term456 x s b) = (term423 x s b).
Proof. exact (eq_refl (term456 x s b)). Qed.
Lemma lem5219618 (x : type1021) (s : real -> Prop) : (term457 x s) = (term425 x s).
Proof. exact (fun_ext (fun b : real => @lem5219617 x s b)). Qed.
Lemma lem5219619 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219620 (x : type1021) (s : real -> Prop) : (term458 x s) = (term426 x s).
Proof. exact (MK_COMB (@lem5219619) (@lem5219618 x s)). Qed.
Lemma lem5219621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5219622 (x : type1021) (s : real -> Prop) : (term459 x s) = (term427 x s).
Proof. exact (MK_COMB (@lem5219621) (@lem5219620 x s)). Qed.
Lemma lem5219623 (x : type1021) (s : real -> Prop) : (term445 x s) = (term445 x s).
Proof. exact (eq_refl (term445 x s)). Qed.
Lemma lem5219624 (x : type1021) (s : real -> Prop) : (term454 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5219622 x s) (@lem5219623 x s)). Qed.
Lemma lem5219625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5219626 (x : type1021) (s : real -> Prop) : (term460 x s) = (term461 x s).
Proof. exact (MK_COMB (@lem5219625) (@lem5219624 x s)). Qed.
Lemma lem5219627 (x : type1021) (s : real -> Prop) (b : real) : (term456 x s b) = (term423 x s b).
Proof. exact (eq_refl (term456 x s b)). Qed.
Lemma lem5219628 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5219629 (x : type1021) (s : real -> Prop) (b : real) : (term462 x s b) = (term463 x s b).
Proof. exact (MK_COMB (@lem5219628) (@lem5219627 x s b)). Qed.
Lemma lem5219630 (x : type1021) (s : real -> Prop) : (term445 x s) = (term445 x s).
Proof. exact (eq_refl (term445 x s)). Qed.
Lemma lem5219631 (b : real) (x : type1021) (s : real -> Prop) : (term464 b x s) = (term465 b x s).
Proof. exact (MK_COMB (@lem5219629 x s b) (@lem5219630 x s)). Qed.
Lemma lem5219632 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (fun_ext (fun b : real => @lem5219631 b x s)). Qed.
Lemma lem5219633 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219634 (x : type1021) (s : real -> Prop) : (term455 x s) = (term468 x s).
Proof. exact (MK_COMB (@lem5219633) (@lem5219632 x s)). Qed.
Lemma lem5219635 (x : type1021) (s : real -> Prop) : ((term454 x s) = (term455 x s)) = ((term449 x s) = (term468 x s)).
Proof. exact (MK_COMB (@lem5219626 x s) (@lem5219634 x s)). Qed.
Lemma lem5219636 (x : type1021) (s : real -> Prop) : (term449 x s) = (term468 x s).
Proof. exact (EQ_MP (@lem5219635 x s) (@lem5219616 x s)). Qed.
Lemma lem5219638 {A : Type'} (P : Prop) (Q : A -> Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5219639 (P : Prop) (Q : real -> Prop) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem5219638 real P Q). Qed.
Lemma lem5219640 (b : real) (x : type1021) (s : real -> Prop) : (term469 b x s) = (term470 b x s).
Proof. exact (@lem5219639 (term423 x s b) (term444 x s)). Qed.
Lemma lem5219641 (x : type1021) (b : real) (s : real -> Prop) : (term471 x s b) = (term442 x b s).
Proof. exact (eq_refl (term471 x s b)). Qed.
Lemma lem5219642 (x : type1021) (s : real -> Prop) : (term472 x s) = (term444 x s).
Proof. exact (fun_ext (fun b : real => @lem5219641 x b s)). Qed.
Lemma lem5219643 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219644 (x : type1021) (s : real -> Prop) : (term473 x s) = (term445 x s).
Proof. exact (MK_COMB (@lem5219643) (@lem5219642 x s)). Qed.
Lemma lem5219645 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term463 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5219646 (b : real) (x : type1021) (s : real -> Prop) : (term469 b x s) = (term465 b x s).
Proof. exact (MK_COMB (@lem5219645 x s b) (@lem5219644 x s)). Qed.
Lemma lem5219647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5219648 (b : real) (x : type1021) (s : real -> Prop) : (term474 b x s) = (term475 b x s).
Proof. exact (MK_COMB (@lem5219647) (@lem5219646 b x s)). Qed.
Lemma lem5219649 (x : type1021) (b' : real) (s : real -> Prop) : (term471 x s b') = (term442 x b' s).
Proof. exact (eq_refl (term471 x s b')). Qed.
Lemma lem5219650 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term463 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5219651 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term476 b x s b') = (term477 b x b' s).
Proof. exact (MK_COMB (@lem5219650 x s b) (@lem5219649 x b' s)). Qed.
Lemma lem5219652 (b : real) (x : type1021) (s : real -> Prop) : (term478 b x s) = (term479 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5219651 b x b' s)). Qed.
Lemma lem5219653 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219654 (b : real) (x : type1021) (s : real -> Prop) : (term470 b x s) = (term480 b x s).
Proof. exact (MK_COMB (@lem5219653) (@lem5219652 b x s)). Qed.
Lemma lem5219655 (b : real) (x : type1021) (s : real -> Prop) : ((term469 b x s) = (term470 b x s)) = ((term465 b x s) = (term480 b x s)).
Proof. exact (MK_COMB (@lem5219648 b x s) (@lem5219654 b x s)). Qed.
Lemma lem5219656 (b : real) (x : type1021) (s : real -> Prop) : (term465 b x s) = (term480 b x s).
Proof. exact (EQ_MP (@lem5219655 b x s) (@lem5219640 b x s)). Qed.
Lemma lem5219657 (x : type1021) (s : real -> Prop) : (term467 x s) = (term481 x s).
Proof. exact (fun_ext (fun b : real => @lem5219656 b x s)). Qed.
Lemma lem5219658 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219659 (x : type1021) (s : real -> Prop) : (term468 x s) = (term482 x s).
Proof. exact (MK_COMB (@lem5219658) (@lem5219657 x s)). Qed.
Lemma lem5219660 (x : type1021) (s : real -> Prop) : (term449 x s) = (term482 x s).
Proof. exact (TRANS (@lem5219636 x s) (@lem5219659 x s)). Qed.
Lemma lem5219661 (x : type1021) (s : real -> Prop) : (term334 x s) = (term482 x s).
Proof. exact (TRANS (@lem5219612 x s) (@lem5219660 x s)). Qed.
Lemma lem5219662 (x : type1021) : (term336 x) = (term483 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5219661 x s)). Qed.
Lemma lem5219663 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5219664 (x : type1021) : (term338 x) = (term484 x).
Proof. exact (MK_COMB (@lem5219663) (@lem5219662 x)). Qed.
Lemma lem5219681 (x : type1021) (b' : real) (s : real -> Prop) : (term402 x b' s) = (term485 x b' s).
Proof. exact (@lem19699 (term486 x b' s) (term487 x s b') (term46 b' s)). Qed.
Lemma lem5219690 (s : real -> Prop) (b' : real) : (term440 s b') = (term440 s b').
Proof. exact (eq_refl (term440 s b')). Qed.
Lemma lem5219691 (x : type1021) (b' : real) (s : real -> Prop) : (term442 x b' s) = (term488 x b' s).
Proof. exact (MK_COMB (@lem5219690 s b') (@lem5219681 x b' s)). Qed.
Lemma lem5219708 (x : type1021) (s : real -> Prop) (b : real) : (term423 x s b) = (term489 x s b).
Proof. exact (@lem19490 (term486 x b s) (s = (@EMPTY real)) (term487 x s b)). Qed.
Lemma lem5219709 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5219710 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term490 x s b).
Proof. exact (MK_COMB (@lem5219709) (@lem5219708 x s b)). Qed.
Lemma lem5219711 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term477 b x b' s) = (term491 b x b' s).
Proof. exact (MK_COMB (@lem5219710 x s b) (@lem5219691 x b' s)). Qed.
Lemma lem5219712 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term491 b x b' s) = (term492 b x b' s).
Proof. exact (@lem19490 (term180 s b') (term489 x s b) (term485 x b' s)). Qed.
Lemma lem5219713 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term493 b x b' s) = (term494 b x b' s).
Proof. exact (@lem19490 (term495 x b' s) (term489 x s b) (term496 x b' s)). Qed.
Lemma lem5219720 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term497 b x b' s) = (term498 b x b' s).
Proof. exact (@lem19699 (term499 x b s) (term500 x s b) (term496 x b' s)). Qed.
Lemma lem5219727 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term501 b x b' s) = (term502 b x b' s).
Proof. exact (@lem19699 (term499 x b s) (term500 x s b) (term495 x b' s)). Qed.
Lemma lem5219728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219729 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term503 b x b' s) = (term504 b x b' s).
Proof. exact (MK_COMB (@lem5219728) (@lem5219727 b x b' s)). Qed.
Lemma lem5219730 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term494 b x b' s) = (term505 b x b' s).
Proof. exact (MK_COMB (@lem5219729 b x b' s) (@lem5219720 b x b' s)). Qed.
Lemma lem5219731 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term493 b x b' s) = (term505 b x b' s).
Proof. exact (TRANS (@lem5219713 b x b' s) (@lem5219730 b x b' s)). Qed.
Lemma lem5219738 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term506 x b s b') = (term507 x b s b').
Proof. exact (@lem19699 (term499 x b s) (term500 x s b) (term180 s b')). Qed.
Lemma lem5219739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219740 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term508 x b s b') = (term509 x b s b').
Proof. exact (MK_COMB (@lem5219739) (@lem5219738 x b s b')). Qed.
Lemma lem5219741 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term492 b x b' s) = (term510 b x b' s).
Proof. exact (MK_COMB (@lem5219740 x b s b') (@lem5219731 b x b' s)). Qed.
Lemma lem5219742 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term491 b x b' s) = (term510 b x b' s).
Proof. exact (TRANS (@lem5219712 b x b' s) (@lem5219741 b x b' s)). Qed.
Lemma lem5219743 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term477 b x b' s) = (term510 b x b' s).
Proof. exact (TRANS (@lem5219711 b x b' s) (@lem5219742 b x b' s)). Qed.
Lemma lem5219744 (b : real) (x : type1021) (s : real -> Prop) : (term479 b x s) = (term511 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5219743 b x b' s)). Qed.
Lemma lem5219745 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219746 (b : real) (x : type1021) (s : real -> Prop) : (term480 b x s) = (term512 b x s).
Proof. exact (MK_COMB (@lem5219745) (@lem5219744 b x s)). Qed.
Lemma lem5219747 (x : type1021) (s : real -> Prop) : (term481 x s) = (term513 x s).
Proof. exact (fun_ext (fun b : real => @lem5219746 b x s)). Qed.
Lemma lem5219748 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219749 (x : type1021) (s : real -> Prop) : (term482 x s) = (term514 x s).
Proof. exact (MK_COMB (@lem5219748) (@lem5219747 x s)). Qed.
Lemma lem5219750 (x : type1021) : (term483 x) = (term515 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5219749 x s)). Qed.
Lemma lem5219751 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5219752 (x : type1021) : (term484 x) = (term516 x).
Proof. exact (MK_COMB (@lem5219751) (@lem5219750 x)). Qed.
Lemma lem5219753 (x : type1021) : (term338 x) = (term516 x).
Proof. exact (TRANS (@lem5219664 x) (@lem5219752 x)). Qed.
Lemma lem5219754 (x : type1021) (h1 : term338 x) : term516 x.
Proof. exact (EQ_MP (@lem5219753 x) (@lem5219461 x h1)). Qed.
Lemma lem5219766 (s : real -> Prop) (b : real) (x : real) : (term73 s b x) = (term73 s b x).
Proof. exact (eq_refl (term73 s b x)). Qed.
Lemma lem5219767 (s : real -> Prop) (b : real) : (term74 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5219766 s b x)). Qed.
Lemma lem5219768 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219770 (s : real -> Prop) (b : real) : (term75 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5219768) (@lem5219767 s b)). Qed.
Lemma lem5219771 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term75 s b.
Proof. exact (EQ_MP (@lem5219770 s b) (@lem5219523 b s x' h1)). Qed.
Lemma lem5219811 (x : real) (y : real) : (term347 x y) = (term347 x y).
Proof. exact (eq_refl (term347 x y)). Qed.
Lemma lem5219812 (x : real) : (term362 x) = (term362 x).
Proof. exact (fun_ext (fun y : real => @lem5219811 x y)). Qed.
Lemma lem5219813 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219814 (x : real) : (term378 x) = (term378 x).
Proof. exact (MK_COMB (@lem5219813) (@lem5219812 x)). Qed.
Lemma lem5219815 : term385 = term385.
Proof. exact (fun_ext (fun x : real => @lem5219814 x)). Qed.
Lemma lem5219816 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219818 : term400 = term400.
Proof. exact (MK_COMB (@lem5219816) (@lem5219815)). Qed.
Lemma lem5219819 (h1 : term21) : term400.
Proof. exact (EQ_MP (@lem5219818) (@lem5219525 h1)). Qed.
Lemma lem5219831 (s : real -> Prop) (h1 : term106 s) : term106 s.
Proof. exact (h1). Qed.
Lemma lem5219849 {A : Type'} (P : Prop) (Q : A -> Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5219850 (P : Prop) (Q : real -> Prop) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem5219849 real P Q). Qed.
Lemma lem5219851 (x : type1021) (s : real -> Prop) : (term415 x s) = (term416 x s).
Proof. exact (@lem5219850 (s = (@EMPTY real)) (term407 x s)). Qed.
Lemma lem5219852 (x : type1021) (s : real -> Prop) (b : real) : (term417 x s b) = (term406 x s b).
Proof. exact (eq_refl (term417 x s b)). Qed.
Lemma lem5219853 (x : type1021) (s : real -> Prop) : (term418 x s) = (term407 x s).
Proof. exact (fun_ext (fun b : real => @lem5219852 x s b)). Qed.
Lemma lem5219854 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219855 (x : type1021) (s : real -> Prop) : (term419 x s) = (term408 x s).
Proof. exact (MK_COMB (@lem5219854) (@lem5219853 x s)). Qed.
Lemma lem5219856 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5219857 (x : type1021) (s : real -> Prop) : (term415 x s) = (term409 x s).
Proof. exact (MK_COMB (@lem5219856 s) (@lem5219855 x s)). Qed.
Lemma lem5219858 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5219859 (x : type1021) (s : real -> Prop) : (term420 x s) = (term421 x s).
Proof. exact (MK_COMB (@lem5219858) (@lem5219857 x s)). Qed.
Lemma lem5219860 (x : type1021) (s : real -> Prop) (b : real) : (term417 x s b) = (term406 x s b).
Proof. exact (eq_refl (term417 x s b)). Qed.
Lemma lem5219861 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5219862 (x : type1021) (s : real -> Prop) (b : real) : (term422 x s b) = (term423 x s b).
Proof. exact (MK_COMB (@lem5219861 s) (@lem5219860 x s b)). Qed.
Lemma lem5219863 (x : type1021) (s : real -> Prop) : (term424 x s) = (term425 x s).
Proof. exact (fun_ext (fun b : real => @lem5219862 x s b)). Qed.
Lemma lem5219864 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219865 (x : type1021) (s : real -> Prop) : (term416 x s) = (term426 x s).
Proof. exact (MK_COMB (@lem5219864) (@lem5219863 x s)). Qed.
Lemma lem5219866 (x : type1021) (s : real -> Prop) : ((term415 x s) = (term416 x s)) = ((term409 x s) = (term426 x s)).
Proof. exact (MK_COMB (@lem5219859 x s) (@lem5219865 x s)). Qed.
Lemma lem5219867 (x : type1021) (s : real -> Prop) : (term409 x s) = (term426 x s).
Proof. exact (EQ_MP (@lem5219866 x s) (@lem5219851 x s)). Qed.
Lemma lem5219868 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5219869 (x : type1021) (s : real -> Prop) : (term410 x s) = (term427 x s).
Proof. exact (MK_COMB (@lem5219868) (@lem5219867 x s)). Qed.
Lemma lem5219871 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term356 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5219872 (P : real -> Prop) (Q : real -> Prop) : (term358 P Q) = (term357 P Q).
Proof. exact (@lem5219871 real P Q). Qed.
Lemma lem5219873 (x : type1021) (s : real -> Prop) : (term428 x s) = (term429 x s).
Proof. exact (@lem5219872 (term181 s) (term403 x s)). Qed.
Lemma lem5219874 (s : real -> Prop) (b : real) : (term430 s b) = (term180 s b).
Proof. exact (eq_refl (term430 s b)). Qed.
Lemma lem5219875 (s : real -> Prop) : (term431 s) = (term181 s).
Proof. exact (fun_ext (fun b : real => @lem5219874 s b)). Qed.
Lemma lem5219876 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219877 (s : real -> Prop) : (term432 s) = (term182 s).
Proof. exact (MK_COMB (@lem5219876) (@lem5219875 s)). Qed.
Lemma lem5219878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219879 (s : real -> Prop) : (term433 s) = (term189 s).
Proof. exact (MK_COMB (@lem5219878) (@lem5219877 s)). Qed.
Lemma lem5219880 (x : type1021) (b : real) (s : real -> Prop) : (term434 x s b) = (term402 x b s).
Proof. exact (eq_refl (term434 x s b)). Qed.
Lemma lem5219881 (x : type1021) (s : real -> Prop) : (term435 x s) = (term403 x s).
Proof. exact (fun_ext (fun b : real => @lem5219880 x b s)). Qed.
Lemma lem5219882 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219883 (x : type1021) (s : real -> Prop) : (term436 x s) = (term404 x s).
Proof. exact (MK_COMB (@lem5219882) (@lem5219881 x s)). Qed.
Lemma lem5219884 (x : type1021) (s : real -> Prop) : (term428 x s) = (term405 x s).
Proof. exact (MK_COMB (@lem5219879 s) (@lem5219883 x s)). Qed.
Lemma lem5219885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5219886 (x : type1021) (s : real -> Prop) : (term437 x s) = (term438 x s).
Proof. exact (MK_COMB (@lem5219885) (@lem5219884 x s)). Qed.
Lemma lem5219887 (s : real -> Prop) (b : real) : (term430 s b) = (term180 s b).
Proof. exact (eq_refl (term430 s b)). Qed.
Lemma lem5219888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5219889 (s : real -> Prop) (b : real) : (term439 s b) = (term440 s b).
Proof. exact (MK_COMB (@lem5219888) (@lem5219887 s b)). Qed.
Lemma lem5219890 (x : type1021) (b : real) (s : real -> Prop) : (term434 x s b) = (term402 x b s).
Proof. exact (eq_refl (term434 x s b)). Qed.
Lemma lem5219891 (x : type1021) (b : real) (s : real -> Prop) : (term441 x s b) = (term442 x b s).
Proof. exact (MK_COMB (@lem5219889 s b) (@lem5219890 x b s)). Qed.
Lemma lem5219892 (x : type1021) (s : real -> Prop) : (term443 x s) = (term444 x s).
Proof. exact (fun_ext (fun b : real => @lem5219891 x b s)). Qed.
Lemma lem5219893 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219894 (x : type1021) (s : real -> Prop) : (term429 x s) = (term445 x s).
Proof. exact (MK_COMB (@lem5219893) (@lem5219892 x s)). Qed.
Lemma lem5219895 (x : type1021) (s : real -> Prop) : ((term428 x s) = (term429 x s)) = ((term405 x s) = (term445 x s)).
Proof. exact (MK_COMB (@lem5219886 x s) (@lem5219894 x s)). Qed.
Lemma lem5219896 (x : type1021) (s : real -> Prop) : (term405 x s) = (term445 x s).
Proof. exact (EQ_MP (@lem5219895 x s) (@lem5219873 x s)). Qed.
Lemma lem5219899 (x : type1021) (s : real -> Prop) : (term446 x s) = (term446 x s).
Proof. exact (eq_refl (term446 x s)). Qed.
Lemma lem5219900 (x : type1021) (s : real -> Prop) : (term446 x s) = ((term405 x s) = (term445 x s)).
Proof. exact (eq_refl (term446 x s)). Qed.
Lemma lem5219901 (x : type1021) (s : real -> Prop) : (term447 x s) = (term447 x s).
Proof. exact (eq_refl (term447 x s)). Qed.
Lemma lem5219902 (x : type1021) (s : real -> Prop) : ((term446 x s) = (term446 x s)) = ((term446 x s) = ((term405 x s) = (term445 x s))).
Proof. exact (MK_COMB (@lem5219901 x s) (@lem5219900 x s)). Qed.
Lemma lem5219903 (x : type1021) (s : real -> Prop) : (term446 x s) = ((term405 x s) = (term445 x s)).
Proof. exact (eq_refl (term446 x s)). Qed.
Lemma lem5219904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5219905 (x : type1021) (s : real -> Prop) : (term447 x s) = (term448 x s).
Proof. exact (MK_COMB (@lem5219904) (@lem5219903 x s)). Qed.
Lemma lem5219906 (x : type1021) (s : real -> Prop) : ((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s)).
Proof. exact (eq_refl ((term405 x s) = (term445 x s))). Qed.
Lemma lem5219907 (x : type1021) (s : real -> Prop) : ((term446 x s) = ((term405 x s) = (term445 x s))) = (((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s))).
Proof. exact (MK_COMB (@lem5219905 x s) (@lem5219906 x s)). Qed.
Lemma lem5219908 (x : type1021) (s : real -> Prop) : ((term446 x s) = (term446 x s)) = (((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s))).
Proof. exact (TRANS (@lem5219902 x s) (@lem5219907 x s)). Qed.
Lemma lem5219909 (x : type1021) (s : real -> Prop) : ((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s)).
Proof. exact (EQ_MP (@lem5219908 x s) (@lem5219899 x s)). Qed.
Lemma lem5219910 (x : type1021) (s : real -> Prop) : (term405 x s) = (term445 x s).
Proof. exact (EQ_MP (@lem5219909 x s) (@lem5219896 x s)). Qed.
Lemma lem5219911 (x : type1021) (s : real -> Prop) : (term334 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5219869 x s) (@lem5219910 x s)). Qed.
Lemma lem5219913 {A : Type'} (P : A -> Prop) (Q : Prop) : (term450 A P Q) = (term451 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5219914 (P : real -> Prop) (Q : Prop) : (term452 P Q) = (term453 P Q).
Proof. exact (@lem5219913 real P Q). Qed.
Lemma lem5219915 (x : type1021) (s : real -> Prop) : (term454 x s) = (term455 x s).
Proof. exact (@lem5219914 (term425 x s) (term445 x s)). Qed.
Lemma lem5219916 (x : type1021) (s : real -> Prop) (b : real) : (term456 x s b) = (term423 x s b).
Proof. exact (eq_refl (term456 x s b)). Qed.
Lemma lem5219917 (x : type1021) (s : real -> Prop) : (term457 x s) = (term425 x s).
Proof. exact (fun_ext (fun b : real => @lem5219916 x s b)). Qed.
Lemma lem5219918 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219919 (x : type1021) (s : real -> Prop) : (term458 x s) = (term426 x s).
Proof. exact (MK_COMB (@lem5219918) (@lem5219917 x s)). Qed.
Lemma lem5219920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5219921 (x : type1021) (s : real -> Prop) : (term459 x s) = (term427 x s).
Proof. exact (MK_COMB (@lem5219920) (@lem5219919 x s)). Qed.
Lemma lem5219922 (x : type1021) (s : real -> Prop) : (term445 x s) = (term445 x s).
Proof. exact (eq_refl (term445 x s)). Qed.
Lemma lem5219923 (x : type1021) (s : real -> Prop) : (term454 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5219921 x s) (@lem5219922 x s)). Qed.
Lemma lem5219924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5219925 (x : type1021) (s : real -> Prop) : (term460 x s) = (term461 x s).
Proof. exact (MK_COMB (@lem5219924) (@lem5219923 x s)). Qed.
Lemma lem5219926 (x : type1021) (s : real -> Prop) (b : real) : (term456 x s b) = (term423 x s b).
Proof. exact (eq_refl (term456 x s b)). Qed.
Lemma lem5219927 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5219928 (x : type1021) (s : real -> Prop) (b : real) : (term462 x s b) = (term463 x s b).
Proof. exact (MK_COMB (@lem5219927) (@lem5219926 x s b)). Qed.
Lemma lem5219929 (x : type1021) (s : real -> Prop) : (term445 x s) = (term445 x s).
Proof. exact (eq_refl (term445 x s)). Qed.
Lemma lem5219930 (b : real) (x : type1021) (s : real -> Prop) : (term464 b x s) = (term465 b x s).
Proof. exact (MK_COMB (@lem5219928 x s b) (@lem5219929 x s)). Qed.
Lemma lem5219931 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (fun_ext (fun b : real => @lem5219930 b x s)). Qed.
Lemma lem5219932 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219933 (x : type1021) (s : real -> Prop) : (term455 x s) = (term468 x s).
Proof. exact (MK_COMB (@lem5219932) (@lem5219931 x s)). Qed.
Lemma lem5219934 (x : type1021) (s : real -> Prop) : ((term454 x s) = (term455 x s)) = ((term449 x s) = (term468 x s)).
Proof. exact (MK_COMB (@lem5219925 x s) (@lem5219933 x s)). Qed.
Lemma lem5219935 (x : type1021) (s : real -> Prop) : (term449 x s) = (term468 x s).
Proof. exact (EQ_MP (@lem5219934 x s) (@lem5219915 x s)). Qed.
Lemma lem5219937 {A : Type'} (P : Prop) (Q : A -> Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5219938 (P : Prop) (Q : real -> Prop) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem5219937 real P Q). Qed.
Lemma lem5219939 (b : real) (x : type1021) (s : real -> Prop) : (term469 b x s) = (term470 b x s).
Proof. exact (@lem5219938 (term423 x s b) (term444 x s)). Qed.
Lemma lem5219940 (x : type1021) (b : real) (s : real -> Prop) : (term471 x s b) = (term442 x b s).
Proof. exact (eq_refl (term471 x s b)). Qed.
Lemma lem5219941 (x : type1021) (s : real -> Prop) : (term472 x s) = (term444 x s).
Proof. exact (fun_ext (fun b : real => @lem5219940 x b s)). Qed.
Lemma lem5219942 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219943 (x : type1021) (s : real -> Prop) : (term473 x s) = (term445 x s).
Proof. exact (MK_COMB (@lem5219942) (@lem5219941 x s)). Qed.
Lemma lem5219944 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term463 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5219945 (b : real) (x : type1021) (s : real -> Prop) : (term469 b x s) = (term465 b x s).
Proof. exact (MK_COMB (@lem5219944 x s b) (@lem5219943 x s)). Qed.
Lemma lem5219946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5219947 (b : real) (x : type1021) (s : real -> Prop) : (term474 b x s) = (term475 b x s).
Proof. exact (MK_COMB (@lem5219946) (@lem5219945 b x s)). Qed.
Lemma lem5219948 (x : type1021) (b' : real) (s : real -> Prop) : (term471 x s b') = (term442 x b' s).
Proof. exact (eq_refl (term471 x s b')). Qed.
Lemma lem5219949 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term463 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5219950 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term476 b x s b') = (term477 b x b' s).
Proof. exact (MK_COMB (@lem5219949 x s b) (@lem5219948 x b' s)). Qed.
Lemma lem5219951 (b : real) (x : type1021) (s : real -> Prop) : (term478 b x s) = (term479 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5219950 b x b' s)). Qed.
Lemma lem5219952 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219953 (b : real) (x : type1021) (s : real -> Prop) : (term470 b x s) = (term480 b x s).
Proof. exact (MK_COMB (@lem5219952) (@lem5219951 b x s)). Qed.
Lemma lem5219954 (b : real) (x : type1021) (s : real -> Prop) : ((term469 b x s) = (term470 b x s)) = ((term465 b x s) = (term480 b x s)).
Proof. exact (MK_COMB (@lem5219947 b x s) (@lem5219953 b x s)). Qed.
Lemma lem5219955 (b : real) (x : type1021) (s : real -> Prop) : (term465 b x s) = (term480 b x s).
Proof. exact (EQ_MP (@lem5219954 b x s) (@lem5219939 b x s)). Qed.
Lemma lem5219956 (x : type1021) (s : real -> Prop) : (term467 x s) = (term481 x s).
Proof. exact (fun_ext (fun b : real => @lem5219955 b x s)). Qed.
Lemma lem5219957 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5219958 (x : type1021) (s : real -> Prop) : (term468 x s) = (term482 x s).
Proof. exact (MK_COMB (@lem5219957) (@lem5219956 x s)). Qed.
Lemma lem5219959 (x : type1021) (s : real -> Prop) : (term449 x s) = (term482 x s).
Proof. exact (TRANS (@lem5219935 x s) (@lem5219958 x s)). Qed.
Lemma lem5219960 (x : type1021) (s : real -> Prop) : (term334 x s) = (term482 x s).
Proof. exact (TRANS (@lem5219911 x s) (@lem5219959 x s)). Qed.
Lemma lem5219961 (x : type1021) : (term336 x) = (term483 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5219960 x s)). Qed.
Lemma lem5219962 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5219963 (x : type1021) : (term338 x) = (term484 x).
Proof. exact (MK_COMB (@lem5219962) (@lem5219961 x)). Qed.
Lemma lem5219980 (x : type1021) (b' : real) (s : real -> Prop) : (term402 x b' s) = (term485 x b' s).
Proof. exact (@lem19699 (term486 x b' s) (term487 x s b') (term46 b' s)). Qed.
Lemma lem5219989 (s : real -> Prop) (b' : real) : (term440 s b') = (term440 s b').
Proof. exact (eq_refl (term440 s b')). Qed.
Lemma lem5219990 (x : type1021) (b' : real) (s : real -> Prop) : (term442 x b' s) = (term488 x b' s).
Proof. exact (MK_COMB (@lem5219989 s b') (@lem5219980 x b' s)). Qed.
Lemma lem5220007 (x : type1021) (s : real -> Prop) (b : real) : (term423 x s b) = (term489 x s b).
Proof. exact (@lem19490 (term486 x b s) (s = (@EMPTY real)) (term487 x s b)). Qed.
Lemma lem5220008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5220009 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term490 x s b).
Proof. exact (MK_COMB (@lem5220008) (@lem5220007 x s b)). Qed.
Lemma lem5220010 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term477 b x b' s) = (term491 b x b' s).
Proof. exact (MK_COMB (@lem5220009 x s b) (@lem5219990 x b' s)). Qed.
Lemma lem5220011 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term491 b x b' s) = (term492 b x b' s).
Proof. exact (@lem19490 (term180 s b') (term489 x s b) (term485 x b' s)). Qed.
Lemma lem5220012 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term493 b x b' s) = (term494 b x b' s).
Proof. exact (@lem19490 (term495 x b' s) (term489 x s b) (term496 x b' s)). Qed.
Lemma lem5220019 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term497 b x b' s) = (term498 b x b' s).
Proof. exact (@lem19699 (term499 x b s) (term500 x s b) (term496 x b' s)). Qed.
Lemma lem5220026 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term501 b x b' s) = (term502 b x b' s).
Proof. exact (@lem19699 (term499 x b s) (term500 x s b) (term495 x b' s)). Qed.
Lemma lem5220027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5220028 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term503 b x b' s) = (term504 b x b' s).
Proof. exact (MK_COMB (@lem5220027) (@lem5220026 b x b' s)). Qed.
Lemma lem5220029 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term494 b x b' s) = (term505 b x b' s).
Proof. exact (MK_COMB (@lem5220028 b x b' s) (@lem5220019 b x b' s)). Qed.
Lemma lem5220030 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term493 b x b' s) = (term505 b x b' s).
Proof. exact (TRANS (@lem5220012 b x b' s) (@lem5220029 b x b' s)). Qed.
Lemma lem5220037 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term506 x b s b') = (term507 x b s b').
Proof. exact (@lem19699 (term499 x b s) (term500 x s b) (term180 s b')). Qed.
Lemma lem5220038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5220039 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term508 x b s b') = (term509 x b s b').
Proof. exact (MK_COMB (@lem5220038) (@lem5220037 x b s b')). Qed.
Lemma lem5220040 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term492 b x b' s) = (term510 b x b' s).
Proof. exact (MK_COMB (@lem5220039 x b s b') (@lem5220030 b x b' s)). Qed.
Lemma lem5220041 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term491 b x b' s) = (term510 b x b' s).
Proof. exact (TRANS (@lem5220011 b x b' s) (@lem5220040 b x b' s)). Qed.
Lemma lem5220042 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term477 b x b' s) = (term510 b x b' s).
Proof. exact (TRANS (@lem5220010 b x b' s) (@lem5220041 b x b' s)). Qed.
Lemma lem5220043 (b : real) (x : type1021) (s : real -> Prop) : (term479 b x s) = (term511 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5220042 b x b' s)). Qed.
Lemma lem5220044 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5220045 (b : real) (x : type1021) (s : real -> Prop) : (term480 b x s) = (term512 b x s).
Proof. exact (MK_COMB (@lem5220044) (@lem5220043 b x s)). Qed.
Lemma lem5220046 (x : type1021) (s : real -> Prop) : (term481 x s) = (term513 x s).
Proof. exact (fun_ext (fun b : real => @lem5220045 b x s)). Qed.
Lemma lem5220047 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5220048 (x : type1021) (s : real -> Prop) : (term482 x s) = (term514 x s).
Proof. exact (MK_COMB (@lem5220047) (@lem5220046 x s)). Qed.
Lemma lem5220049 (x : type1021) : (term483 x) = (term515 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5220048 x s)). Qed.
Lemma lem5220050 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5220051 (x : type1021) : (term484 x) = (term516 x).
Proof. exact (MK_COMB (@lem5220050) (@lem5220049 x)). Qed.
Lemma lem5220052 (x : type1021) : (term338 x) = (term516 x).
Proof. exact (TRANS (@lem5219963 x) (@lem5220051 x)). Qed.
Lemma lem5220053 (x : type1021) (h1 : term338 x) : term516 x.
Proof. exact (EQ_MP (@lem5220052 x) (@lem5219461 x h1)). Qed.
Lemma lem5220065 (s : real -> Prop) (b : real) (x : real) : (term73 s b x) = (term73 s b x).
Proof. exact (eq_refl (term73 s b x)). Qed.
Lemma lem5220066 (s : real -> Prop) (b : real) : (term74 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5220065 s b x)). Qed.
Lemma lem5220067 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5220069 (s : real -> Prop) (b : real) : (term75 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5220067) (@lem5220066 s b)). Qed.
Lemma lem5220070 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term75 s b.
Proof. exact (EQ_MP (@lem5220069 s b) (@lem5219523 b s x' h1)). Qed.
Lemma lem5220141 (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term517 x _68312.
Proof. exact (@lem5219754 x h1 _68312). Qed.
Lemma lem5220142 (x : type1021) (_68312 : real -> Prop) : (term517 x _68312) = (term514 x _68312).
Proof. exact (eq_refl (term517 x _68312)). Qed.
Lemma lem5220143 (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term514 x _68312.
Proof. exact (EQ_MP (@lem5220142 x _68312) (@lem5220141 _68312 x h1)). Qed.
Lemma lem5220144 (_68312 : real -> Prop) (_68313 : real) (x : type1021) (h1 : term338 x) : term518 x _68312 _68313.
Proof. exact (@lem5220143 _68312 x h1 _68313). Qed.
Lemma lem5220145 (_68313 : real) (x : type1021) (_68312 : real -> Prop) : (term518 x _68312 _68313) = (term512 _68313 x _68312).
Proof. exact (eq_refl (term518 x _68312 _68313)). Qed.
Lemma lem5220146 (_68313 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term512 _68313 x _68312.
Proof. exact (EQ_MP (@lem5220145 _68313 x _68312) (@lem5220144 _68312 _68313 x h1)). Qed.
Lemma lem5220147 (_68313 : real) (_68312 : real -> Prop) (_68314 : real) (x : type1021) (h1 : term338 x) : term519 _68313 x _68312 _68314.
Proof. exact (@lem5220146 _68313 _68312 x h1 _68314). Qed.
Lemma lem5220148 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term519 _68313 x _68312 _68314) = (term510 _68313 x _68314 _68312).
Proof. exact (eq_refl (term519 _68313 x _68312 _68314)). Qed.
Lemma lem5220149 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term510 _68313 x _68314 _68312.
Proof. exact (EQ_MP (@lem5220148 _68313 x _68314 _68312) (@lem5220147 _68313 _68312 _68314 x h1)). Qed.
Lemma lem5220150 (_68315 : real) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term520 s b _68315.
Proof. exact (@lem5219771 b s x' h1 _68315). Qed.
Lemma lem5220151 (s : real -> Prop) (b : real) (_68315 : real) : (term520 s b _68315) = (term73 s b _68315).
Proof. exact (eq_refl (term520 s b _68315)). Qed.
Lemma lem5220159 (_68318 : real) (h1 : term21) : term388 _68318.
Proof. exact (@lem5219819 h1 _68318). Qed.
Lemma lem5220160 (_68318 : real) : (term388 _68318) = (term378 _68318).
Proof. exact (eq_refl (term388 _68318)). Qed.
Lemma lem5220161 (_68318 : real) (h1 : term21) : term378 _68318.
Proof. exact (EQ_MP (@lem5220160 _68318) (@lem5220159 _68318 h1)). Qed.
Lemma lem5220162 (_68318 : real) (_68319 : real) (h1 : term21) : term366 _68318 _68319.
Proof. exact (@lem5220161 _68318 h1 _68319). Qed.
Lemma lem5220163 (_68318 : real) (_68319 : real) : (term366 _68318 _68319) = (term347 _68318 _68319).
Proof. exact (eq_refl (term366 _68318 _68319)). Qed.
Lemma lem5220164 (_68318 : real) (_68319 : real) (h1 : term21) : term347 _68318 _68319.
Proof. exact (EQ_MP (@lem5220163 _68318 _68319) (@lem5220162 _68318 _68319 h1)). Qed.
Lemma lem5220171 (_68322 : real -> Prop) (x : type1021) (h1 : term338 x) : term517 x _68322.
Proof. exact (@lem5220053 x h1 _68322). Qed.
Lemma lem5220172 (x : type1021) (_68322 : real -> Prop) : (term517 x _68322) = (term514 x _68322).
Proof. exact (eq_refl (term517 x _68322)). Qed.
Lemma lem5220173 (_68322 : real -> Prop) (x : type1021) (h1 : term338 x) : term514 x _68322.
Proof. exact (EQ_MP (@lem5220172 x _68322) (@lem5220171 _68322 x h1)). Qed.
Lemma lem5220174 (_68322 : real -> Prop) (_68323 : real) (x : type1021) (h1 : term338 x) : term518 x _68322 _68323.
Proof. exact (@lem5220173 _68322 x h1 _68323). Qed.
Lemma lem5220175 (_68323 : real) (x : type1021) (_68322 : real -> Prop) : (term518 x _68322 _68323) = (term512 _68323 x _68322).
Proof. exact (eq_refl (term518 x _68322 _68323)). Qed.
Lemma lem5220176 (_68323 : real) (_68322 : real -> Prop) (x : type1021) (h1 : term338 x) : term512 _68323 x _68322.
Proof. exact (EQ_MP (@lem5220175 _68323 x _68322) (@lem5220174 _68322 _68323 x h1)). Qed.
Lemma lem5220177 (_68323 : real) (_68322 : real -> Prop) (_68324 : real) (x : type1021) (h1 : term338 x) : term519 _68323 x _68322 _68324.
Proof. exact (@lem5220176 _68323 _68322 x h1 _68324). Qed.
Lemma lem5220178 (_68323 : real) (x : type1021) (_68324 : real) (_68322 : real -> Prop) : (term519 _68323 x _68322 _68324) = (term510 _68323 x _68324 _68322).
Proof. exact (eq_refl (term519 _68323 x _68322 _68324)). Qed.
Lemma lem5220179 (_68323 : real) (_68324 : real) (_68322 : real -> Prop) (x : type1021) (h1 : term338 x) : term510 _68323 x _68324 _68322.
Proof. exact (EQ_MP (@lem5220178 _68323 x _68324 _68322) (@lem5220177 _68323 _68322 _68324 x h1)). Qed.
Lemma lem5220180 (_68325 : real) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term520 s b _68325.
Proof. exact (@lem5220070 b s x' h1 _68325). Qed.
Lemma lem5220181 (s : real -> Prop) (b : real) (_68325 : real) : (term520 s b _68325) = (term73 s b _68325).
Proof. exact (eq_refl (term520 s b _68325)). Qed.
Lemma lem5220197 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term505 _68313 x _68314 _68312.
Proof. exact (proj2 (@lem5220149 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220198 (_68313 : real) (_68312 : real -> Prop) (_68314 : real) (x : type1021) (h1 : term338 x) : term507 x _68313 _68312 _68314.
Proof. exact (proj1 (@lem5220149 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220199 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term498 _68313 x _68314 _68312.
Proof. exact (proj2 (@lem5220197 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220200 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term502 _68313 x _68314 _68312.
Proof. exact (proj1 (@lem5220197 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220201 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term521 _68313 x _68314 _68312.
Proof. exact (proj2 (@lem5220199 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220203 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term522 _68313 x _68314 _68312.
Proof. exact (proj2 (@lem5220200 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220204 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term523 _68313 x _68314 _68312.
Proof. exact (proj1 (@lem5220200 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220205 (_68313 : real) (_68312 : real -> Prop) (_68314 : real) (x : type1021) (h1 : term338 x) : term524 x _68313 _68312 _68314.
Proof. exact (proj2 (@lem5220198 _68313 _68312 _68314 x h1)). Qed.
Lemma lem5220206 (_68313 : real) (_68312 : real -> Prop) (_68314 : real) (x : type1021) (h1 : term338 x) : term525 x _68313 _68312 _68314.
Proof. exact (proj1 (@lem5220198 _68313 _68312 _68314 x h1)). Qed.
Lemma lem5220210 (_68323 : real) (_68322 : real -> Prop) (_68324 : real) (x : type1021) (h1 : term338 x) : term507 x _68323 _68322 _68324.
Proof. exact (proj1 (@lem5220179 _68323 _68324 _68322 x h1)). Qed.
Lemma lem5220217 (_68323 : real) (_68322 : real -> Prop) (_68324 : real) (x : type1021) (h1 : term338 x) : term524 x _68323 _68322 _68324.
Proof. exact (proj2 (@lem5220210 _68323 _68322 _68324 x h1)). Qed.
Lemma lem5220218 (_68323 : real) (_68322 : real -> Prop) (_68324 : real) (x : type1021) (h1 : term338 x) : term525 x _68323 _68322 _68324.
Proof. exact (proj1 (@lem5220210 _68323 _68322 _68324 x h1)). Qed.
Lemma lem5220232 (_68315 : real) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term73 s b _68315.
Proof. exact (EQ_MP (@lem5220151 s b _68315) (@lem5220150 _68315 b s x' h1)). Qed.
Lemma lem5220243 (_68318 : real) (_68319 : real) : (term347 _68318 _68319) = (term526 _68318 _68319).
Proof. exact (@lem5217591 (term527 _68318 _68319) (term527 _68319 _68318) (_68318 = _68319)). Qed.
Lemma lem5220244 (_68318 : real) (_68319 : real) (h1 : term21) : term526 _68318 _68319.
Proof. exact (EQ_MP (@lem5220243 _68318 _68319) (@lem5220164 _68318 _68319 h1)). Qed.
Lemma lem5220250 (s : real -> Prop) (h1 : term106 s) : term106 s.
Proof. exact (h1). Qed.
Lemma lem5220293 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term521 _68313 x _68314 _68312) = (term528 _68313 x _68314 _68312).
Proof. exact (@lem5217591 (_68312 = (@EMPTY real)) (term487 x _68312 _68313) (term496 x _68314 _68312)). Qed.
Lemma lem5220294 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term528 _68313 x _68314 _68312.
Proof. exact (EQ_MP (@lem5220293 _68313 x _68314 _68312) (@lem5220201 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220309 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term523 _68313 x _68314 _68312) = (term529 _68313 x _68314 _68312).
Proof. exact (@lem5217591 (_68312 = (@EMPTY real)) (term486 x _68313 _68312) (term495 x _68314 _68312)). Qed.
Lemma lem5220310 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term529 _68313 x _68314 _68312.
Proof. exact (EQ_MP (@lem5220309 _68313 x _68314 _68312) (@lem5220204 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220325 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term522 _68313 x _68314 _68312) = (term530 _68313 x _68314 _68312).
Proof. exact (@lem5217591 (_68312 = (@EMPTY real)) (term487 x _68312 _68313) (term495 x _68314 _68312)). Qed.
Lemma lem5220326 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term530 _68313 x _68314 _68312.
Proof. exact (EQ_MP (@lem5220325 _68313 x _68314 _68312) (@lem5220203 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220341 (x : type1021) (_68313 : real) (_68312 : real -> Prop) (_68314 : real) : (term525 x _68313 _68312 _68314) = (term531 x _68313 _68312 _68314).
Proof. exact (@lem5217591 (_68312 = (@EMPTY real)) (term486 x _68313 _68312) (term180 _68312 _68314)). Qed.
Lemma lem5220342 (_68313 : real) (_68312 : real -> Prop) (_68314 : real) (x : type1021) (h1 : term338 x) : term531 x _68313 _68312 _68314.
Proof. exact (EQ_MP (@lem5220341 x _68313 _68312 _68314) (@lem5220206 _68313 _68312 _68314 x h1)). Qed.
Lemma lem5220357 (x : type1021) (_68313 : real) (_68312 : real -> Prop) (_68314 : real) : (term524 x _68313 _68312 _68314) = (term532 x _68313 _68312 _68314).
Proof. exact (@lem5217591 (_68312 = (@EMPTY real)) (term487 x _68312 _68313) (term180 _68312 _68314)). Qed.
Lemma lem5220358 (_68313 : real) (_68312 : real -> Prop) (_68314 : real) (x : type1021) (h1 : term338 x) : term532 x _68313 _68312 _68314.
Proof. exact (EQ_MP (@lem5220357 x _68313 _68312 _68314) (@lem5220205 _68313 _68312 _68314 x h1)). Qed.
Lemma lem5220372 (_68325 : real) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term73 s b _68325.
Proof. exact (EQ_MP (@lem5220181 s b _68325) (@lem5220180 _68325 b s x' h1)). Qed.
Lemma lem5220392 (s : real -> Prop) (x' : real) (h1 : term80 s x') : term533 s x'.
Proof. exact (proj2 (@lem5219530 s x' h1)). Qed.
Lemma lem5220483 (x : type1021) (_68323 : real) (_68322 : real -> Prop) (_68324 : real) : (term525 x _68323 _68322 _68324) = (term531 x _68323 _68322 _68324).
Proof. exact (@lem5217591 (_68322 = (@EMPTY real)) (term486 x _68323 _68322) (term180 _68322 _68324)). Qed.
Lemma lem5220484 (_68323 : real) (_68322 : real -> Prop) (_68324 : real) (x : type1021) (h1 : term338 x) : term531 x _68323 _68322 _68324.
Proof. exact (EQ_MP (@lem5220483 x _68323 _68322 _68324) (@lem5220218 _68323 _68322 _68324 x h1)). Qed.
Lemma lem5220499 (x : type1021) (_68323 : real) (_68322 : real -> Prop) (_68324 : real) : (term524 x _68323 _68322 _68324) = (term532 x _68323 _68322 _68324).
Proof. exact (@lem5217591 (_68322 = (@EMPTY real)) (term487 x _68322 _68323) (term180 _68322 _68324)). Qed.
Lemma lem5220500 (_68323 : real) (_68322 : real -> Prop) (_68324 : real) (x : type1021) (h1 : term338 x) : term532 x _68323 _68322 _68324.
Proof. exact (EQ_MP (@lem5220499 x _68323 _68322 _68324) (@lem5220217 _68323 _68322 _68324 x h1)). Qed.
Lemma lem5220513 : (@IN real) = (@IN real).
Proof. exact (eq_refl (@IN real)). Qed.
Lemma lem5220514 (_68332 : real) (_68334 : real) (h1 : _68332 = _68334) : _68332 = _68334.
Proof. exact (h1). Qed.
Lemma lem5220515 (_68333 : real -> Prop) (_68335 : real -> Prop) (h1 : _68333 = _68335) : _68333 = _68335.
Proof. exact (h1). Qed.
Lemma lem5220516 (_68332 : real) (_68334 : real) (h1 : _68332 = _68334) : (@IN real _68332) = (@IN real _68334).
Proof. exact (MK_COMB (@lem5220513) (@lem5220514 _68332 _68334 h1)). Qed.
Lemma lem5220517 (_68333 : real -> Prop) (_68335 : real -> Prop) (_68332 : real) (_68334 : real) (h1 : _68333 = _68335) (h2 : _68332 = _68334) : (@IN real _68332 _68333) = (@IN real _68334 _68335).
Proof. exact (MK_COMB (@lem5220516 _68332 _68334 h2) (@lem5220515 _68333 _68335 h1)). Qed.
Lemma lem5220519 (b : Prop) (a : Prop) : term534 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5220520 (_68334 : real) (_68335 : real -> Prop) (_68332 : real) (_68333 : real -> Prop) : term535 _68334 _68335 _68332 _68333.
Proof. exact (@lem5220519 (@IN real _68334 _68335) (@IN real _68332 _68333)). Qed.
Lemma lem5220521 (_68333 : real -> Prop) (_68335 : real -> Prop) (_68332 : real) (_68334 : real) (h1 : _68333 = _68335) (h2 : _68332 = _68334) : term536 _68334 _68335 _68332 _68333.
Proof. exact (@lem5220520 _68334 _68335 _68332 _68333 (@lem5220517 _68333 _68335 _68332 _68334 h1 h2)). Qed.
Lemma lem5220522 (_68334 : real) (_68332 : real) (_68333 : real -> Prop) (_68335 : real -> Prop) (h1 : _68333 = _68335) : term537 _68334 _68335 _68332 _68333.
Proof. exact (fun h0 : _68332 = _68334 => @lem5220521 _68333 _68335 _68332 _68334 h1 h0). Qed.
Lemma lem5220524 (a : Prop) (b : Prop) : (a -> b) = (term538 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5220525 (_68334 : real) (_68335 : real -> Prop) (_68332 : real) (_68333 : real -> Prop) : (term537 _68334 _68335 _68332 _68333) = (term539 _68334 _68335 _68332 _68333).
Proof. exact (@lem5220524 (_68332 = _68334) (term536 _68334 _68335 _68332 _68333)). Qed.
Lemma lem5220526 (_68334 : real) (_68332 : real) (_68333 : real -> Prop) (_68335 : real -> Prop) (h1 : _68333 = _68335) : term539 _68334 _68335 _68332 _68333.
Proof. exact (EQ_MP (@lem5220525 _68334 _68335 _68332 _68333) (@lem5220522 _68334 _68332 _68333 _68335 h1)). Qed.
Lemma lem5220527 (_68334 : real) (_68335 : real -> Prop) (_68332 : real) (_68333 : real -> Prop) : term540 _68334 _68335 _68332 _68333.
Proof. exact (fun h0 : _68333 = _68335 => @lem5220526 _68334 _68332 _68333 _68335 h0). Qed.
Lemma lem5220529 (a : Prop) (b : Prop) : (a -> b) = (term538 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5220530 (_68334 : real) (_68335 : real -> Prop) (_68332 : real) (_68333 : real -> Prop) : (term540 _68334 _68335 _68332 _68333) = (term541 _68334 _68335 _68332 _68333).
Proof. exact (@lem5220529 (_68333 = _68335) (term539 _68334 _68335 _68332 _68333)). Qed.
Lemma lem5220531 (_68334 : real) (_68335 : real -> Prop) (_68332 : real) (_68333 : real -> Prop) : term541 _68334 _68335 _68332 _68333.
Proof. exact (EQ_MP (@lem5220530 _68334 _68335 _68332 _68333) (@lem5220527 _68334 _68335 _68332 _68333)). Qed.
Lemma lem5220579 (x : real -> Prop) : x = x.
Proof. exact (@lem21386 (real -> Prop) x). Qed.
Lemma lem5220580 (s : real -> Prop) : s = s.
Proof. exact (@lem5220579 s). Qed.
Lemma lem5220581 (s : real -> Prop) : term542 s.
Proof. exact (fun h0 : term543 s => @lem5220580 s). Qed.
Lemma lem5220583 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5220584 (s : real -> Prop) : (term542 s) = (s = s).
Proof. exact (@lem5220583 (s = s)). Qed.
Lemma lem5220585 (s : real -> Prop) : s = s.
Proof. exact (EQ_MP (@lem5220584 s) (@lem5220581 s)). Qed.
Lemma lem5220587 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5219277 s h1)). Qed.
Lemma lem5220588 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5220587 s h1). Qed.
Lemma lem5220590 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5220591 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5220590 (s = (@EMPTY real))). Qed.
Lemma lem5220592 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5220591 s) (@lem5220588 s h1)). Qed.
Lemma lem5220594 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5219277 s h1)). Qed.
Lemma lem5220595 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5220594 s h1). Qed.
Lemma lem5220597 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5220598 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5220597 (s = (@EMPTY real))). Qed.
Lemma lem5220599 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5220598 s) (@lem5220595 s h1)). Qed.
Lemma lem5220602 (x : type1021) (b : real) (s : real -> Prop) (h1 : term547 x b s) : term547 x b s.
Proof. exact (h1). Qed.
Lemma lem5220603 (x : type1021) (b : real) (s : real -> Prop) (h1 : term547 x b s) : term548 x b s.
Proof. exact (fun h0 : term486 x b s => @lem5220602 x b s h1). Qed.
Lemma lem5220605 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5220606 (x : type1021) (b : real) (s : real -> Prop) : (term548 x b s) = (term547 x b s).
Proof. exact (@lem5220605 (term486 x b s)). Qed.
Lemma lem5220607 (x : type1021) (b : real) (s : real -> Prop) (h1 : term547 x b s) : term547 x b s.
Proof. exact (EQ_MP (@lem5220606 x b s) (@lem5220603 x b s h1)). Qed.
Lemma lem5220610 (b : real) (s : real -> Prop) (h1 : term549 b s) : term549 b s.
Proof. exact (h1). Qed.
Lemma lem5220611 (b : real) (s : real -> Prop) (h1 : term549 b s) : term550 b s.
Proof. exact (fun h0 : term46 b s => @lem5220610 b s h1). Qed.
Lemma lem5220613 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5220614 (b : real) (s : real -> Prop) : (term550 b s) = (term549 b s).
Proof. exact (@lem5220613 (term46 b s)). Qed.
Lemma lem5220615 (b : real) (s : real -> Prop) (h1 : term549 b s) : term549 b s.
Proof. exact (EQ_MP (@lem5220614 b s) (@lem5220611 b s h1)). Qed.
Lemma lem5220648 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5220649 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term551 x _68313 _68314 _68312) = (term552 x _68313 _68314 _68312).
Proof. exact (@lem5220648 (_68312 = (@EMPTY real)) (term486 x _68314 _68312) (term553 x _68313 _68314 _68312)). Qed.
Lemma lem5220665 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5220666 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term554 x _68313 _68314 _68312) = (term555 _68313 x _68314 _68312).
Proof. exact (@lem5220665 (term486 x _68313 _68312) (term486 x _68314 _68312) (term46 _68314 _68312)). Qed.
Lemma lem5220682 (_68312 : real -> Prop) : (term175 _68312) = (term175 _68312).
Proof. exact (eq_refl (term175 _68312)). Qed.
Lemma lem5220683 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term552 x _68313 _68314 _68312) = (term529 _68313 x _68314 _68312).
Proof. exact (MK_COMB (@lem5220682 _68312) (@lem5220666 _68313 x _68314 _68312)). Qed.
Lemma lem5220694 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term551 x _68313 _68314 _68312) = (term529 _68313 x _68314 _68312).
Proof. exact (TRANS (@lem5220649 x _68313 _68314 _68312) (@lem5220683 _68313 x _68314 _68312)). Qed.
Lemma lem5220695 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term556 _68313 x _68314 _68312) = (term556 _68313 x _68314 _68312).
Proof. exact (eq_refl (term556 _68313 x _68314 _68312)). Qed.
Lemma lem5220696 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : ((term529 _68313 x _68314 _68312) = (term551 x _68313 _68314 _68312)) = ((term529 _68313 x _68314 _68312) = (term529 _68313 x _68314 _68312)).
Proof. exact (MK_COMB (@lem5220695 _68313 x _68314 _68312) (@lem5220694 _68313 x _68314 _68312)). Qed.
Lemma lem5220698 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5220699 (x : Prop) : (x = x) = True.
Proof. exact (@lem5220698 Prop x). Qed.
Lemma lem5220700 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : ((term529 _68313 x _68314 _68312) = (term529 _68313 x _68314 _68312)) = True.
Proof. exact (@lem5220699 (term529 _68313 x _68314 _68312)). Qed.
Lemma lem5220701 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : ((term529 _68313 x _68314 _68312) = (term551 x _68313 _68314 _68312)) = True.
Proof. exact (TRANS (@lem5220696 _68313 x _68314 _68312) (@lem5220700 _68313 x _68314 _68312)). Qed.
Lemma lem5220702 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : True = ((term529 _68313 x _68314 _68312) = (term551 x _68313 _68314 _68312)).
Proof. exact (SYM (@lem5220701 x _68313 _68314 _68312)). Qed.
Lemma lem5220703 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term529 _68313 x _68314 _68312) = (term551 x _68313 _68314 _68312).
Proof. exact (EQ_MP (@lem5220702 x _68313 _68314 _68312) (@lem0)). Qed.
Lemma lem5220704 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term551 x _68313 _68314 _68312.
Proof. exact (EQ_MP (@lem5220703 x _68313 _68314 _68312) (@lem5220310 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220706 (b : Prop) (a : Prop) : (a \/ b) = (term557 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5220707 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term551 x _68313 _68314 _68312) = (term558 _68313 x _68314 _68312).
Proof. exact (@lem5220706 (term559 x _68313 _68314 _68312) (term486 x _68314 _68312)). Qed.
Lemma lem5220709 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5220710 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term562 x _68313 _68314 _68312) = (term563 x _68313 _68314 _68312).
Proof. exact (@lem5220709 (_68312 = (@EMPTY real)) (term553 x _68313 _68314 _68312)). Qed.
Lemma lem5220712 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5220713 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term564 x _68313 _68314 _68312) = (term565 x _68313 _68314 _68312).
Proof. exact (@lem5220712 (term486 x _68313 _68312) (term46 _68314 _68312)). Qed.
Lemma lem5220714 (_68312 : real -> Prop) : (term61 _68312) = (term61 _68312).
Proof. exact (eq_refl (term61 _68312)). Qed.
Lemma lem5220715 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term563 x _68313 _68314 _68312) = (term566 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5220714 _68312) (@lem5220713 x _68313 _68314 _68312)). Qed.
Lemma lem5220716 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term562 x _68313 _68314 _68312) = (term566 x _68313 _68314 _68312).
Proof. exact (TRANS (@lem5220710 x _68313 _68314 _68312) (@lem5220715 x _68313 _68314 _68312)). Qed.
Lemma lem5220717 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5220718 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term567 x _68313 _68314 _68312) = (term568 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5220717) (@lem5220716 x _68313 _68314 _68312)). Qed.
Lemma lem5220719 (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term486 x _68314 _68312) = (term486 x _68314 _68312).
Proof. exact (eq_refl (term486 x _68314 _68312)). Qed.
Lemma lem5220720 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term558 _68313 x _68314 _68312) = (term569 _68313 x _68314 _68312).
Proof. exact (MK_COMB (@lem5220718 x _68313 _68314 _68312) (@lem5220719 x _68314 _68312)). Qed.
Lemma lem5220721 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term551 x _68313 _68314 _68312) = (term569 _68313 x _68314 _68312).
Proof. exact (TRANS (@lem5220707 _68313 x _68314 _68312) (@lem5220720 _68313 x _68314 _68312)). Qed.
Lemma lem5220723 (x : type1021) (b : real) (s : real -> Prop) (h1 : term547 x b s) (h2 : term549 b s) : term570 x b s.
Proof. exact (conj (@lem5220607 x b s h1) (@lem5220615 b s h2)). Qed.
Lemma lem5220724 (x : type1021) (b : real) (s : real -> Prop) (h1 : term547 x b s) (h2 : term549 b s) (h3 : term9 s) : term571 x b s.
Proof. exact (conj (@lem5220599 s h3) (@lem5220723 x b s h1 h2)). Qed.
Lemma lem5220726 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term569 _68313 x _68314 _68312.
Proof. exact (EQ_MP (@lem5220721 _68313 x _68314 _68312) (@lem5220704 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220727 (b : real) (s : real -> Prop) (x : type1021) (h1 : term338 x) : term572 x b s.
Proof. exact (@lem5220726 b b s x h1). Qed.
Lemma lem5220730 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term547 x b s) (h3 : term549 b s) (h4 : term9 s) : term486 x b s.
Proof. exact (@lem5220727 b s x h1 (@lem5220724 x b s h2 h3 h4)). Qed.
Lemma lem5220731 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) : term573 x b s.
Proof. exact (fun h0 : term547 x b s => @lem5220730 x b s h1 h0 h2 h3). Qed.
Lemma lem5220733 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5220734 (x : type1021) (b : real) (s : real -> Prop) : (term573 x b s) = (term486 x b s).
Proof. exact (@lem5220733 (term486 x b s)). Qed.
Lemma lem5220735 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) : term486 x b s.
Proof. exact (EQ_MP (@lem5220734 x b s) (@lem5220731 x b s h1 h2 h3)). Qed.
Lemma lem5220741 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5220742 (b : real) (_68315 : real) (s : real -> Prop) : (term73 s b _68315) = (term574 b _68315 s).
Proof. exact (@lem5220741 (real_le b _68315) (term575 _68315 s)). Qed.
Lemma lem5220748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5220749 (b : real) (_68315 : real) (s : real -> Prop) : (term576 s b _68315) = (term577 b _68315 s).
Proof. exact (MK_COMB (@lem5220748) (@lem5220742 b _68315 s)). Qed.
Lemma lem5220755 (b : real) (_68315 : real) (s : real -> Prop) : (term574 b _68315 s) = (term574 b _68315 s).
Proof. exact (eq_refl (term574 b _68315 s)). Qed.
Lemma lem5220756 (b : real) (_68315 : real) (s : real -> Prop) : ((term73 s b _68315) = (term574 b _68315 s)) = ((term574 b _68315 s) = (term574 b _68315 s)).
Proof. exact (MK_COMB (@lem5220749 b _68315 s) (@lem5220755 b _68315 s)). Qed.
Lemma lem5220758 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5220759 (x : Prop) : (x = x) = True.
Proof. exact (@lem5220758 Prop x). Qed.
Lemma lem5220760 (b : real) (_68315 : real) (s : real -> Prop) : ((term574 b _68315 s) = (term574 b _68315 s)) = True.
Proof. exact (@lem5220759 (term574 b _68315 s)). Qed.
Lemma lem5220761 (b : real) (_68315 : real) (s : real -> Prop) : ((term73 s b _68315) = (term574 b _68315 s)) = True.
Proof. exact (TRANS (@lem5220756 b _68315 s) (@lem5220760 b _68315 s)). Qed.
Lemma lem5220762 (b : real) (_68315 : real) (s : real -> Prop) : True = ((term73 s b _68315) = (term574 b _68315 s)).
Proof. exact (SYM (@lem5220761 b _68315 s)). Qed.
Lemma lem5220763 (b : real) (_68315 : real) (s : real -> Prop) : (term73 s b _68315) = (term574 b _68315 s).
Proof. exact (EQ_MP (@lem5220762 b _68315 s) (@lem0)). Qed.
Lemma lem5220764 (_68315 : real) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term574 b _68315 s.
Proof. exact (EQ_MP (@lem5220763 b _68315 s) (@lem5220232 _68315 b s x' h1)). Qed.
Lemma lem5220766 (b : Prop) (a : Prop) : (a \/ b) = (term557 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5220767 (s : real -> Prop) (b : real) (_68315 : real) : (term574 b _68315 s) = (term578 s b _68315).
Proof. exact (@lem5220766 (term575 _68315 s) (real_le b _68315)). Qed.
Lemma lem5220769 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5220770 (_68315 : real) (s : real -> Prop) : (term580 _68315 s) = (@IN real _68315 s).
Proof. exact (@lem5220769 (@IN real _68315 s)). Qed.
Lemma lem5220771 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5220772 (_68315 : real) (s : real -> Prop) : (term581 _68315 s) = (term582 _68315 s).
Proof. exact (MK_COMB (@lem5220771) (@lem5220770 _68315 s)). Qed.
Lemma lem5220773 (b : real) (_68315 : real) : (real_le b _68315) = (real_le b _68315).
Proof. exact (eq_refl (real_le b _68315)). Qed.
Lemma lem5220774 (s : real -> Prop) (b : real) (_68315 : real) : (term578 s b _68315) = (term47 s b _68315).
Proof. exact (MK_COMB (@lem5220772 _68315 s) (@lem5220773 b _68315)). Qed.
Lemma lem5220775 (s : real -> Prop) (b : real) (_68315 : real) : (term574 b _68315 s) = (term47 s b _68315).
Proof. exact (TRANS (@lem5220767 s b _68315) (@lem5220774 s b _68315)). Qed.
Lemma lem5220778 (_68315 : real) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term47 s b _68315.
Proof. exact (EQ_MP (@lem5220775 s b _68315) (@lem5220764 _68315 b s x' h1)). Qed.
Lemma lem5220779 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term583 x s b.
Proof. exact (@lem5220778 (x s b) b s x' h1). Qed.
Lemma lem5220782 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term584 x s b.
Proof. exact (@lem5220779 x b s x' h4 (@lem5220735 x b s h1 h2 h3)). Qed.
Lemma lem5220783 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term585 x s b.
Proof. exact (fun h0 : term487 x s b => @lem5220782 x b s x' h1 h2 h3 h4). Qed.
Lemma lem5220785 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5220786 (x : type1021) (s : real -> Prop) (b : real) : (term585 x s b) = (term584 x s b).
Proof. exact (@lem5220785 (term584 x s b)). Qed.
Lemma lem5220787 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term584 x s b.
Proof. exact (EQ_MP (@lem5220786 x s b) (@lem5220783 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5220789 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5219277 s h1)). Qed.
Lemma lem5220790 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5220789 s h1). Qed.
Lemma lem5220792 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5220793 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5220792 (s = (@EMPTY real))). Qed.
Lemma lem5220794 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5220793 s) (@lem5220790 s h1)). Qed.
Lemma lem5220796 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5219277 s h1)). Qed.
Lemma lem5220797 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5220796 s h1). Qed.
Lemma lem5220799 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5220800 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5220799 (s = (@EMPTY real))). Qed.
Lemma lem5220801 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5220800 s) (@lem5220797 s h1)). Qed.
Lemma lem5220804 (x : type1021) (b : real) (s : real -> Prop) (h1 : term547 x b s) : term547 x b s.
Proof. exact (h1). Qed.
Lemma lem5220805 (x : type1021) (b : real) (s : real -> Prop) (h1 : term547 x b s) : term548 x b s.
Proof. exact (fun h0 : term486 x b s => @lem5220804 x b s h1). Qed.
Lemma lem5220807 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5220808 (x : type1021) (b : real) (s : real -> Prop) : (term548 x b s) = (term547 x b s).
Proof. exact (@lem5220807 (term486 x b s)). Qed.
Lemma lem5220809 (x : type1021) (b : real) (s : real -> Prop) (h1 : term547 x b s) : term547 x b s.
Proof. exact (EQ_MP (@lem5220808 x b s) (@lem5220805 x b s h1)). Qed.
Lemma lem5220812 (b : real) (s : real -> Prop) (h1 : term549 b s) : term549 b s.
Proof. exact (h1). Qed.
Lemma lem5220813 (b : real) (s : real -> Prop) (h1 : term549 b s) : term550 b s.
Proof. exact (fun h0 : term46 b s => @lem5220812 b s h1). Qed.
Lemma lem5220815 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5220816 (b : real) (s : real -> Prop) : (term550 b s) = (term549 b s).
Proof. exact (@lem5220815 (term46 b s)). Qed.
Lemma lem5220817 (b : real) (s : real -> Prop) (h1 : term549 b s) : term549 b s.
Proof. exact (EQ_MP (@lem5220816 b s) (@lem5220813 b s h1)). Qed.
Lemma lem5220818 (x : type1021) (b : real) (s : real -> Prop) (h1 : term547 x b s) (h2 : term549 b s) : term570 x b s.
Proof. exact (conj (@lem5220809 x b s h1) (@lem5220817 b s h2)). Qed.
Lemma lem5220819 (x : type1021) (b : real) (s : real -> Prop) (h1 : term547 x b s) (h2 : term549 b s) (h3 : term9 s) : term571 x b s.
Proof. exact (conj (@lem5220801 s h3) (@lem5220818 x b s h1 h2)). Qed.
Lemma lem5220821 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term569 _68313 x _68314 _68312.
Proof. exact (EQ_MP (@lem5220721 _68313 x _68314 _68312) (@lem5220704 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5220822 (b : real) (s : real -> Prop) (x : type1021) (h1 : term338 x) : term572 x b s.
Proof. exact (@lem5220821 b b s x h1). Qed.
Lemma lem5220825 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term547 x b s) (h3 : term549 b s) (h4 : term9 s) : term486 x b s.
Proof. exact (@lem5220822 b s x h1 (@lem5220819 x b s h2 h3 h4)). Qed.
Lemma lem5220826 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) : term573 x b s.
Proof. exact (fun h0 : term547 x b s => @lem5220825 x b s h1 h0 h2 h3). Qed.
Lemma lem5220828 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5220829 (x : type1021) (b : real) (s : real -> Prop) : (term573 x b s) = (term486 x b s).
Proof. exact (@lem5220828 (term486 x b s)). Qed.
Lemma lem5220830 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) : term486 x b s.
Proof. exact (EQ_MP (@lem5220829 x b s) (@lem5220826 x b s h1 h2 h3)). Qed.
Lemma lem5220832 (_68315 : real) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term47 s b _68315.
Proof. exact (EQ_MP (@lem5220775 s b _68315) (@lem5220764 _68315 b s x' h1)). Qed.
Lemma lem5220833 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term583 x s b.
Proof. exact (@lem5220832 (x s b) b s x' h1). Qed.
Lemma lem5220836 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term584 x s b.
Proof. exact (@lem5220833 x b s x' h4 (@lem5220830 x b s h1 h2 h3)). Qed.
Lemma lem5220837 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term585 x s b.
Proof. exact (fun h0 : term487 x s b => @lem5220836 x b s x' h1 h2 h3 h4). Qed.
Lemma lem5220839 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5220840 (x : type1021) (s : real -> Prop) (b : real) : (term585 x s b) = (term584 x s b).
Proof. exact (@lem5220839 (term584 x s b)). Qed.
Lemma lem5220841 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term584 x s b.
Proof. exact (EQ_MP (@lem5220840 x s b) (@lem5220837 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5220844 (b : real) (s : real -> Prop) (h1 : term549 b s) : term549 b s.
Proof. exact (h1). Qed.
Lemma lem5220845 (b : real) (s : real -> Prop) (h1 : term549 b s) : term550 b s.
Proof. exact (fun h0 : term46 b s => @lem5220844 b s h1). Qed.
Lemma lem5220847 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5220848 (b : real) (s : real -> Prop) : (term550 b s) = (term549 b s).
Proof. exact (@lem5220847 (term46 b s)). Qed.
Lemma lem5220849 (b : real) (s : real -> Prop) (h1 : term549 b s) : term549 b s.
Proof. exact (EQ_MP (@lem5220848 b s) (@lem5220845 b s h1)). Qed.
Lemma lem5220877 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5220878 (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term496 x _68314 _68312) = (term586 x _68312 _68314).
Proof. exact (@lem5220877 (term46 _68314 _68312) (term487 x _68312 _68314)). Qed.
Lemma lem5220884 (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term587 x _68312 _68313) = (term587 x _68312 _68313).
Proof. exact (eq_refl (term587 x _68312 _68313)). Qed.
Lemma lem5220885 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term588 _68313 x _68314 _68312) = (term589 _68313 x _68312 _68314).
Proof. exact (MK_COMB (@lem5220884 x _68312 _68313) (@lem5220878 x _68312 _68314)). Qed.
Lemma lem5220889 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5220890 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term589 _68313 x _68312 _68314) = (term590 _68313 x _68312 _68314).
Proof. exact (@lem5220889 (term46 _68314 _68312) (term487 x _68312 _68313) (term487 x _68312 _68314)). Qed.
Lemma lem5220906 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term588 _68313 x _68314 _68312) = (term590 _68313 x _68312 _68314).
Proof. exact (TRANS (@lem5220885 _68313 x _68312 _68314) (@lem5220890 _68313 x _68312 _68314)). Qed.
Lemma lem5220907 (_68312 : real -> Prop) : (term175 _68312) = (term175 _68312).
Proof. exact (eq_refl (term175 _68312)). Qed.
Lemma lem5220908 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term528 _68313 x _68314 _68312) = (term591 _68313 x _68312 _68314).
Proof. exact (MK_COMB (@lem5220907 _68312) (@lem5220906 _68313 x _68312 _68314)). Qed.
Lemma lem5220919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5220920 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term592 _68313 x _68314 _68312) = (term593 _68313 x _68312 _68314).
Proof. exact (MK_COMB (@lem5220919) (@lem5220908 _68313 x _68312 _68314)). Qed.
Lemma lem5220924 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5220925 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term594 x _68313 _68314 _68312) = (term595 x _68313 _68314 _68312).
Proof. exact (@lem5220924 (_68312 = (@EMPTY real)) (term487 x _68312 _68314) (term596 x _68313 _68314 _68312)). Qed.
Lemma lem5220941 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5220942 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term597 x _68313 _68314 _68312) = (term588 _68313 x _68314 _68312).
Proof. exact (@lem5220941 (term487 x _68312 _68313) (term487 x _68312 _68314) (term46 _68314 _68312)). Qed.
Lemma lem5220956 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5220957 (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term496 x _68314 _68312) = (term586 x _68312 _68314).
Proof. exact (@lem5220956 (term46 _68314 _68312) (term487 x _68312 _68314)). Qed.
Lemma lem5220963 (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term587 x _68312 _68313) = (term587 x _68312 _68313).
Proof. exact (eq_refl (term587 x _68312 _68313)). Qed.
Lemma lem5220964 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term588 _68313 x _68314 _68312) = (term589 _68313 x _68312 _68314).
Proof. exact (MK_COMB (@lem5220963 x _68312 _68313) (@lem5220957 x _68312 _68314)). Qed.
Lemma lem5220968 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5220969 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term589 _68313 x _68312 _68314) = (term590 _68313 x _68312 _68314).
Proof. exact (@lem5220968 (term46 _68314 _68312) (term487 x _68312 _68313) (term487 x _68312 _68314)). Qed.
Lemma lem5220985 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term588 _68313 x _68314 _68312) = (term590 _68313 x _68312 _68314).
Proof. exact (TRANS (@lem5220964 _68313 x _68312 _68314) (@lem5220969 _68313 x _68312 _68314)). Qed.
Lemma lem5220986 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term597 x _68313 _68314 _68312) = (term590 _68313 x _68312 _68314).
Proof. exact (TRANS (@lem5220942 _68313 x _68314 _68312) (@lem5220985 _68313 x _68312 _68314)). Qed.
Lemma lem5220987 (_68312 : real -> Prop) : (term175 _68312) = (term175 _68312).
Proof. exact (eq_refl (term175 _68312)). Qed.
Lemma lem5220988 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term595 x _68313 _68314 _68312) = (term591 _68313 x _68312 _68314).
Proof. exact (MK_COMB (@lem5220987 _68312) (@lem5220986 _68313 x _68312 _68314)). Qed.
Lemma lem5220999 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term594 x _68313 _68314 _68312) = (term591 _68313 x _68312 _68314).
Proof. exact (TRANS (@lem5220925 x _68313 _68314 _68312) (@lem5220988 _68313 x _68312 _68314)). Qed.
Lemma lem5221000 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : ((term528 _68313 x _68314 _68312) = (term594 x _68313 _68314 _68312)) = ((term591 _68313 x _68312 _68314) = (term591 _68313 x _68312 _68314)).
Proof. exact (MK_COMB (@lem5220920 _68313 x _68312 _68314) (@lem5220999 _68313 x _68312 _68314)). Qed.
Lemma lem5221002 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5221003 (x : Prop) : (x = x) = True.
Proof. exact (@lem5221002 Prop x). Qed.
Lemma lem5221004 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : ((term591 _68313 x _68312 _68314) = (term591 _68313 x _68312 _68314)) = True.
Proof. exact (@lem5221003 (term591 _68313 x _68312 _68314)). Qed.
Lemma lem5221005 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : ((term528 _68313 x _68314 _68312) = (term594 x _68313 _68314 _68312)) = True.
Proof. exact (TRANS (@lem5221000 _68313 x _68312 _68314) (@lem5221004 _68313 x _68312 _68314)). Qed.
Lemma lem5221006 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : True = ((term528 _68313 x _68314 _68312) = (term594 x _68313 _68314 _68312)).
Proof. exact (SYM (@lem5221005 x _68313 _68314 _68312)). Qed.
Lemma lem5221007 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term528 _68313 x _68314 _68312) = (term594 x _68313 _68314 _68312).
Proof. exact (EQ_MP (@lem5221006 x _68313 _68314 _68312) (@lem0)). Qed.
Lemma lem5221008 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term594 x _68313 _68314 _68312.
Proof. exact (EQ_MP (@lem5221007 x _68313 _68314 _68312) (@lem5220294 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5221010 (b : Prop) (a : Prop) : (a \/ b) = (term557 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5221011 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term594 x _68313 _68314 _68312) = (term598 _68313 x _68312 _68314).
Proof. exact (@lem5221010 (term599 x _68313 _68314 _68312) (term487 x _68312 _68314)). Qed.
Lemma lem5221013 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5221014 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term600 x _68313 _68314 _68312) = (term601 x _68313 _68314 _68312).
Proof. exact (@lem5221013 (_68312 = (@EMPTY real)) (term596 x _68313 _68314 _68312)). Qed.
Lemma lem5221016 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5221017 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term602 x _68313 _68314 _68312) = (term603 x _68313 _68314 _68312).
Proof. exact (@lem5221016 (term487 x _68312 _68313) (term46 _68314 _68312)). Qed.
Lemma lem5221019 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5221020 (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term604 x _68312 _68313) = (term584 x _68312 _68313).
Proof. exact (@lem5221019 (term584 x _68312 _68313)). Qed.
Lemma lem5221021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5221022 (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term605 x _68312 _68313) = (term606 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221021) (@lem5221020 x _68312 _68313)). Qed.
Lemma lem5221023 (_68314 : real) (_68312 : real -> Prop) : (term549 _68314 _68312) = (term549 _68314 _68312).
Proof. exact (eq_refl (term549 _68314 _68312)). Qed.
Lemma lem5221024 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term603 x _68313 _68314 _68312) = (term607 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5221022 x _68312 _68313) (@lem5221023 _68314 _68312)). Qed.
Lemma lem5221025 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term602 x _68313 _68314 _68312) = (term607 x _68313 _68314 _68312).
Proof. exact (TRANS (@lem5221017 x _68313 _68314 _68312) (@lem5221024 x _68313 _68314 _68312)). Qed.
Lemma lem5221026 (_68312 : real -> Prop) : (term61 _68312) = (term61 _68312).
Proof. exact (eq_refl (term61 _68312)). Qed.
Lemma lem5221027 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term601 x _68313 _68314 _68312) = (term608 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5221026 _68312) (@lem5221025 x _68313 _68314 _68312)). Qed.
Lemma lem5221028 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term600 x _68313 _68314 _68312) = (term608 x _68313 _68314 _68312).
Proof. exact (TRANS (@lem5221014 x _68313 _68314 _68312) (@lem5221027 x _68313 _68314 _68312)). Qed.
Lemma lem5221029 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5221030 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term609 x _68313 _68314 _68312) = (term610 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5221029) (@lem5221028 x _68313 _68314 _68312)). Qed.
Lemma lem5221031 (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term487 x _68312 _68314) = (term487 x _68312 _68314).
Proof. exact (eq_refl (term487 x _68312 _68314)). Qed.
Lemma lem5221032 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term598 _68313 x _68312 _68314) = (term611 _68313 x _68312 _68314).
Proof. exact (MK_COMB (@lem5221030 x _68313 _68314 _68312) (@lem5221031 x _68312 _68314)). Qed.
Lemma lem5221033 (_68313 : real) (x : type1021) (_68312 : real -> Prop) (_68314 : real) : (term594 x _68313 _68314 _68312) = (term611 _68313 x _68312 _68314).
Proof. exact (TRANS (@lem5221011 _68313 x _68312 _68314) (@lem5221032 _68313 x _68312 _68314)). Qed.
Lemma lem5221035 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term612 x b s.
Proof. exact (conj (@lem5220841 x b s x' h1 h2 h3 h4) (@lem5220849 b s h2)). Qed.
Lemma lem5221036 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term613 x b s.
Proof. exact (conj (@lem5220794 s h3) (@lem5221035 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221038 (_68313 : real) (_68312 : real -> Prop) (_68314 : real) (x : type1021) (h1 : term338 x) : term611 _68313 x _68312 _68314.
Proof. exact (EQ_MP (@lem5221033 _68313 x _68312 _68314) (@lem5221008 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5221039 (s : real -> Prop) (b : real) (x : type1021) (h1 : term338 x) : term614 x s b.
Proof. exact (@lem5221038 b s b x h1). Qed.
Lemma lem5221042 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term487 x s b.
Proof. exact (@lem5221039 s b x h1 (@lem5221036 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221043 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term615 x s b.
Proof. exact (fun h0 : term584 x s b => @lem5221042 x b s x' h1 h2 h3 h4). Qed.
Lemma lem5221045 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5221046 (x : type1021) (s : real -> Prop) (b : real) : (term615 x s b) = (term487 x s b).
Proof. exact (@lem5221045 (term584 x s b)). Qed.
Lemma lem5221047 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term487 x s b.
Proof. exact (EQ_MP (@lem5221046 x s b) (@lem5221043 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221049 (b : Prop) (a : Prop) : (a \/ b) = (term557 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5221052 (b : real) (_68315 : real) (s : real -> Prop) : (term73 s b _68315) = (term616 b _68315 s).
Proof. exact (@lem5221049 (real_le b _68315) (term575 _68315 s)). Qed.
Lemma lem5221055 (_68315 : real) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term616 b _68315 s.
Proof. exact (EQ_MP (@lem5221052 b _68315 s) (@lem5220232 _68315 b s x' h1)). Qed.
Lemma lem5221056 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term617 x b s.
Proof. exact (@lem5221055 (x s b) b s x' h1). Qed.
Lemma lem5221059 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term547 x b s.
Proof. exact (@lem5221056 x b s x' h4 (@lem5221047 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221060 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term548 x b s.
Proof. exact (fun h0 : term486 x b s => @lem5221059 x b s x' h1 h2 h3 h4). Qed.
Lemma lem5221062 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5221063 (x : type1021) (b : real) (s : real -> Prop) : (term548 x b s) = (term547 x b s).
Proof. exact (@lem5221062 (term486 x b s)). Qed.
Lemma lem5221064 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term547 x b s.
Proof. exact (EQ_MP (@lem5221063 x b s) (@lem5221060 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221082 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5221083 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term618 _68313 x _68314 _68312) = (term619 x _68313 _68314 _68312).
Proof. exact (@lem5221082 (term486 x _68314 _68312) (term487 x _68312 _68313) (term46 _68314 _68312)). Qed.
Lemma lem5221097 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5221098 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term596 x _68313 _68314 _68312) = (term620 _68314 x _68312 _68313).
Proof. exact (@lem5221097 (term46 _68314 _68312) (term487 x _68312 _68313)). Qed.
Lemma lem5221104 (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term621 x _68314 _68312) = (term621 x _68314 _68312).
Proof. exact (eq_refl (term621 x _68314 _68312)). Qed.
Lemma lem5221105 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term619 x _68313 _68314 _68312) = (term622 _68314 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221104 x _68314 _68312) (@lem5221098 _68314 x _68312 _68313)). Qed.
Lemma lem5221116 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term618 _68313 x _68314 _68312) = (term622 _68314 x _68312 _68313).
Proof. exact (TRANS (@lem5221083 x _68313 _68314 _68312) (@lem5221105 _68314 x _68312 _68313)). Qed.
Lemma lem5221117 (_68312 : real -> Prop) : (term175 _68312) = (term175 _68312).
Proof. exact (eq_refl (term175 _68312)). Qed.
Lemma lem5221118 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term530 _68313 x _68314 _68312) = (term623 _68314 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221117 _68312) (@lem5221116 _68314 x _68312 _68313)). Qed.
Lemma lem5221129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5221130 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term624 _68313 x _68314 _68312) = (term625 _68314 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221129) (@lem5221118 _68314 x _68312 _68313)). Qed.
Lemma lem5221134 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5221135 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term626 _68313 x _68314 _68312) = (term627 _68313 x _68314 _68312).
Proof. exact (@lem5221134 (_68312 = (@EMPTY real)) (term46 _68314 _68312) (term628 _68313 x _68314 _68312)). Qed.
Lemma lem5221161 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5221162 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term628 _68313 x _68314 _68312) = (term629 _68314 x _68312 _68313).
Proof. exact (@lem5221161 (term486 x _68314 _68312) (term487 x _68312 _68313)). Qed.
Lemma lem5221168 (_68314 : real) (_68312 : real -> Prop) : (term630 _68314 _68312) = (term630 _68314 _68312).
Proof. exact (eq_refl (term630 _68314 _68312)). Qed.
Lemma lem5221169 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term631 _68313 x _68314 _68312) = (term632 _68314 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221168 _68314 _68312) (@lem5221162 _68314 x _68312 _68313)). Qed.
Lemma lem5221173 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5221174 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term632 _68314 x _68312 _68313) = (term622 _68314 x _68312 _68313).
Proof. exact (@lem5221173 (term486 x _68314 _68312) (term46 _68314 _68312) (term487 x _68312 _68313)). Qed.
Lemma lem5221190 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term631 _68313 x _68314 _68312) = (term622 _68314 x _68312 _68313).
Proof. exact (TRANS (@lem5221169 _68314 x _68312 _68313) (@lem5221174 _68314 x _68312 _68313)). Qed.
Lemma lem5221191 (_68312 : real -> Prop) : (term175 _68312) = (term175 _68312).
Proof. exact (eq_refl (term175 _68312)). Qed.
Lemma lem5221192 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term627 _68313 x _68314 _68312) = (term623 _68314 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221191 _68312) (@lem5221190 _68314 x _68312 _68313)). Qed.
Lemma lem5221203 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term626 _68313 x _68314 _68312) = (term623 _68314 x _68312 _68313).
Proof. exact (TRANS (@lem5221135 _68313 x _68314 _68312) (@lem5221192 _68314 x _68312 _68313)). Qed.
Lemma lem5221204 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : ((term530 _68313 x _68314 _68312) = (term626 _68313 x _68314 _68312)) = ((term623 _68314 x _68312 _68313) = (term623 _68314 x _68312 _68313)).
Proof. exact (MK_COMB (@lem5221130 _68314 x _68312 _68313) (@lem5221203 _68314 x _68312 _68313)). Qed.
Lemma lem5221206 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5221207 (x : Prop) : (x = x) = True.
Proof. exact (@lem5221206 Prop x). Qed.
Lemma lem5221208 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : ((term623 _68314 x _68312 _68313) = (term623 _68314 x _68312 _68313)) = True.
Proof. exact (@lem5221207 (term623 _68314 x _68312 _68313)). Qed.
Lemma lem5221209 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : ((term530 _68313 x _68314 _68312) = (term626 _68313 x _68314 _68312)) = True.
Proof. exact (TRANS (@lem5221204 _68314 x _68312 _68313) (@lem5221208 _68314 x _68312 _68313)). Qed.
Lemma lem5221210 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : True = ((term530 _68313 x _68314 _68312) = (term626 _68313 x _68314 _68312)).
Proof. exact (SYM (@lem5221209 _68313 x _68314 _68312)). Qed.
Lemma lem5221211 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term530 _68313 x _68314 _68312) = (term626 _68313 x _68314 _68312).
Proof. exact (EQ_MP (@lem5221210 _68313 x _68314 _68312) (@lem0)). Qed.
Lemma lem5221212 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term626 _68313 x _68314 _68312.
Proof. exact (EQ_MP (@lem5221211 _68313 x _68314 _68312) (@lem5220326 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5221214 (b : Prop) (a : Prop) : (a \/ b) = (term557 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5221215 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term626 _68313 x _68314 _68312) = (term633 _68313 x _68314 _68312).
Proof. exact (@lem5221214 (term634 _68313 x _68314 _68312) (term46 _68314 _68312)). Qed.
Lemma lem5221217 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5221218 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term635 _68313 x _68314 _68312) = (term636 _68313 x _68314 _68312).
Proof. exact (@lem5221217 (_68312 = (@EMPTY real)) (term628 _68313 x _68314 _68312)). Qed.
Lemma lem5221220 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5221221 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term637 _68313 x _68314 _68312) = (term638 _68313 x _68314 _68312).
Proof. exact (@lem5221220 (term487 x _68312 _68313) (term486 x _68314 _68312)). Qed.
Lemma lem5221223 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5221224 (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term604 x _68312 _68313) = (term584 x _68312 _68313).
Proof. exact (@lem5221223 (term584 x _68312 _68313)). Qed.
Lemma lem5221225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5221226 (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term605 x _68312 _68313) = (term606 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221225) (@lem5221224 x _68312 _68313)). Qed.
Lemma lem5221227 (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term547 x _68314 _68312) = (term547 x _68314 _68312).
Proof. exact (eq_refl (term547 x _68314 _68312)). Qed.
Lemma lem5221228 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term638 _68313 x _68314 _68312) = (term639 _68313 x _68314 _68312).
Proof. exact (MK_COMB (@lem5221226 x _68312 _68313) (@lem5221227 x _68314 _68312)). Qed.
Lemma lem5221229 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term637 _68313 x _68314 _68312) = (term639 _68313 x _68314 _68312).
Proof. exact (TRANS (@lem5221221 _68313 x _68314 _68312) (@lem5221228 _68313 x _68314 _68312)). Qed.
Lemma lem5221230 (_68312 : real -> Prop) : (term61 _68312) = (term61 _68312).
Proof. exact (eq_refl (term61 _68312)). Qed.
Lemma lem5221231 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term636 _68313 x _68314 _68312) = (term640 _68313 x _68314 _68312).
Proof. exact (MK_COMB (@lem5221230 _68312) (@lem5221229 _68313 x _68314 _68312)). Qed.
Lemma lem5221232 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term635 _68313 x _68314 _68312) = (term640 _68313 x _68314 _68312).
Proof. exact (TRANS (@lem5221218 _68313 x _68314 _68312) (@lem5221231 _68313 x _68314 _68312)). Qed.
Lemma lem5221233 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5221234 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term641 _68313 x _68314 _68312) = (term642 _68313 x _68314 _68312).
Proof. exact (MK_COMB (@lem5221233) (@lem5221232 _68313 x _68314 _68312)). Qed.
Lemma lem5221235 (_68314 : real) (_68312 : real -> Prop) : (term46 _68314 _68312) = (term46 _68314 _68312).
Proof. exact (eq_refl (term46 _68314 _68312)). Qed.
Lemma lem5221236 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term633 _68313 x _68314 _68312) = (term643 _68313 x _68314 _68312).
Proof. exact (MK_COMB (@lem5221234 _68313 x _68314 _68312) (@lem5221235 _68314 _68312)). Qed.
Lemma lem5221237 (_68313 : real) (x : type1021) (_68314 : real) (_68312 : real -> Prop) : (term626 _68313 x _68314 _68312) = (term643 _68313 x _68314 _68312).
Proof. exact (TRANS (@lem5221215 _68313 x _68314 _68312) (@lem5221236 _68313 x _68314 _68312)). Qed.
Lemma lem5221239 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term644 x b s.
Proof. exact (conj (@lem5220787 x b s x' h1 h2 h3 h4) (@lem5221064 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221240 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term645 x b s.
Proof. exact (conj (@lem5220592 s h3) (@lem5221239 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221242 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term643 _68313 x _68314 _68312.
Proof. exact (EQ_MP (@lem5221237 _68313 x _68314 _68312) (@lem5221212 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5221243 (b : real) (s : real -> Prop) (x : type1021) (h1 : term338 x) : term646 x b s.
Proof. exact (@lem5221242 b b s x h1). Qed.
Lemma lem5221246 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term549 b s) (h3 : term9 s) (h4 : term149 b s x') : term46 b s.
Proof. exact (@lem5221243 b s x h1 (@lem5221240 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221247 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b s x') : term647 b s.
Proof. exact (fun h0 : term549 b s => @lem5221246 x b s x' h1 h0 h2 h3). Qed.
Lemma lem5221249 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5221250 (b : real) (s : real -> Prop) : (term647 b s) = (term46 b s).
Proof. exact (@lem5221249 (term46 b s)). Qed.
Lemma lem5221251 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b s x') : term46 b s.
Proof. exact (EQ_MP (@lem5221250 b s) (@lem5221247 x b s x' h1 h2 h3)). Qed.
Lemma lem5221253 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5219277 s h1)). Qed.
Lemma lem5221254 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5221253 s h1). Qed.
Lemma lem5221256 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5221257 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5221256 (s = (@EMPTY real))). Qed.
Lemma lem5221258 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5221257 s) (@lem5221254 s h1)). Qed.
Lemma lem5221260 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5219277 s h1)). Qed.
Lemma lem5221261 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5221260 s h1). Qed.
Lemma lem5221263 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5221264 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5221263 (s = (@EMPTY real))). Qed.
Lemma lem5221265 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5221264 s) (@lem5221261 s h1)). Qed.
Lemma lem5221267 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : @IN real b s.
Proof. exact (proj1 (@lem5219522 b s x' h1)). Qed.
Lemma lem5221268 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term648 b s.
Proof. exact (fun h0 : term575 b s => @lem5221267 b s x' h1). Qed.
Lemma lem5221270 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5221271 (b : real) (s : real -> Prop) : (term648 b s) = (@IN real b s).
Proof. exact (@lem5221270 (@IN real b s)). Qed.
Lemma lem5221272 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : @IN real b s.
Proof. exact (EQ_MP (@lem5221271 b s) (@lem5221268 b s x' h1)). Qed.
Lemma lem5221275 (s : real -> Prop) (b : real) (h1 : term533 s b) : term533 s b.
Proof. exact (h1). Qed.
Lemma lem5221276 (s : real -> Prop) (b : real) (h1 : term533 s b) : term649 s b.
Proof. exact (fun h0 : term81 s b => @lem5221275 s b h1). Qed.
Lemma lem5221278 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5221279 (s : real -> Prop) (b : real) : (term649 s b) = (term533 s b).
Proof. exact (@lem5221278 (term81 s b)). Qed.
Lemma lem5221280 (s : real -> Prop) (b : real) (h1 : term533 s b) : term533 s b.
Proof. exact (EQ_MP (@lem5221279 s b) (@lem5221276 s b h1)). Qed.
Lemma lem5221308 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5221309 (_68314 : real) (_68312 : real -> Prop) : (term180 _68312 _68314) = (term650 _68314 _68312).
Proof. exact (@lem5221308 (term81 _68312 _68314) (term575 _68314 _68312)). Qed.
Lemma lem5221315 (x : type1021) (_68313 : real) (_68312 : real -> Prop) : (term621 x _68313 _68312) = (term621 x _68313 _68312).
Proof. exact (eq_refl (term621 x _68313 _68312)). Qed.
Lemma lem5221316 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term651 x _68313 _68312 _68314) = (term652 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5221315 x _68313 _68312) (@lem5221309 _68314 _68312)). Qed.
Lemma lem5221327 (_68312 : real -> Prop) : (term175 _68312) = (term175 _68312).
Proof. exact (eq_refl (term175 _68312)). Qed.
Lemma lem5221328 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term531 x _68313 _68312 _68314) = (term653 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5221327 _68312) (@lem5221316 x _68313 _68314 _68312)). Qed.
Lemma lem5221339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5221340 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term654 x _68313 _68312 _68314) = (term655 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5221339) (@lem5221328 x _68313 _68314 _68312)). Qed.
Lemma lem5221344 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5221345 (x : type1021) (_68313 : real) (_68312 : real -> Prop) (_68314 : real) : (term656 x _68313 _68312 _68314) = (term531 x _68313 _68312 _68314).
Proof. exact (@lem5221344 (_68312 = (@EMPTY real)) (term486 x _68313 _68312) (term180 _68312 _68314)). Qed.
Lemma lem5221371 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5221372 (_68314 : real) (_68312 : real -> Prop) : (term180 _68312 _68314) = (term650 _68314 _68312).
Proof. exact (@lem5221371 (term81 _68312 _68314) (term575 _68314 _68312)). Qed.
Lemma lem5221378 (x : type1021) (_68313 : real) (_68312 : real -> Prop) : (term621 x _68313 _68312) = (term621 x _68313 _68312).
Proof. exact (eq_refl (term621 x _68313 _68312)). Qed.
Lemma lem5221379 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term651 x _68313 _68312 _68314) = (term652 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5221378 x _68313 _68312) (@lem5221372 _68314 _68312)). Qed.
Lemma lem5221390 (_68312 : real -> Prop) : (term175 _68312) = (term175 _68312).
Proof. exact (eq_refl (term175 _68312)). Qed.
Lemma lem5221391 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term531 x _68313 _68312 _68314) = (term653 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5221390 _68312) (@lem5221379 x _68313 _68314 _68312)). Qed.
Lemma lem5221402 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term656 x _68313 _68312 _68314) = (term653 x _68313 _68314 _68312).
Proof. exact (TRANS (@lem5221345 x _68313 _68312 _68314) (@lem5221391 x _68313 _68314 _68312)). Qed.
Lemma lem5221403 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : ((term531 x _68313 _68312 _68314) = (term656 x _68313 _68312 _68314)) = ((term653 x _68313 _68314 _68312) = (term653 x _68313 _68314 _68312)).
Proof. exact (MK_COMB (@lem5221340 x _68313 _68314 _68312) (@lem5221402 x _68313 _68314 _68312)). Qed.
Lemma lem5221405 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5221406 (x : Prop) : (x = x) = True.
Proof. exact (@lem5221405 Prop x). Qed.
Lemma lem5221407 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : ((term653 x _68313 _68314 _68312) = (term653 x _68313 _68314 _68312)) = True.
Proof. exact (@lem5221406 (term653 x _68313 _68314 _68312)). Qed.
Lemma lem5221408 (x : type1021) (_68313 : real) (_68312 : real -> Prop) (_68314 : real) : ((term531 x _68313 _68312 _68314) = (term656 x _68313 _68312 _68314)) = True.
Proof. exact (TRANS (@lem5221403 x _68313 _68314 _68312) (@lem5221407 x _68313 _68314 _68312)). Qed.
Lemma lem5221409 (x : type1021) (_68313 : real) (_68312 : real -> Prop) (_68314 : real) : True = ((term531 x _68313 _68312 _68314) = (term656 x _68313 _68312 _68314)).
Proof. exact (SYM (@lem5221408 x _68313 _68312 _68314)). Qed.
Lemma lem5221410 (x : type1021) (_68313 : real) (_68312 : real -> Prop) (_68314 : real) : (term531 x _68313 _68312 _68314) = (term656 x _68313 _68312 _68314).
Proof. exact (EQ_MP (@lem5221409 x _68313 _68312 _68314) (@lem0)). Qed.
Lemma lem5221411 (_68313 : real) (_68312 : real -> Prop) (_68314 : real) (x : type1021) (h1 : term338 x) : term656 x _68313 _68312 _68314.
Proof. exact (EQ_MP (@lem5221410 x _68313 _68312 _68314) (@lem5220342 _68313 _68312 _68314 x h1)). Qed.
Lemma lem5221413 (b : Prop) (a : Prop) : (a \/ b) = (term557 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5221414 (_68314 : real) (x : type1021) (_68313 : real) (_68312 : real -> Prop) : (term656 x _68313 _68312 _68314) = (term657 _68314 x _68313 _68312).
Proof. exact (@lem5221413 (term658 _68312 _68314) (term486 x _68313 _68312)). Qed.
Lemma lem5221416 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5221417 (_68312 : real -> Prop) (_68314 : real) : (term659 _68312 _68314) = (term660 _68312 _68314).
Proof. exact (@lem5221416 (_68312 = (@EMPTY real)) (term180 _68312 _68314)). Qed.
Lemma lem5221419 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5221420 (_68312 : real -> Prop) (_68314 : real) : (term661 _68312 _68314) = (term662 _68312 _68314).
Proof. exact (@lem5221419 (term575 _68314 _68312) (term81 _68312 _68314)). Qed.
Lemma lem5221422 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5221423 (_68314 : real) (_68312 : real -> Prop) : (term580 _68314 _68312) = (@IN real _68314 _68312).
Proof. exact (@lem5221422 (@IN real _68314 _68312)). Qed.
Lemma lem5221424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5221425 (_68314 : real) (_68312 : real -> Prop) : (term663 _68314 _68312) = (term69 _68314 _68312).
Proof. exact (MK_COMB (@lem5221424) (@lem5221423 _68314 _68312)). Qed.
Lemma lem5221426 (_68312 : real -> Prop) (_68314 : real) : (term533 _68312 _68314) = (term533 _68312 _68314).
Proof. exact (eq_refl (term533 _68312 _68314)). Qed.
Lemma lem5221427 (_68312 : real -> Prop) (_68314 : real) : (term662 _68312 _68314) = (term80 _68312 _68314).
Proof. exact (MK_COMB (@lem5221425 _68314 _68312) (@lem5221426 _68312 _68314)). Qed.
Lemma lem5221428 (_68312 : real -> Prop) (_68314 : real) : (term661 _68312 _68314) = (term80 _68312 _68314).
Proof. exact (TRANS (@lem5221420 _68312 _68314) (@lem5221427 _68312 _68314)). Qed.
Lemma lem5221429 (_68312 : real -> Prop) : (term61 _68312) = (term61 _68312).
Proof. exact (eq_refl (term61 _68312)). Qed.
Lemma lem5221430 (_68312 : real -> Prop) (_68314 : real) : (term660 _68312 _68314) = (term664 _68312 _68314).
Proof. exact (MK_COMB (@lem5221429 _68312) (@lem5221428 _68312 _68314)). Qed.
Lemma lem5221431 (_68312 : real -> Prop) (_68314 : real) : (term659 _68312 _68314) = (term664 _68312 _68314).
Proof. exact (TRANS (@lem5221417 _68312 _68314) (@lem5221430 _68312 _68314)). Qed.
Lemma lem5221432 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5221433 (_68312 : real -> Prop) (_68314 : real) : (term665 _68312 _68314) = (term666 _68312 _68314).
Proof. exact (MK_COMB (@lem5221432) (@lem5221431 _68312 _68314)). Qed.
Lemma lem5221434 (x : type1021) (_68313 : real) (_68312 : real -> Prop) : (term486 x _68313 _68312) = (term486 x _68313 _68312).
Proof. exact (eq_refl (term486 x _68313 _68312)). Qed.
Lemma lem5221435 (_68314 : real) (x : type1021) (_68313 : real) (_68312 : real -> Prop) : (term657 _68314 x _68313 _68312) = (term667 _68314 x _68313 _68312).
Proof. exact (MK_COMB (@lem5221433 _68312 _68314) (@lem5221434 x _68313 _68312)). Qed.
Lemma lem5221436 (_68314 : real) (x : type1021) (_68313 : real) (_68312 : real -> Prop) : (term656 x _68313 _68312 _68314) = (term667 _68314 x _68313 _68312).
Proof. exact (TRANS (@lem5221414 _68314 x _68313 _68312) (@lem5221435 _68314 x _68313 _68312)). Qed.
Lemma lem5221438 (b : real) (s : real -> Prop) (x' : real) (h1 : term533 s b) (h2 : term149 b s x') : term80 s b.
Proof. exact (conj (@lem5221272 b s x' h2) (@lem5221280 s b h1)). Qed.
Lemma lem5221439 (b : real) (s : real -> Prop) (x' : real) (h1 : term533 s b) (h2 : term9 s) (h3 : term149 b s x') : term664 s b.
Proof. exact (conj (@lem5221265 s h2) (@lem5221438 b s x' h1 h3)). Qed.
Lemma lem5221441 (_68314 : real) (_68313 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term667 _68314 x _68313 _68312.
Proof. exact (EQ_MP (@lem5221436 _68314 x _68313 _68312) (@lem5221411 _68313 _68312 _68314 x h1)). Qed.
Lemma lem5221442 (b : real) (_68313 : real) (s : real -> Prop) (x : type1021) (h1 : term338 x) : term667 b x _68313 s.
Proof. exact (@lem5221441 b _68313 s x h1). Qed.
Lemma lem5221445 (_68313 : real) (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s b) (h3 : term9 s) (h4 : term149 b s x') : term486 x _68313 s.
Proof. exact (@lem5221442 b _68313 s x h1 (@lem5221439 b s x' h2 h3 h4)). Qed.
Lemma lem5221446 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s b) (h3 : term9 s) (h4 : term149 b s x') : term486 x b s.
Proof. exact (@lem5221445 b x b s x' h1 h2 h3 h4). Qed.
Lemma lem5221447 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s b) (h3 : term9 s) (h4 : term149 b s x') : term573 x b s.
Proof. exact (fun h0 : term547 x b s => @lem5221446 x b s x' h1 h2 h3 h4). Qed.
Lemma lem5221449 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5221450 (x : type1021) (b : real) (s : real -> Prop) : (term573 x b s) = (term486 x b s).
Proof. exact (@lem5221449 (term486 x b s)). Qed.
Lemma lem5221451 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s b) (h3 : term9 s) (h4 : term149 b s x') : term486 x b s.
Proof. exact (EQ_MP (@lem5221450 x b s) (@lem5221447 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221453 (_68315 : real) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term47 s b _68315.
Proof. exact (EQ_MP (@lem5220775 s b _68315) (@lem5220764 _68315 b s x' h1)). Qed.
Lemma lem5221454 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term583 x s b.
Proof. exact (@lem5221453 (x s b) b s x' h1). Qed.
Lemma lem5221457 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s b) (h3 : term9 s) (h4 : term149 b s x') : term584 x s b.
Proof. exact (@lem5221454 x b s x' h4 (@lem5221451 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221458 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s b) (h3 : term9 s) (h4 : term149 b s x') : term585 x s b.
Proof. exact (fun h0 : term487 x s b => @lem5221457 x b s x' h1 h2 h3 h4). Qed.
Lemma lem5221460 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5221461 (x : type1021) (s : real -> Prop) (b : real) : (term585 x s b) = (term584 x s b).
Proof. exact (@lem5221460 (term584 x s b)). Qed.
Lemma lem5221462 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s b) (h3 : term9 s) (h4 : term149 b s x') : term584 x s b.
Proof. exact (EQ_MP (@lem5221461 x s b) (@lem5221458 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221464 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : @IN real b s.
Proof. exact (proj1 (@lem5219522 b s x' h1)). Qed.
Lemma lem5221465 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term648 b s.
Proof. exact (fun h0 : term575 b s => @lem5221464 b s x' h1). Qed.
Lemma lem5221467 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5221468 (b : real) (s : real -> Prop) : (term648 b s) = (@IN real b s).
Proof. exact (@lem5221467 (@IN real b s)). Qed.
Lemma lem5221469 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : @IN real b s.
Proof. exact (EQ_MP (@lem5221468 b s) (@lem5221465 b s x' h1)). Qed.
Lemma lem5221487 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5221488 (x : type1021) (_68313 : real) (_68312 : real -> Prop) (_68314 : real) : (term668 x _68313 _68312 _68314) = (term669 x _68313 _68312 _68314).
Proof. exact (@lem5221487 (term575 _68314 _68312) (term487 x _68312 _68313) (term81 _68312 _68314)). Qed.
Lemma lem5221502 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5221503 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term670 x _68313 _68312 _68314) = (term671 _68314 x _68312 _68313).
Proof. exact (@lem5221502 (term81 _68312 _68314) (term487 x _68312 _68313)). Qed.
Lemma lem5221509 (_68314 : real) (_68312 : real -> Prop) : (term672 _68314 _68312) = (term672 _68314 _68312).
Proof. exact (eq_refl (term672 _68314 _68312)). Qed.
Lemma lem5221510 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term669 x _68313 _68312 _68314) = (term673 _68314 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221509 _68314 _68312) (@lem5221503 _68314 x _68312 _68313)). Qed.
Lemma lem5221514 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5221515 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term673 _68314 x _68312 _68313) = (term674 _68314 x _68312 _68313).
Proof. exact (@lem5221514 (term81 _68312 _68314) (term575 _68314 _68312) (term487 x _68312 _68313)). Qed.
Lemma lem5221531 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term669 x _68313 _68312 _68314) = (term674 _68314 x _68312 _68313).
Proof. exact (TRANS (@lem5221510 _68314 x _68312 _68313) (@lem5221515 _68314 x _68312 _68313)). Qed.
Lemma lem5221532 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term668 x _68313 _68312 _68314) = (term674 _68314 x _68312 _68313).
Proof. exact (TRANS (@lem5221488 x _68313 _68312 _68314) (@lem5221531 _68314 x _68312 _68313)). Qed.
Lemma lem5221533 (_68312 : real -> Prop) : (term175 _68312) = (term175 _68312).
Proof. exact (eq_refl (term175 _68312)). Qed.
Lemma lem5221534 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term532 x _68313 _68312 _68314) = (term675 _68314 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221533 _68312) (@lem5221532 _68314 x _68312 _68313)). Qed.
Lemma lem5221545 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5221546 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term676 x _68313 _68312 _68314) = (term677 _68314 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221545) (@lem5221534 _68314 x _68312 _68313)). Qed.
Lemma lem5221550 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5221551 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term678 x _68313 _68314 _68312) = (term679 x _68313 _68314 _68312).
Proof. exact (@lem5221550 (_68312 = (@EMPTY real)) (term81 _68312 _68314) (term680 x _68313 _68314 _68312)). Qed.
Lemma lem5221577 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5221578 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term680 x _68313 _68314 _68312) = (term681 _68314 x _68312 _68313).
Proof. exact (@lem5221577 (term575 _68314 _68312) (term487 x _68312 _68313)). Qed.
Lemma lem5221584 (_68312 : real -> Prop) (_68314 : real) : (term682 _68312 _68314) = (term682 _68312 _68314).
Proof. exact (eq_refl (term682 _68312 _68314)). Qed.
Lemma lem5221585 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term683 x _68313 _68314 _68312) = (term674 _68314 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221584 _68312 _68314) (@lem5221578 _68314 x _68312 _68313)). Qed.
Lemma lem5221596 (_68312 : real -> Prop) : (term175 _68312) = (term175 _68312).
Proof. exact (eq_refl (term175 _68312)). Qed.
Lemma lem5221597 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term679 x _68313 _68314 _68312) = (term675 _68314 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221596 _68312) (@lem5221585 _68314 x _68312 _68313)). Qed.
Lemma lem5221608 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term678 x _68313 _68314 _68312) = (term675 _68314 x _68312 _68313).
Proof. exact (TRANS (@lem5221551 x _68313 _68314 _68312) (@lem5221597 _68314 x _68312 _68313)). Qed.
Lemma lem5221609 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : ((term532 x _68313 _68312 _68314) = (term678 x _68313 _68314 _68312)) = ((term675 _68314 x _68312 _68313) = (term675 _68314 x _68312 _68313)).
Proof. exact (MK_COMB (@lem5221546 _68314 x _68312 _68313) (@lem5221608 _68314 x _68312 _68313)). Qed.
Lemma lem5221611 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5221612 (x : Prop) : (x = x) = True.
Proof. exact (@lem5221611 Prop x). Qed.
Lemma lem5221613 (_68314 : real) (x : type1021) (_68312 : real -> Prop) (_68313 : real) : ((term675 _68314 x _68312 _68313) = (term675 _68314 x _68312 _68313)) = True.
Proof. exact (@lem5221612 (term675 _68314 x _68312 _68313)). Qed.
Lemma lem5221614 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : ((term532 x _68313 _68312 _68314) = (term678 x _68313 _68314 _68312)) = True.
Proof. exact (TRANS (@lem5221609 _68314 x _68312 _68313) (@lem5221613 _68314 x _68312 _68313)). Qed.
Lemma lem5221615 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : True = ((term532 x _68313 _68312 _68314) = (term678 x _68313 _68314 _68312)).
Proof. exact (SYM (@lem5221614 x _68313 _68314 _68312)). Qed.
Lemma lem5221616 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term532 x _68313 _68312 _68314) = (term678 x _68313 _68314 _68312).
Proof. exact (EQ_MP (@lem5221615 x _68313 _68314 _68312) (@lem0)). Qed.
Lemma lem5221617 (_68313 : real) (_68314 : real) (_68312 : real -> Prop) (x : type1021) (h1 : term338 x) : term678 x _68313 _68314 _68312.
Proof. exact (EQ_MP (@lem5221616 x _68313 _68314 _68312) (@lem5220358 _68313 _68312 _68314 x h1)). Qed.
Lemma lem5221619 (b : Prop) (a : Prop) : (a \/ b) = (term557 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5221620 (x : type1021) (_68313 : real) (_68312 : real -> Prop) (_68314 : real) : (term678 x _68313 _68314 _68312) = (term684 x _68313 _68312 _68314).
Proof. exact (@lem5221619 (term685 x _68313 _68314 _68312) (term81 _68312 _68314)). Qed.
Lemma lem5221622 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5221623 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term686 x _68313 _68314 _68312) = (term687 x _68313 _68314 _68312).
Proof. exact (@lem5221622 (_68312 = (@EMPTY real)) (term680 x _68313 _68314 _68312)). Qed.
Lemma lem5221625 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5221626 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term688 x _68313 _68314 _68312) = (term689 x _68313 _68314 _68312).
Proof. exact (@lem5221625 (term487 x _68312 _68313) (term575 _68314 _68312)). Qed.
Lemma lem5221628 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5221629 (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term604 x _68312 _68313) = (term584 x _68312 _68313).
Proof. exact (@lem5221628 (term584 x _68312 _68313)). Qed.
Lemma lem5221630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5221631 (x : type1021) (_68312 : real -> Prop) (_68313 : real) : (term605 x _68312 _68313) = (term606 x _68312 _68313).
Proof. exact (MK_COMB (@lem5221630) (@lem5221629 x _68312 _68313)). Qed.
Lemma lem5221633 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5221634 (_68314 : real) (_68312 : real -> Prop) : (term580 _68314 _68312) = (@IN real _68314 _68312).
Proof. exact (@lem5221633 (@IN real _68314 _68312)). Qed.
Lemma lem5221635 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term689 x _68313 _68314 _68312) = (term690 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5221631 x _68312 _68313) (@lem5221634 _68314 _68312)). Qed.
Lemma lem5221636 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term688 x _68313 _68314 _68312) = (term690 x _68313 _68314 _68312).
Proof. exact (TRANS (@lem5221626 x _68313 _68314 _68312) (@lem5221635 x _68313 _68314 _68312)). Qed.
Lemma lem5221637 (_68312 : real -> Prop) : (term61 _68312) = (term61 _68312).
Proof. exact (eq_refl (term61 _68312)). Qed.
Lemma lem5221638 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term687 x _68313 _68314 _68312) = (term691 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5221637 _68312) (@lem5221636 x _68313 _68314 _68312)). Qed.
Lemma lem5221639 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term686 x _68313 _68314 _68312) = (term691 x _68313 _68314 _68312).
Proof. exact (TRANS (@lem5221623 x _68313 _68314 _68312) (@lem5221638 x _68313 _68314 _68312)). Qed.
Lemma lem5221640 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5221641 (x : type1021) (_68313 : real) (_68314 : real) (_68312 : real -> Prop) : (term692 x _68313 _68314 _68312) = (term693 x _68313 _68314 _68312).
Proof. exact (MK_COMB (@lem5221640) (@lem5221639 x _68313 _68314 _68312)). Qed.
Lemma lem5221642 (_68312 : real -> Prop) (_68314 : real) : (term81 _68312 _68314) = (term81 _68312 _68314).
Proof. exact (eq_refl (term81 _68312 _68314)). Qed.
Lemma lem5221643 (x : type1021) (_68313 : real) (_68312 : real -> Prop) (_68314 : real) : (term684 x _68313 _68312 _68314) = (term694 x _68313 _68312 _68314).
Proof. exact (MK_COMB (@lem5221641 x _68313 _68314 _68312) (@lem5221642 _68312 _68314)). Qed.
Lemma lem5221644 (x : type1021) (_68313 : real) (_68312 : real -> Prop) (_68314 : real) : (term678 x _68313 _68314 _68312) = (term694 x _68313 _68312 _68314).
Proof. exact (TRANS (@lem5221620 x _68313 _68312 _68314) (@lem5221643 x _68313 _68312 _68314)). Qed.
Lemma lem5221646 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s b) (h3 : term9 s) (h4 : term149 b s x') : term695 x b s.
Proof. exact (conj (@lem5221462 x b s x' h1 h2 h3 h4) (@lem5221469 b s x' h4)). Qed.
Lemma lem5221647 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s b) (h3 : term9 s) (h4 : term149 b s x') : term696 x b s.
Proof. exact (conj (@lem5221258 s h3) (@lem5221646 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221649 (_68313 : real) (_68312 : real -> Prop) (_68314 : real) (x : type1021) (h1 : term338 x) : term694 x _68313 _68312 _68314.
Proof. exact (EQ_MP (@lem5221644 x _68313 _68312 _68314) (@lem5221617 _68313 _68314 _68312 x h1)). Qed.
Lemma lem5221650 (s : real -> Prop) (b : real) (x : type1021) (h1 : term338 x) : term697 x s b.
Proof. exact (@lem5221649 b s b x h1). Qed.
Lemma lem5221653 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s b) (h3 : term9 s) (h4 : term149 b s x') : term81 s b.
Proof. exact (@lem5221650 s b x h1 (@lem5221647 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221654 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b s x') : term698 s b.
Proof. exact (fun h0 : term533 s b => @lem5221653 x b s x' h1 h0 h2 h3). Qed.
Lemma lem5221656 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5221657 (s : real -> Prop) (b : real) : (term698 s b) = (term81 s b).
Proof. exact (@lem5221656 (term81 s b)). Qed.
Lemma lem5221658 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b s x') : term81 s b.
Proof. exact (EQ_MP (@lem5221657 s b) (@lem5221654 x b s x' h1 h2 h3)). Qed.
Lemma lem5221674 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5221675 (_68319 : real) (_68318 : real) : (term699 _68318 _68319) = (term700 _68319 _68318).
Proof. exact (@lem5221674 (_68318 = _68319) (term527 _68319 _68318)). Qed.
Lemma lem5221683 (_68318 : real) (_68319 : real) : (term701 _68318 _68319) = (term701 _68318 _68319).
Proof. exact (eq_refl (term701 _68318 _68319)). Qed.
Lemma lem5221684 (_68319 : real) (_68318 : real) : (term526 _68318 _68319) = (term702 _68319 _68318).
Proof. exact (MK_COMB (@lem5221683 _68318 _68319) (@lem5221675 _68319 _68318)). Qed.
Lemma lem5221688 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5221689 (_68319 : real) (_68318 : real) : (term702 _68319 _68318) = (term703 _68319 _68318).
Proof. exact (@lem5221688 (_68318 = _68319) (term527 _68318 _68319) (term527 _68319 _68318)). Qed.
Lemma lem5221707 (_68319 : real) (_68318 : real) : (term526 _68318 _68319) = (term703 _68319 _68318).
Proof. exact (TRANS (@lem5221684 _68319 _68318) (@lem5221689 _68319 _68318)). Qed.
Lemma lem5221708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5221709 (_68319 : real) (_68318 : real) : (term704 _68318 _68319) = (term705 _68319 _68318).
Proof. exact (MK_COMB (@lem5221708) (@lem5221707 _68319 _68318)). Qed.
Lemma lem5221727 (_68319 : real) (_68318 : real) : (term703 _68319 _68318) = (term703 _68319 _68318).
Proof. exact (eq_refl (term703 _68319 _68318)). Qed.
Lemma lem5221728 (_68319 : real) (_68318 : real) : ((term526 _68318 _68319) = (term703 _68319 _68318)) = ((term703 _68319 _68318) = (term703 _68319 _68318)).
Proof. exact (MK_COMB (@lem5221709 _68319 _68318) (@lem5221727 _68319 _68318)). Qed.
Lemma lem5221730 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5221731 (x : Prop) : (x = x) = True.
Proof. exact (@lem5221730 Prop x). Qed.
Lemma lem5221732 (_68319 : real) (_68318 : real) : ((term703 _68319 _68318) = (term703 _68319 _68318)) = True.
Proof. exact (@lem5221731 (term703 _68319 _68318)). Qed.
Lemma lem5221733 (_68319 : real) (_68318 : real) : ((term526 _68318 _68319) = (term703 _68319 _68318)) = True.
Proof. exact (TRANS (@lem5221728 _68319 _68318) (@lem5221732 _68319 _68318)). Qed.
Lemma lem5221734 (_68319 : real) (_68318 : real) : True = ((term526 _68318 _68319) = (term703 _68319 _68318)).
Proof. exact (SYM (@lem5221733 _68319 _68318)). Qed.
Lemma lem5221735 (_68319 : real) (_68318 : real) : (term526 _68318 _68319) = (term703 _68319 _68318).
Proof. exact (EQ_MP (@lem5221734 _68319 _68318) (@lem0)). Qed.
Lemma lem5221736 (_68319 : real) (_68318 : real) (h1 : term21) : term703 _68319 _68318.
Proof. exact (EQ_MP (@lem5221735 _68319 _68318) (@lem5220244 _68318 _68319 h1)). Qed.
Lemma lem5221738 (b : Prop) (a : Prop) : (a \/ b) = (term557 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5221739 (_68318 : real) (_68319 : real) : (term703 _68319 _68318) = (term706 _68318 _68319).
Proof. exact (@lem5221738 (term343 _68319 _68318) (_68318 = _68319)). Qed.
Lemma lem5221741 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5221742 (_68319 : real) (_68318 : real) : (term707 _68319 _68318) = (term708 _68319 _68318).
Proof. exact (@lem5221741 (term527 _68318 _68319) (term527 _68319 _68318)). Qed.
Lemma lem5221744 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5221745 (_68318 : real) (_68319 : real) : (term709 _68318 _68319) = (real_le _68318 _68319).
Proof. exact (@lem5221744 (real_le _68318 _68319)). Qed.
Lemma lem5221746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5221747 (_68318 : real) (_68319 : real) : (term710 _68318 _68319) = (term711 _68318 _68319).
Proof. exact (MK_COMB (@lem5221746) (@lem5221745 _68318 _68319)). Qed.
Lemma lem5221749 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5221750 (_68319 : real) (_68318 : real) : (term709 _68319 _68318) = (real_le _68319 _68318).
Proof. exact (@lem5221749 (real_le _68319 _68318)). Qed.
Lemma lem5221751 (_68319 : real) (_68318 : real) : (term708 _68319 _68318) = (term37 _68319 _68318).
Proof. exact (MK_COMB (@lem5221747 _68318 _68319) (@lem5221750 _68319 _68318)). Qed.
Lemma lem5221752 (_68319 : real) (_68318 : real) : (term707 _68319 _68318) = (term37 _68319 _68318).
Proof. exact (TRANS (@lem5221742 _68319 _68318) (@lem5221751 _68319 _68318)). Qed.
Lemma lem5221753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5221754 (_68319 : real) (_68318 : real) : (term712 _68319 _68318) = (term713 _68319 _68318).
Proof. exact (MK_COMB (@lem5221753) (@lem5221752 _68319 _68318)). Qed.
Lemma lem5221755 (_68318 : real) (_68319 : real) : (_68318 = _68319) = (_68318 = _68319).
Proof. exact (eq_refl (_68318 = _68319)). Qed.
Lemma lem5221756 (_68318 : real) (_68319 : real) : (term706 _68318 _68319) = (term714 _68318 _68319).
Proof. exact (MK_COMB (@lem5221754 _68319 _68318) (@lem5221755 _68318 _68319)). Qed.
Lemma lem5221757 (_68318 : real) (_68319 : real) : (term703 _68319 _68318) = (term714 _68318 _68319).
Proof. exact (TRANS (@lem5221739 _68318 _68319) (@lem5221756 _68318 _68319)). Qed.
Lemma lem5221759 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b s x') : term715 s b.
Proof. exact (conj (@lem5221251 x b s x' h1 h2 h3) (@lem5221658 x b s x' h1 h2 h3)). Qed.
Lemma lem5221761 (_68318 : real) (_68319 : real) (h1 : term21) : term714 _68318 _68319.
Proof. exact (EQ_MP (@lem5221757 _68318 _68319) (@lem5221736 _68319 _68318 h1)). Qed.
Lemma lem5221762 (b : real) (s : real -> Prop) (h1 : term21) : term716 b s.
Proof. exact (@lem5221761 b (inf s) h1). Qed.
Lemma lem5221765 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : b = (inf s).
Proof. exact (@lem5221762 b s h2 (@lem5221759 x b s x' h1 h3 h4)). Qed.
Lemma lem5221766 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : term717 b s.
Proof. exact (fun h0 : term718 b s => @lem5221765 x b s x' h1 h2 h3 h4). Qed.
Lemma lem5221768 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5221769 (b : real) (s : real -> Prop) : (term717 b s) = (b = (inf s)).
Proof. exact (@lem5221768 (b = (inf s))). Qed.
Lemma lem5221770 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : b = (inf s).
Proof. exact (EQ_MP (@lem5221769 b s) (@lem5221766 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221772 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : @IN real b s.
Proof. exact (proj1 (@lem5219522 b s x' h1)). Qed.
Lemma lem5221773 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term648 b s.
Proof. exact (fun h0 : term575 b s => @lem5221772 b s x' h1). Qed.
Lemma lem5221775 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5221776 (b : real) (s : real -> Prop) : (term648 b s) = (@IN real b s).
Proof. exact (@lem5221775 (@IN real b s)). Qed.
Lemma lem5221777 (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : @IN real b s.
Proof. exact (EQ_MP (@lem5221776 b s) (@lem5221773 b s x' h1)). Qed.
Lemma lem5221795 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5221796 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term539 _68334 _68335 _68332 _68333) = (term719 _68335 _68334 _68332 _68333).
Proof. exact (@lem5221795 (@IN real _68334 _68335) (term720 _68332 _68334) (term575 _68332 _68333)). Qed.
Lemma lem5221814 (_68333 : real -> Prop) (_68335 : real -> Prop) : (term721 _68333 _68335) = (term721 _68333 _68335).
Proof. exact (eq_refl (term721 _68333 _68335)). Qed.
Lemma lem5221815 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term541 _68334 _68335 _68332 _68333) = (term722 _68335 _68334 _68332 _68333).
Proof. exact (MK_COMB (@lem5221814 _68333 _68335) (@lem5221796 _68335 _68334 _68332 _68333)). Qed.
Lemma lem5221819 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5221820 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term722 _68335 _68334 _68332 _68333) = (term723 _68335 _68334 _68332 _68333).
Proof. exact (@lem5221819 (@IN real _68334 _68335) (term724 _68333 _68335) (term725 _68334 _68332 _68333)). Qed.
Lemma lem5221850 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term541 _68334 _68335 _68332 _68333) = (term723 _68335 _68334 _68332 _68333).
Proof. exact (TRANS (@lem5221815 _68335 _68334 _68332 _68333) (@lem5221820 _68335 _68334 _68332 _68333)). Qed.
Lemma lem5221851 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5221852 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term726 _68334 _68335 _68332 _68333) = (term727 _68335 _68334 _68332 _68333).
Proof. exact (MK_COMB (@lem5221851) (@lem5221850 _68335 _68334 _68332 _68333)). Qed.
Lemma lem5221882 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term723 _68335 _68334 _68332 _68333) = (term723 _68335 _68334 _68332 _68333).
Proof. exact (eq_refl (term723 _68335 _68334 _68332 _68333)). Qed.
Lemma lem5221883 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : ((term541 _68334 _68335 _68332 _68333) = (term723 _68335 _68334 _68332 _68333)) = ((term723 _68335 _68334 _68332 _68333) = (term723 _68335 _68334 _68332 _68333)).
Proof. exact (MK_COMB (@lem5221852 _68335 _68334 _68332 _68333) (@lem5221882 _68335 _68334 _68332 _68333)). Qed.
Lemma lem5221885 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5221886 (x : Prop) : (x = x) = True.
Proof. exact (@lem5221885 Prop x). Qed.
Lemma lem5221887 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : ((term723 _68335 _68334 _68332 _68333) = (term723 _68335 _68334 _68332 _68333)) = True.
Proof. exact (@lem5221886 (term723 _68335 _68334 _68332 _68333)). Qed.
Lemma lem5221888 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : ((term541 _68334 _68335 _68332 _68333) = (term723 _68335 _68334 _68332 _68333)) = True.
Proof. exact (TRANS (@lem5221883 _68335 _68334 _68332 _68333) (@lem5221887 _68335 _68334 _68332 _68333)). Qed.
Lemma lem5221889 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : True = ((term541 _68334 _68335 _68332 _68333) = (term723 _68335 _68334 _68332 _68333)).
Proof. exact (SYM (@lem5221888 _68335 _68334 _68332 _68333)). Qed.
Lemma lem5221890 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term541 _68334 _68335 _68332 _68333) = (term723 _68335 _68334 _68332 _68333).
Proof. exact (EQ_MP (@lem5221889 _68335 _68334 _68332 _68333) (@lem0)). Qed.
Lemma lem5221891 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : term723 _68335 _68334 _68332 _68333.
Proof. exact (EQ_MP (@lem5221890 _68335 _68334 _68332 _68333) (@lem5220531 _68334 _68335 _68332 _68333)). Qed.
Lemma lem5221893 (b : Prop) (a : Prop) : (a \/ b) = (term557 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5221894 (_68332 : real) (_68333 : real -> Prop) (_68334 : real) (_68335 : real -> Prop) : (term723 _68335 _68334 _68332 _68333) = (term728 _68332 _68333 _68334 _68335).
Proof. exact (@lem5221893 (term729 _68335 _68334 _68332 _68333) (@IN real _68334 _68335)). Qed.
Lemma lem5221896 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5221897 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term730 _68335 _68334 _68332 _68333) = (term731 _68335 _68334 _68332 _68333).
Proof. exact (@lem5221896 (term724 _68333 _68335) (term725 _68334 _68332 _68333)). Qed.
Lemma lem5221899 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5221900 (_68333 : real -> Prop) (_68335 : real -> Prop) : (term732 _68333 _68335) = (_68333 = _68335).
Proof. exact (@lem5221899 (_68333 = _68335)). Qed.
Lemma lem5221901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5221902 (_68333 : real -> Prop) (_68335 : real -> Prop) : (term733 _68333 _68335) = (term734 _68333 _68335).
Proof. exact (MK_COMB (@lem5221901) (@lem5221900 _68333 _68335)). Qed.
Lemma lem5221904 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5221905 (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term735 _68334 _68332 _68333) = (term736 _68334 _68332 _68333).
Proof. exact (@lem5221904 (term720 _68332 _68334) (term575 _68332 _68333)). Qed.
Lemma lem5221907 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5221908 (_68332 : real) (_68334 : real) : (term737 _68332 _68334) = (_68332 = _68334).
Proof. exact (@lem5221907 (_68332 = _68334)). Qed.
Lemma lem5221909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5221910 (_68332 : real) (_68334 : real) : (term738 _68332 _68334) = (term739 _68332 _68334).
Proof. exact (MK_COMB (@lem5221909) (@lem5221908 _68332 _68334)). Qed.
Lemma lem5221912 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5221913 (_68332 : real) (_68333 : real -> Prop) : (term580 _68332 _68333) = (@IN real _68332 _68333).
Proof. exact (@lem5221912 (@IN real _68332 _68333)). Qed.
Lemma lem5221914 (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term736 _68334 _68332 _68333) = (term740 _68334 _68332 _68333).
Proof. exact (MK_COMB (@lem5221910 _68332 _68334) (@lem5221913 _68332 _68333)). Qed.
Lemma lem5221915 (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term735 _68334 _68332 _68333) = (term740 _68334 _68332 _68333).
Proof. exact (TRANS (@lem5221905 _68334 _68332 _68333) (@lem5221914 _68334 _68332 _68333)). Qed.
Lemma lem5221916 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term731 _68335 _68334 _68332 _68333) = (term741 _68335 _68334 _68332 _68333).
Proof. exact (MK_COMB (@lem5221902 _68333 _68335) (@lem5221915 _68334 _68332 _68333)). Qed.
Lemma lem5221917 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term730 _68335 _68334 _68332 _68333) = (term741 _68335 _68334 _68332 _68333).
Proof. exact (TRANS (@lem5221897 _68335 _68334 _68332 _68333) (@lem5221916 _68335 _68334 _68332 _68333)). Qed.
Lemma lem5221918 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5221919 (_68335 : real -> Prop) (_68334 : real) (_68332 : real) (_68333 : real -> Prop) : (term742 _68335 _68334 _68332 _68333) = (term743 _68335 _68334 _68332 _68333).
Proof. exact (MK_COMB (@lem5221918) (@lem5221917 _68335 _68334 _68332 _68333)). Qed.
Lemma lem5221920 (_68334 : real) (_68335 : real -> Prop) : (@IN real _68334 _68335) = (@IN real _68334 _68335).
Proof. exact (eq_refl (@IN real _68334 _68335)). Qed.
Lemma lem5221921 (_68332 : real) (_68333 : real -> Prop) (_68334 : real) (_68335 : real -> Prop) : (term728 _68332 _68333 _68334 _68335) = (term744 _68332 _68333 _68334 _68335).
Proof. exact (MK_COMB (@lem5221919 _68335 _68334 _68332 _68333) (@lem5221920 _68334 _68335)). Qed.
Lemma lem5221922 (_68332 : real) (_68333 : real -> Prop) (_68334 : real) (_68335 : real -> Prop) : (term723 _68335 _68334 _68332 _68333) = (term744 _68332 _68333 _68334 _68335).
Proof. exact (TRANS (@lem5221894 _68332 _68333 _68334 _68335) (@lem5221921 _68332 _68333 _68334 _68335)). Qed.
Lemma lem5221924 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : term745 b s.
Proof. exact (conj (@lem5221770 x b s x' h1 h2 h3 h4) (@lem5221777 b s x' h4)). Qed.
Lemma lem5221925 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : term746 b s.
Proof. exact (conj (@lem5220585 s) (@lem5221924 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221927 (_68332 : real) (_68333 : real -> Prop) (_68334 : real) (_68335 : real -> Prop) : term744 _68332 _68333 _68334 _68335.
Proof. exact (EQ_MP (@lem5221922 _68332 _68333 _68334 _68335) (@lem5221891 _68335 _68334 _68332 _68333)). Qed.
Lemma lem5221928 (b : real) (s : real -> Prop) : term747 b s.
Proof. exact (@lem5221927 b s (inf s) s). Qed.
Lemma lem5221931 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : term95 s.
Proof. exact (@lem5221928 b s (@lem5221925 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221932 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : term748 s.
Proof. exact (fun h0 : term106 s => @lem5221931 x b s x' h1 h2 h3 h4). Qed.
Lemma lem5221934 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5221935 (s : real -> Prop) : (term748 s) = (term95 s).
Proof. exact (@lem5221934 (term95 s)). Qed.
Lemma lem5221936 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : term95 s.
Proof. exact (EQ_MP (@lem5221935 s) (@lem5221932 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5221939 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5221941 (s : real -> Prop) : (term106 s) = (term749 s).
Proof. exact (@lem5221939 (term95 s)). Qed.
Lemma lem5221944 (s : real -> Prop) (h1 : term106 s) : term749 s.
Proof. exact (EQ_MP (@lem5221941 s) (@lem5220250 s h1)). Qed.
Lemma lem5221947 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b s x') : False.
Proof. exact (@lem5221944 s h3 (@lem5221936 x b s x' h1 h2 h4 h5)). Qed.
Lemma lem5221948 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b s x') : term750.
Proof. exact (fun h0 : ~ False => @lem5221947 x b s x' h1 h2 h3 h4 h5). Qed.
Lemma lem5221950 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5221951 : term750 = False.
Proof. exact (@lem5221950 False). Qed.
Lemma lem5221952 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b s x') : False.
Proof. exact (EQ_MP (@lem5221951) (@lem5221948 x b s x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5222031 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5219277 s h1)). Qed.
Lemma lem5222032 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5222031 s h1). Qed.
Lemma lem5222034 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5222035 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5222034 (s = (@EMPTY real))). Qed.
Lemma lem5222036 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5222035 s) (@lem5222032 s h1)). Qed.
Lemma lem5222038 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5219277 s h1)). Qed.
Lemma lem5222039 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5222038 s h1). Qed.
Lemma lem5222041 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5222042 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5222041 (s = (@EMPTY real))). Qed.
Lemma lem5222043 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5222042 s) (@lem5222039 s h1)). Qed.
Lemma lem5222045 (s : real -> Prop) (x' : real) (h1 : term80 s x') : @IN real x' s.
Proof. exact (proj1 (@lem5219530 s x' h1)). Qed.
Lemma lem5222046 (s : real -> Prop) (x' : real) (h1 : term80 s x') : term648 x' s.
Proof. exact (fun h0 : term575 x' s => @lem5222045 s x' h1). Qed.
Lemma lem5222048 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5222049 (x' : real) (s : real -> Prop) : (term648 x' s) = (@IN real x' s).
Proof. exact (@lem5222048 (@IN real x' s)). Qed.
Lemma lem5222050 (s : real -> Prop) (x' : real) (h1 : term80 s x') : @IN real x' s.
Proof. exact (EQ_MP (@lem5222049 x' s) (@lem5222046 s x' h1)). Qed.
Lemma lem5222053 (s : real -> Prop) (x' : real) (h1 : term533 s x') : term533 s x'.
Proof. exact (h1). Qed.
Lemma lem5222054 (s : real -> Prop) (x' : real) (h1 : term533 s x') : term649 s x'.
Proof. exact (fun h0 : term81 s x' => @lem5222053 s x' h1). Qed.
Lemma lem5222056 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5222057 (s : real -> Prop) (x' : real) : (term649 s x') = (term533 s x').
Proof. exact (@lem5222056 (term81 s x')). Qed.
Lemma lem5222058 (s : real -> Prop) (x' : real) (h1 : term533 s x') : term533 s x'.
Proof. exact (EQ_MP (@lem5222057 s x') (@lem5222054 s x' h1)). Qed.
Lemma lem5222086 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5222087 (_68324 : real) (_68322 : real -> Prop) : (term180 _68322 _68324) = (term650 _68324 _68322).
Proof. exact (@lem5222086 (term81 _68322 _68324) (term575 _68324 _68322)). Qed.
Lemma lem5222093 (x : type1021) (_68323 : real) (_68322 : real -> Prop) : (term621 x _68323 _68322) = (term621 x _68323 _68322).
Proof. exact (eq_refl (term621 x _68323 _68322)). Qed.
Lemma lem5222094 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term651 x _68323 _68322 _68324) = (term652 x _68323 _68324 _68322).
Proof. exact (MK_COMB (@lem5222093 x _68323 _68322) (@lem5222087 _68324 _68322)). Qed.
Lemma lem5222105 (_68322 : real -> Prop) : (term175 _68322) = (term175 _68322).
Proof. exact (eq_refl (term175 _68322)). Qed.
Lemma lem5222106 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term531 x _68323 _68322 _68324) = (term653 x _68323 _68324 _68322).
Proof. exact (MK_COMB (@lem5222105 _68322) (@lem5222094 x _68323 _68324 _68322)). Qed.
Lemma lem5222117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5222118 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term654 x _68323 _68322 _68324) = (term655 x _68323 _68324 _68322).
Proof. exact (MK_COMB (@lem5222117) (@lem5222106 x _68323 _68324 _68322)). Qed.
Lemma lem5222122 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5222123 (x : type1021) (_68323 : real) (_68322 : real -> Prop) (_68324 : real) : (term656 x _68323 _68322 _68324) = (term531 x _68323 _68322 _68324).
Proof. exact (@lem5222122 (_68322 = (@EMPTY real)) (term486 x _68323 _68322) (term180 _68322 _68324)). Qed.
Lemma lem5222149 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5222150 (_68324 : real) (_68322 : real -> Prop) : (term180 _68322 _68324) = (term650 _68324 _68322).
Proof. exact (@lem5222149 (term81 _68322 _68324) (term575 _68324 _68322)). Qed.
Lemma lem5222156 (x : type1021) (_68323 : real) (_68322 : real -> Prop) : (term621 x _68323 _68322) = (term621 x _68323 _68322).
Proof. exact (eq_refl (term621 x _68323 _68322)). Qed.
Lemma lem5222157 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term651 x _68323 _68322 _68324) = (term652 x _68323 _68324 _68322).
Proof. exact (MK_COMB (@lem5222156 x _68323 _68322) (@lem5222150 _68324 _68322)). Qed.
Lemma lem5222168 (_68322 : real -> Prop) : (term175 _68322) = (term175 _68322).
Proof. exact (eq_refl (term175 _68322)). Qed.
Lemma lem5222169 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term531 x _68323 _68322 _68324) = (term653 x _68323 _68324 _68322).
Proof. exact (MK_COMB (@lem5222168 _68322) (@lem5222157 x _68323 _68324 _68322)). Qed.
Lemma lem5222180 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term656 x _68323 _68322 _68324) = (term653 x _68323 _68324 _68322).
Proof. exact (TRANS (@lem5222123 x _68323 _68322 _68324) (@lem5222169 x _68323 _68324 _68322)). Qed.
Lemma lem5222181 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : ((term531 x _68323 _68322 _68324) = (term656 x _68323 _68322 _68324)) = ((term653 x _68323 _68324 _68322) = (term653 x _68323 _68324 _68322)).
Proof. exact (MK_COMB (@lem5222118 x _68323 _68324 _68322) (@lem5222180 x _68323 _68324 _68322)). Qed.
Lemma lem5222183 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5222184 (x : Prop) : (x = x) = True.
Proof. exact (@lem5222183 Prop x). Qed.
Lemma lem5222185 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : ((term653 x _68323 _68324 _68322) = (term653 x _68323 _68324 _68322)) = True.
Proof. exact (@lem5222184 (term653 x _68323 _68324 _68322)). Qed.
Lemma lem5222186 (x : type1021) (_68323 : real) (_68322 : real -> Prop) (_68324 : real) : ((term531 x _68323 _68322 _68324) = (term656 x _68323 _68322 _68324)) = True.
Proof. exact (TRANS (@lem5222181 x _68323 _68324 _68322) (@lem5222185 x _68323 _68324 _68322)). Qed.
Lemma lem5222187 (x : type1021) (_68323 : real) (_68322 : real -> Prop) (_68324 : real) : True = ((term531 x _68323 _68322 _68324) = (term656 x _68323 _68322 _68324)).
Proof. exact (SYM (@lem5222186 x _68323 _68322 _68324)). Qed.
Lemma lem5222188 (x : type1021) (_68323 : real) (_68322 : real -> Prop) (_68324 : real) : (term531 x _68323 _68322 _68324) = (term656 x _68323 _68322 _68324).
Proof. exact (EQ_MP (@lem5222187 x _68323 _68322 _68324) (@lem0)). Qed.
Lemma lem5222189 (_68323 : real) (_68322 : real -> Prop) (_68324 : real) (x : type1021) (h1 : term338 x) : term656 x _68323 _68322 _68324.
Proof. exact (EQ_MP (@lem5222188 x _68323 _68322 _68324) (@lem5220484 _68323 _68322 _68324 x h1)). Qed.
Lemma lem5222191 (b : Prop) (a : Prop) : (a \/ b) = (term557 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5222192 (_68324 : real) (x : type1021) (_68323 : real) (_68322 : real -> Prop) : (term656 x _68323 _68322 _68324) = (term657 _68324 x _68323 _68322).
Proof. exact (@lem5222191 (term658 _68322 _68324) (term486 x _68323 _68322)). Qed.
Lemma lem5222194 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5222195 (_68322 : real -> Prop) (_68324 : real) : (term659 _68322 _68324) = (term660 _68322 _68324).
Proof. exact (@lem5222194 (_68322 = (@EMPTY real)) (term180 _68322 _68324)). Qed.
Lemma lem5222197 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5222198 (_68322 : real -> Prop) (_68324 : real) : (term661 _68322 _68324) = (term662 _68322 _68324).
Proof. exact (@lem5222197 (term575 _68324 _68322) (term81 _68322 _68324)). Qed.
Lemma lem5222200 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5222201 (_68324 : real) (_68322 : real -> Prop) : (term580 _68324 _68322) = (@IN real _68324 _68322).
Proof. exact (@lem5222200 (@IN real _68324 _68322)). Qed.
Lemma lem5222202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5222203 (_68324 : real) (_68322 : real -> Prop) : (term663 _68324 _68322) = (term69 _68324 _68322).
Proof. exact (MK_COMB (@lem5222202) (@lem5222201 _68324 _68322)). Qed.
Lemma lem5222204 (_68322 : real -> Prop) (_68324 : real) : (term533 _68322 _68324) = (term533 _68322 _68324).
Proof. exact (eq_refl (term533 _68322 _68324)). Qed.
Lemma lem5222205 (_68322 : real -> Prop) (_68324 : real) : (term662 _68322 _68324) = (term80 _68322 _68324).
Proof. exact (MK_COMB (@lem5222203 _68324 _68322) (@lem5222204 _68322 _68324)). Qed.
Lemma lem5222206 (_68322 : real -> Prop) (_68324 : real) : (term661 _68322 _68324) = (term80 _68322 _68324).
Proof. exact (TRANS (@lem5222198 _68322 _68324) (@lem5222205 _68322 _68324)). Qed.
Lemma lem5222207 (_68322 : real -> Prop) : (term61 _68322) = (term61 _68322).
Proof. exact (eq_refl (term61 _68322)). Qed.
Lemma lem5222208 (_68322 : real -> Prop) (_68324 : real) : (term660 _68322 _68324) = (term664 _68322 _68324).
Proof. exact (MK_COMB (@lem5222207 _68322) (@lem5222206 _68322 _68324)). Qed.
Lemma lem5222209 (_68322 : real -> Prop) (_68324 : real) : (term659 _68322 _68324) = (term664 _68322 _68324).
Proof. exact (TRANS (@lem5222195 _68322 _68324) (@lem5222208 _68322 _68324)). Qed.
Lemma lem5222210 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5222211 (_68322 : real -> Prop) (_68324 : real) : (term665 _68322 _68324) = (term666 _68322 _68324).
Proof. exact (MK_COMB (@lem5222210) (@lem5222209 _68322 _68324)). Qed.
Lemma lem5222212 (x : type1021) (_68323 : real) (_68322 : real -> Prop) : (term486 x _68323 _68322) = (term486 x _68323 _68322).
Proof. exact (eq_refl (term486 x _68323 _68322)). Qed.
Lemma lem5222213 (_68324 : real) (x : type1021) (_68323 : real) (_68322 : real -> Prop) : (term657 _68324 x _68323 _68322) = (term667 _68324 x _68323 _68322).
Proof. exact (MK_COMB (@lem5222211 _68322 _68324) (@lem5222212 x _68323 _68322)). Qed.
Lemma lem5222214 (_68324 : real) (x : type1021) (_68323 : real) (_68322 : real -> Prop) : (term656 x _68323 _68322 _68324) = (term667 _68324 x _68323 _68322).
Proof. exact (TRANS (@lem5222192 _68324 x _68323 _68322) (@lem5222213 _68324 x _68323 _68322)). Qed.
Lemma lem5222216 (s : real -> Prop) (x' : real) (h1 : term533 s x') (h2 : term80 s x') : term80 s x'.
Proof. exact (conj (@lem5222050 s x' h2) (@lem5222058 s x' h1)). Qed.
Lemma lem5222217 (s : real -> Prop) (x' : real) (h1 : term533 s x') (h2 : term9 s) (h3 : term80 s x') : term664 s x'.
Proof. exact (conj (@lem5222043 s h2) (@lem5222216 s x' h1 h3)). Qed.
Lemma lem5222219 (_68324 : real) (_68323 : real) (_68322 : real -> Prop) (x : type1021) (h1 : term338 x) : term667 _68324 x _68323 _68322.
Proof. exact (EQ_MP (@lem5222214 _68324 x _68323 _68322) (@lem5222189 _68323 _68322 _68324 x h1)). Qed.
Lemma lem5222220 (x' : real) (_68323 : real) (s : real -> Prop) (x : type1021) (h1 : term338 x) : term667 x' x _68323 s.
Proof. exact (@lem5222219 x' _68323 s x h1). Qed.
Lemma lem5222223 (_68323 : real) (x : type1021) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s x') (h3 : term9 s) (h4 : term80 s x') : term486 x _68323 s.
Proof. exact (@lem5222220 x' _68323 s x h1 (@lem5222217 s x' h2 h3 h4)). Qed.
Lemma lem5222224 (b : real) (x : type1021) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s x') (h3 : term9 s) (h4 : term80 s x') : term486 x b s.
Proof. exact (@lem5222223 b x s x' h1 h2 h3 h4). Qed.
Lemma lem5222225 (b : real) (x : type1021) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s x') (h3 : term9 s) (h4 : term80 s x') : term573 x b s.
Proof. exact (fun h0 : term547 x b s => @lem5222224 b x s x' h1 h2 h3 h4). Qed.
Lemma lem5222227 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5222228 (x : type1021) (b : real) (s : real -> Prop) : (term573 x b s) = (term486 x b s).
Proof. exact (@lem5222227 (term486 x b s)). Qed.
Lemma lem5222229 (b : real) (x : type1021) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s x') (h3 : term9 s) (h4 : term80 s x') : term486 x b s.
Proof. exact (EQ_MP (@lem5222228 x b s) (@lem5222225 b x s x' h1 h2 h3 h4)). Qed.
Lemma lem5222235 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5222236 (b : real) (_68325 : real) (s : real -> Prop) : (term73 s b _68325) = (term574 b _68325 s).
Proof. exact (@lem5222235 (real_le b _68325) (term575 _68325 s)). Qed.
Lemma lem5222242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5222243 (b : real) (_68325 : real) (s : real -> Prop) : (term576 s b _68325) = (term577 b _68325 s).
Proof. exact (MK_COMB (@lem5222242) (@lem5222236 b _68325 s)). Qed.
Lemma lem5222249 (b : real) (_68325 : real) (s : real -> Prop) : (term574 b _68325 s) = (term574 b _68325 s).
Proof. exact (eq_refl (term574 b _68325 s)). Qed.
Lemma lem5222250 (b : real) (_68325 : real) (s : real -> Prop) : ((term73 s b _68325) = (term574 b _68325 s)) = ((term574 b _68325 s) = (term574 b _68325 s)).
Proof. exact (MK_COMB (@lem5222243 b _68325 s) (@lem5222249 b _68325 s)). Qed.
Lemma lem5222252 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5222253 (x : Prop) : (x = x) = True.
Proof. exact (@lem5222252 Prop x). Qed.
Lemma lem5222254 (b : real) (_68325 : real) (s : real -> Prop) : ((term574 b _68325 s) = (term574 b _68325 s)) = True.
Proof. exact (@lem5222253 (term574 b _68325 s)). Qed.
Lemma lem5222255 (b : real) (_68325 : real) (s : real -> Prop) : ((term73 s b _68325) = (term574 b _68325 s)) = True.
Proof. exact (TRANS (@lem5222250 b _68325 s) (@lem5222254 b _68325 s)). Qed.
Lemma lem5222256 (b : real) (_68325 : real) (s : real -> Prop) : True = ((term73 s b _68325) = (term574 b _68325 s)).
Proof. exact (SYM (@lem5222255 b _68325 s)). Qed.
Lemma lem5222257 (b : real) (_68325 : real) (s : real -> Prop) : (term73 s b _68325) = (term574 b _68325 s).
Proof. exact (EQ_MP (@lem5222256 b _68325 s) (@lem0)). Qed.
Lemma lem5222258 (_68325 : real) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term574 b _68325 s.
Proof. exact (EQ_MP (@lem5222257 b _68325 s) (@lem5220372 _68325 b s x' h1)). Qed.
Lemma lem5222260 (b : Prop) (a : Prop) : (a \/ b) = (term557 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5222261 (s : real -> Prop) (b : real) (_68325 : real) : (term574 b _68325 s) = (term578 s b _68325).
Proof. exact (@lem5222260 (term575 _68325 s) (real_le b _68325)). Qed.
Lemma lem5222263 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5222264 (_68325 : real) (s : real -> Prop) : (term580 _68325 s) = (@IN real _68325 s).
Proof. exact (@lem5222263 (@IN real _68325 s)). Qed.
Lemma lem5222265 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5222266 (_68325 : real) (s : real -> Prop) : (term581 _68325 s) = (term582 _68325 s).
Proof. exact (MK_COMB (@lem5222265) (@lem5222264 _68325 s)). Qed.
Lemma lem5222267 (b : real) (_68325 : real) : (real_le b _68325) = (real_le b _68325).
Proof. exact (eq_refl (real_le b _68325)). Qed.
Lemma lem5222268 (s : real -> Prop) (b : real) (_68325 : real) : (term578 s b _68325) = (term47 s b _68325).
Proof. exact (MK_COMB (@lem5222266 _68325 s) (@lem5222267 b _68325)). Qed.
Lemma lem5222269 (s : real -> Prop) (b : real) (_68325 : real) : (term574 b _68325 s) = (term47 s b _68325).
Proof. exact (TRANS (@lem5222261 s b _68325) (@lem5222268 s b _68325)). Qed.
Lemma lem5222272 (_68325 : real) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term47 s b _68325.
Proof. exact (EQ_MP (@lem5222269 s b _68325) (@lem5222258 _68325 b s x' h1)). Qed.
Lemma lem5222273 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term149 b s x') : term583 x s b.
Proof. exact (@lem5222272 (x s b) b s x' h1). Qed.
Lemma lem5222276 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s x') (h3 : term9 s) (h4 : term149 b s x') (h5 : term80 s x') : term584 x s b.
Proof. exact (@lem5222273 x b s x' h4 (@lem5222229 b x s x' h1 h2 h3 h5)). Qed.
Lemma lem5222277 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s x') (h3 : term9 s) (h4 : term149 b s x') (h5 : term80 s x') : term585 x s b.
Proof. exact (fun h0 : term487 x s b => @lem5222276 x b s x' h1 h2 h3 h4 h5). Qed.
Lemma lem5222279 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5222280 (x : type1021) (s : real -> Prop) (b : real) : (term585 x s b) = (term584 x s b).
Proof. exact (@lem5222279 (term584 x s b)). Qed.
Lemma lem5222281 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s x') (h3 : term9 s) (h4 : term149 b s x') (h5 : term80 s x') : term584 x s b.
Proof. exact (EQ_MP (@lem5222280 x s b) (@lem5222277 x b s x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5222283 (s : real -> Prop) (x' : real) (h1 : term80 s x') : @IN real x' s.
Proof. exact (proj1 (@lem5219530 s x' h1)). Qed.
Lemma lem5222284 (s : real -> Prop) (x' : real) (h1 : term80 s x') : term648 x' s.
Proof. exact (fun h0 : term575 x' s => @lem5222283 s x' h1). Qed.
Lemma lem5222286 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5222287 (x' : real) (s : real -> Prop) : (term648 x' s) = (@IN real x' s).
Proof. exact (@lem5222286 (@IN real x' s)). Qed.
Lemma lem5222288 (s : real -> Prop) (x' : real) (h1 : term80 s x') : @IN real x' s.
Proof. exact (EQ_MP (@lem5222287 x' s) (@lem5222284 s x' h1)). Qed.
Lemma lem5222306 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5222307 (x : type1021) (_68323 : real) (_68322 : real -> Prop) (_68324 : real) : (term668 x _68323 _68322 _68324) = (term669 x _68323 _68322 _68324).
Proof. exact (@lem5222306 (term575 _68324 _68322) (term487 x _68322 _68323) (term81 _68322 _68324)). Qed.
Lemma lem5222321 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5222322 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term670 x _68323 _68322 _68324) = (term671 _68324 x _68322 _68323).
Proof. exact (@lem5222321 (term81 _68322 _68324) (term487 x _68322 _68323)). Qed.
Lemma lem5222328 (_68324 : real) (_68322 : real -> Prop) : (term672 _68324 _68322) = (term672 _68324 _68322).
Proof. exact (eq_refl (term672 _68324 _68322)). Qed.
Lemma lem5222329 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term669 x _68323 _68322 _68324) = (term673 _68324 x _68322 _68323).
Proof. exact (MK_COMB (@lem5222328 _68324 _68322) (@lem5222322 _68324 x _68322 _68323)). Qed.
Lemma lem5222333 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5222334 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term673 _68324 x _68322 _68323) = (term674 _68324 x _68322 _68323).
Proof. exact (@lem5222333 (term81 _68322 _68324) (term575 _68324 _68322) (term487 x _68322 _68323)). Qed.
Lemma lem5222350 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term669 x _68323 _68322 _68324) = (term674 _68324 x _68322 _68323).
Proof. exact (TRANS (@lem5222329 _68324 x _68322 _68323) (@lem5222334 _68324 x _68322 _68323)). Qed.
Lemma lem5222351 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term668 x _68323 _68322 _68324) = (term674 _68324 x _68322 _68323).
Proof. exact (TRANS (@lem5222307 x _68323 _68322 _68324) (@lem5222350 _68324 x _68322 _68323)). Qed.
Lemma lem5222352 (_68322 : real -> Prop) : (term175 _68322) = (term175 _68322).
Proof. exact (eq_refl (term175 _68322)). Qed.
Lemma lem5222353 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term532 x _68323 _68322 _68324) = (term675 _68324 x _68322 _68323).
Proof. exact (MK_COMB (@lem5222352 _68322) (@lem5222351 _68324 x _68322 _68323)). Qed.
Lemma lem5222364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5222365 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term676 x _68323 _68322 _68324) = (term677 _68324 x _68322 _68323).
Proof. exact (MK_COMB (@lem5222364) (@lem5222353 _68324 x _68322 _68323)). Qed.
Lemma lem5222369 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5222370 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term678 x _68323 _68324 _68322) = (term679 x _68323 _68324 _68322).
Proof. exact (@lem5222369 (_68322 = (@EMPTY real)) (term81 _68322 _68324) (term680 x _68323 _68324 _68322)). Qed.
Lemma lem5222396 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5222397 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term680 x _68323 _68324 _68322) = (term681 _68324 x _68322 _68323).
Proof. exact (@lem5222396 (term575 _68324 _68322) (term487 x _68322 _68323)). Qed.
Lemma lem5222403 (_68322 : real -> Prop) (_68324 : real) : (term682 _68322 _68324) = (term682 _68322 _68324).
Proof. exact (eq_refl (term682 _68322 _68324)). Qed.
Lemma lem5222404 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term683 x _68323 _68324 _68322) = (term674 _68324 x _68322 _68323).
Proof. exact (MK_COMB (@lem5222403 _68322 _68324) (@lem5222397 _68324 x _68322 _68323)). Qed.
Lemma lem5222415 (_68322 : real -> Prop) : (term175 _68322) = (term175 _68322).
Proof. exact (eq_refl (term175 _68322)). Qed.
Lemma lem5222416 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term679 x _68323 _68324 _68322) = (term675 _68324 x _68322 _68323).
Proof. exact (MK_COMB (@lem5222415 _68322) (@lem5222404 _68324 x _68322 _68323)). Qed.
Lemma lem5222427 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term678 x _68323 _68324 _68322) = (term675 _68324 x _68322 _68323).
Proof. exact (TRANS (@lem5222370 x _68323 _68324 _68322) (@lem5222416 _68324 x _68322 _68323)). Qed.
Lemma lem5222428 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : ((term532 x _68323 _68322 _68324) = (term678 x _68323 _68324 _68322)) = ((term675 _68324 x _68322 _68323) = (term675 _68324 x _68322 _68323)).
Proof. exact (MK_COMB (@lem5222365 _68324 x _68322 _68323) (@lem5222427 _68324 x _68322 _68323)). Qed.
Lemma lem5222430 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5222431 (x : Prop) : (x = x) = True.
Proof. exact (@lem5222430 Prop x). Qed.
Lemma lem5222432 (_68324 : real) (x : type1021) (_68322 : real -> Prop) (_68323 : real) : ((term675 _68324 x _68322 _68323) = (term675 _68324 x _68322 _68323)) = True.
Proof. exact (@lem5222431 (term675 _68324 x _68322 _68323)). Qed.
Lemma lem5222433 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : ((term532 x _68323 _68322 _68324) = (term678 x _68323 _68324 _68322)) = True.
Proof. exact (TRANS (@lem5222428 _68324 x _68322 _68323) (@lem5222432 _68324 x _68322 _68323)). Qed.
Lemma lem5222434 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : True = ((term532 x _68323 _68322 _68324) = (term678 x _68323 _68324 _68322)).
Proof. exact (SYM (@lem5222433 x _68323 _68324 _68322)). Qed.
Lemma lem5222435 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term532 x _68323 _68322 _68324) = (term678 x _68323 _68324 _68322).
Proof. exact (EQ_MP (@lem5222434 x _68323 _68324 _68322) (@lem0)). Qed.
Lemma lem5222436 (_68323 : real) (_68324 : real) (_68322 : real -> Prop) (x : type1021) (h1 : term338 x) : term678 x _68323 _68324 _68322.
Proof. exact (EQ_MP (@lem5222435 x _68323 _68324 _68322) (@lem5220500 _68323 _68322 _68324 x h1)). Qed.
Lemma lem5222438 (b : Prop) (a : Prop) : (a \/ b) = (term557 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5222439 (x : type1021) (_68323 : real) (_68322 : real -> Prop) (_68324 : real) : (term678 x _68323 _68324 _68322) = (term684 x _68323 _68322 _68324).
Proof. exact (@lem5222438 (term685 x _68323 _68324 _68322) (term81 _68322 _68324)). Qed.
Lemma lem5222441 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5222442 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term686 x _68323 _68324 _68322) = (term687 x _68323 _68324 _68322).
Proof. exact (@lem5222441 (_68322 = (@EMPTY real)) (term680 x _68323 _68324 _68322)). Qed.
Lemma lem5222444 (a : Prop) (b : Prop) : (term560 a b) = (term561 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5222445 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term688 x _68323 _68324 _68322) = (term689 x _68323 _68324 _68322).
Proof. exact (@lem5222444 (term487 x _68322 _68323) (term575 _68324 _68322)). Qed.
Lemma lem5222447 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5222448 (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term604 x _68322 _68323) = (term584 x _68322 _68323).
Proof. exact (@lem5222447 (term584 x _68322 _68323)). Qed.
Lemma lem5222449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5222450 (x : type1021) (_68322 : real -> Prop) (_68323 : real) : (term605 x _68322 _68323) = (term606 x _68322 _68323).
Proof. exact (MK_COMB (@lem5222449) (@lem5222448 x _68322 _68323)). Qed.
Lemma lem5222452 (a : Prop) : (term579 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5222453 (_68324 : real) (_68322 : real -> Prop) : (term580 _68324 _68322) = (@IN real _68324 _68322).
Proof. exact (@lem5222452 (@IN real _68324 _68322)). Qed.
Lemma lem5222454 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term689 x _68323 _68324 _68322) = (term690 x _68323 _68324 _68322).
Proof. exact (MK_COMB (@lem5222450 x _68322 _68323) (@lem5222453 _68324 _68322)). Qed.
Lemma lem5222455 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term688 x _68323 _68324 _68322) = (term690 x _68323 _68324 _68322).
Proof. exact (TRANS (@lem5222445 x _68323 _68324 _68322) (@lem5222454 x _68323 _68324 _68322)). Qed.
Lemma lem5222456 (_68322 : real -> Prop) : (term61 _68322) = (term61 _68322).
Proof. exact (eq_refl (term61 _68322)). Qed.
Lemma lem5222457 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term687 x _68323 _68324 _68322) = (term691 x _68323 _68324 _68322).
Proof. exact (MK_COMB (@lem5222456 _68322) (@lem5222455 x _68323 _68324 _68322)). Qed.
Lemma lem5222458 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term686 x _68323 _68324 _68322) = (term691 x _68323 _68324 _68322).
Proof. exact (TRANS (@lem5222442 x _68323 _68324 _68322) (@lem5222457 x _68323 _68324 _68322)). Qed.
Lemma lem5222459 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5222460 (x : type1021) (_68323 : real) (_68324 : real) (_68322 : real -> Prop) : (term692 x _68323 _68324 _68322) = (term693 x _68323 _68324 _68322).
Proof. exact (MK_COMB (@lem5222459) (@lem5222458 x _68323 _68324 _68322)). Qed.
Lemma lem5222461 (_68322 : real -> Prop) (_68324 : real) : (term81 _68322 _68324) = (term81 _68322 _68324).
Proof. exact (eq_refl (term81 _68322 _68324)). Qed.
Lemma lem5222462 (x : type1021) (_68323 : real) (_68322 : real -> Prop) (_68324 : real) : (term684 x _68323 _68322 _68324) = (term694 x _68323 _68322 _68324).
Proof. exact (MK_COMB (@lem5222460 x _68323 _68324 _68322) (@lem5222461 _68322 _68324)). Qed.
Lemma lem5222463 (x : type1021) (_68323 : real) (_68322 : real -> Prop) (_68324 : real) : (term678 x _68323 _68324 _68322) = (term694 x _68323 _68322 _68324).
Proof. exact (TRANS (@lem5222439 x _68323 _68322 _68324) (@lem5222462 x _68323 _68322 _68324)). Qed.
Lemma lem5222465 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s x') (h3 : term9 s) (h4 : term149 b s x') (h5 : term80 s x') : term690 x b x' s.
Proof. exact (conj (@lem5222281 x b s x' h1 h2 h3 h4 h5) (@lem5222288 s x' h5)). Qed.
Lemma lem5222466 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s x') (h3 : term9 s) (h4 : term149 b s x') (h5 : term80 s x') : term691 x b x' s.
Proof. exact (conj (@lem5222036 s h3) (@lem5222465 x b s x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5222468 (_68323 : real) (_68322 : real -> Prop) (_68324 : real) (x : type1021) (h1 : term338 x) : term694 x _68323 _68322 _68324.
Proof. exact (EQ_MP (@lem5222463 x _68323 _68322 _68324) (@lem5222436 _68323 _68324 _68322 x h1)). Qed.
Lemma lem5222469 (b : real) (s : real -> Prop) (x' : real) (x : type1021) (h1 : term338 x) : term694 x b s x'.
Proof. exact (@lem5222468 b s x' x h1). Qed.
Lemma lem5222472 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term533 s x') (h3 : term9 s) (h4 : term149 b s x') (h5 : term80 s x') : term81 s x'.
Proof. exact (@lem5222469 b s x' x h1 (@lem5222466 x b s x' h1 h2 h3 h4 h5)). Qed.
Lemma lem5222473 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b s x') (h4 : term80 s x') : term698 s x'.
Proof. exact (fun h0 : term533 s x' => @lem5222472 x b s x' h1 h0 h2 h3 h4). Qed.
Lemma lem5222475 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5222476 (s : real -> Prop) (x' : real) : (term698 s x') = (term81 s x').
Proof. exact (@lem5222475 (term81 s x')). Qed.
Lemma lem5222477 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b s x') (h4 : term80 s x') : term81 s x'.
Proof. exact (EQ_MP (@lem5222476 s x') (@lem5222473 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5222480 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5222482 (s : real -> Prop) (x' : real) : (term533 s x') = (term751 s x').
Proof. exact (@lem5222480 (term81 s x')). Qed.
Lemma lem5222485 (s : real -> Prop) (x' : real) (h1 : term80 s x') : term751 s x'.
Proof. exact (EQ_MP (@lem5222482 s x') (@lem5220392 s x' h1)). Qed.
Lemma lem5222488 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b s x') (h4 : term80 s x') : False.
Proof. exact (@lem5222485 s x' h4 (@lem5222477 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5222489 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b s x') (h4 : term80 s x') : term750.
Proof. exact (fun h0 : ~ False => @lem5222488 x b s x' h1 h2 h3 h4). Qed.
Lemma lem5222491 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5222492 : term750 = False.
Proof. exact (@lem5222491 False). Qed.
Lemma lem5222493 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b s x') (h4 : term80 s x') : False.
Proof. exact (EQ_MP (@lem5222492) (@lem5222489 x b s x' h1 h2 h3 h4)). Qed.
Lemma lem5222494 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b s x') : (term106 s) = False.
Proof. exact (prop_ext (fun h6 : term106 s => @lem5221952 x b s x' h1 h2 h3 h4 h5) (fun h6 : False => @lem5220250 s h3)). Qed.
Lemma lem5222495 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b s x') : False.
Proof. exact (EQ_MP (@lem5222494 x b s x' h1 h2 h3 h4 h5) (@lem5220250 s h3)). Qed.
Lemma lem5222496 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b s x') : (term106 s) = False.
Proof. exact (prop_ext (fun h6 : term106 s => @lem5222495 x b s x' h1 h2 h3 h4 h5) (fun h6 : False => @lem5219831 s h3)). Qed.
Lemma lem5222497 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b s x') : False.
Proof. exact (EQ_MP (@lem5222496 x b s x' h1 h2 h3 h4 h5) (@lem5219831 s h3)). Qed.
Lemma lem5222498 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b s x') : (term106 s) = False.
Proof. exact (prop_ext (fun h6 : term106 s => @lem5222497 x b s x' h1 h2 h3 h4 h5) (fun h6 : False => @lem5219831 s h3)). Qed.
Lemma lem5222499 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b s x') : False.
Proof. exact (EQ_MP (@lem5222498 x b s x' h1 h2 h3 h4 h5) (@lem5219831 s h3)). Qed.
Lemma lem5222500 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : False.
Proof. exact (or_elim (@lem5219521 b s x' h4) (fun h0 : term106 s => @lem5222499 x b s x' h1 h2 h0 h3 h4) (fun h0 : term80 s x' => @lem5222493 x b s x' h1 h3 h4 h0)). Qed.
Lemma lem5222501 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : (term149 b s x') = False.
Proof. exact (prop_ext (fun h5 : term149 b s x' => @lem5222500 x b s x' h1 h2 h3 h4) (fun h5 : False => @lem5219520 b s x' h4)). Qed.
Lemma lem5222502 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : False.
Proof. exact (EQ_MP (@lem5222501 x b s x' h1 h2 h3 h4) (@lem5219520 b s x' h4)). Qed.
Lemma lem5222503 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : (term338 x) = False.
Proof. exact (prop_ext (fun h5 : term338 x => @lem5222502 x b s x' h1 h2 h3 h4) (fun h5 : False => @lem5219461 x h1)). Qed.
Lemma lem5222504 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : False.
Proof. exact (EQ_MP (@lem5222503 x b s x' h1 h2 h3 h4) (@lem5219461 x h1)). Qed.
Lemma lem5222505 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : (term9 s) = False.
Proof. exact (prop_ext (fun h5 : term9 s => @lem5222504 x b s x' h1 h2 h3 h4) (fun h5 : False => @lem5219277 s h3)). Qed.
Lemma lem5222506 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b s x') : False.
Proof. exact (EQ_MP (@lem5222505 x b s x' h1 h2 h3 h4) (@lem5219277 s h3)). Qed.
Lemma lem5222507 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term152 b s) (h4 : term9 s) : False.
Proof. exact (ex_elim (@lem5219262 b s h3) (fun x' : real => fun h0 : term151 b s x' => @lem5222506 x b s x' h1 h2 h4 h0)). Qed.
Lemma lem5222508 (x : type1021) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term14 s) (h4 : term9 s) : False.
Proof. exact (ex_elim (@lem5218366 s h3) (fun b : real => fun h0 : term153 s b => @lem5222507 x b s h1 h2 h0 h4)). Qed.
Lemma lem5222509 (s : real -> Prop) (h1 : term66) (h2 : term21) (h3 : term14 s) (h4 : term9 s) : False.
Proof. exact (ex_elim (@lem5218895 h1) (fun x : type1021 => fun h0 : term340 x => @lem5222508 x s h0 h2 h3 h4)). Qed.
Lemma lem5222510 (s : real -> Prop) (h1 : term66) (h2 : term21) (h3 : term14 s) (h4 : term9 s) : (term9 s) = False.
Proof. exact (prop_ext (fun h5 : term9 s => @lem5222509 s h1 h2 h3 h4) (fun h5 : False => @lem5218102 s h4)). Qed.
Lemma lem5222511 (s : real -> Prop) (h1 : term66) (h2 : term21) (h3 : term14 s) (h4 : term9 s) : False.
Proof. exact (EQ_MP (@lem5222510 s h1 h2 h3 h4) (@lem5218102 s h4)). Qed.
Lemma lem5222512 (s : real -> Prop) (h1 : term66) (h2 : term14 s) (h3 : term9 s) : term19.
Proof. exact (fun h0 : term21 => @lem5222511 s h1 h0 h2 h3). Qed.
Lemma lem5222513 : term19 = term20.
Proof. exact (@lem69 term21). Qed.
Lemma lem5222514 (s : real -> Prop) (h1 : term66) (h2 : term14 s) (h3 : term9 s) : term20.
Proof. exact (EQ_MP (@lem5222513) (@lem5222512 s h1 h2 h3)). Qed.
Lemma lem5222515 (s : real -> Prop) (h1 : term66) (h2 : term14 s) (h3 : term9 s) : term24.
Proof. exact (fun h0 : term45 => @lem5222514 s h1 h2 h3). Qed.
Lemma lem5222516 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : term27.
Proof. exact (fun h0 : term66 => @lem5222515 s h0 h1 h2). Qed.
Lemma lem5222517 (s : real -> Prop) (h1 : term9 s) : term30 s.
Proof. exact (fun h0 : term14 s => @lem5222516 s h0 h1). Qed.
Lemma lem5222518 (s : real -> Prop) : term32 s.
Proof. exact (fun h0 : term9 s => @lem5222517 s h0). Qed.
Lemma lem5222523 : term36.
Proof. exact (fun s : real -> Prop => @lem5222518 s). Qed.
Lemma lem5222524 : term35.
Proof. exact (EQ_MP (@lem5218087) (@lem5222523)). Qed.
Lemma lem5222525 (s : real -> Prop) : term752 s.
Proof. exact (@lem5222524 s). Qed.
Lemma lem5222526 (s : real -> Prop) : (term752 s) = (term15 s).
Proof. exact (eq_refl (term752 s)). Qed.
Lemma lem5222527 (s : real -> Prop) : term15 s.
Proof. exact (EQ_MP (@lem5222526 s) (@lem5222525 s)). Qed.
Lemma lem5222529 (s : real -> Prop) : term15 s.
Proof. exact (@lem5217618 s (@lem5222527 s)). Qed.
Lemma lem5222530 (s : real -> Prop) (h1 : term9 s) : term29 s.
Proof. exact (@lem5222529 s (@lem5217595 s h1)). Qed.
Lemma lem5222531 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : term26.
Proof. exact (@lem5222530 s h2 (@lem5217603 s h1)). Qed.
Lemma lem5222532 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : term23.
Proof. exact (@lem5222531 s h1 h2 (@lem5214027)). Qed.
Lemma lem5222533 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : term19.
Proof. exact (@lem5222532 s h1 h2 (@lem1339697)). Qed.
Lemma lem5222534 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : False.
Proof. exact (@lem5222533 s h1 h2 (@lem1339379)). Qed.
Lemma lem5222535 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : (term14 s) = False.
Proof. exact (prop_ext (fun h3 : term14 s => @lem5222534 s h1 h2) (fun h3 : False => @lem5217603 s h1)). Qed.
Lemma lem5222536 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : False.
Proof. exact (EQ_MP (@lem5222535 s h1 h2) (@lem5217603 s h1)). Qed.
Lemma lem5222537 (s : real -> Prop) (h1 : term9 s) : term13 s.
Proof. exact (fun h0 : term14 s => @lem5222536 s h0 h1). Qed.
Lemma lem5222538 (s : real -> Prop) (h1 : term9 s) : term12 s.
Proof. exact (EQ_MP (@lem5217602 s) (@lem5222537 s h1)). Qed.
Lemma lem5222539 (s : real -> Prop) (h1 : term9 s) : term68 s.
Proof. exact (@lem5222538 s h1 (@lem5217598 s h1)). Qed.
Lemma lem5222540 (s : real -> Prop) : term753 s.
Proof. exact (fun h0 : term9 s => @lem5222539 s h0). Qed.
Lemma lem5222545 : term754.
Proof. exact (fun s : real -> Prop => @lem5222540 s). Qed.
