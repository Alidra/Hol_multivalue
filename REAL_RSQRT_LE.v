Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_RSQRT_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_POW_LE2_spec.
Require Import SQRT_POW_2_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1965642 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1965643 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1965644 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1965643 t1) (@lem1965642 t1)). Qed.
Lemma lem1965645 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1965644 t1 t2). Qed.
Lemma lem1965646 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1965647 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1965646 t1 t2) (@lem1965645 t1 t2)). Qed.
Lemma lem1965648 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1965647 t1 t2 t3). Qed.
Lemma lem1965649 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1965650 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1965649 t1 t2 t3) (@lem1965648 t1 t2 t3)). Qed.
Lemma lem1965651 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1965650 t1 t2 t3)). Qed.
Lemma lem1965653 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1965654 : term8 = term9.
Proof. exact (@lem1965653 term8). Qed.
Lemma lem1965655 : term9 = term8.
Proof. exact (SYM (@lem1965654)). Qed.
Lemma lem1965656 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1965659 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1965660 : term12.
Proof. exact (fun h0 : term11 => @lem1965659 h0). Qed.
Lemma lem1965661 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1965662 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1965663 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1965661 h2 (@lem1965662 h1)). Qed.
Lemma lem1965664 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1965663 h1 h0). Qed.
Lemma lem1965665 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1965666 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1965664 h1 (@lem1965665 h2)). Qed.
Lemma lem1965667 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1965666 h0 h1). Qed.
Lemma lem1965668 : term14.
Proof. exact (fun h0 : term12 => @lem1965667 h0). Qed.
Lemma lem1965671 : term12.
Proof. exact (@lem1965668 (@lem1965660)). Qed.
Lemma lem1965697 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1965698 : term15 = term16.
Proof. exact (@lem1965697 term17). Qed.
Lemma lem1965715 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1965716 : term19 = term20.
Proof. exact (MK_COMB (@lem1965715) (@lem1965698)). Qed.
Lemma lem1965719 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1965726 : term11 = term22.
Proof. exact (MK_COMB (@lem1965719) (@lem1965716)). Qed.
Lemma lem1965735 (x : real) (y : real) (n : nat) : (term23 x y n) = (term23 x y n).
Proof. exact (eq_refl (term23 x y n)). Qed.
Lemma lem1965736 (x : real) (n : nat) : (term24 x n) = (term24 x n).
Proof. exact (fun_ext (fun y : real => @lem1965735 x y n)). Qed.
Lemma lem1965737 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1965738 (x : real) (n : nat) : (term25 x n) = (term25 x n).
Proof. exact (MK_COMB (@lem1965737) (@lem1965736 x n)). Qed.
Lemma lem1965739 (n : nat) : (term26 n) = (term26 n).
Proof. exact (fun_ext (fun x : real => @lem1965738 x n)). Qed.
Lemma lem1965740 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1965741 (n : nat) : (term27 n) = (term27 n).
Proof. exact (MK_COMB (@lem1965740) (@lem1965739 n)). Qed.
Lemma lem1965742 : term28 = term28.
Proof. exact (fun_ext (fun n : nat => @lem1965741 n)). Qed.
Lemma lem1965743 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1965744 : term17 = term17.
Proof. exact (MK_COMB (@lem1965743) (@lem1965742)). Qed.
Lemma lem1965745 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1965746 : term16 = term16.
Proof. exact (MK_COMB (@lem1965745) (@lem1965744)). Qed.
Lemma lem1965751 (x : real) : (term29 x) = (term29 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1965752 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1965751 x)). Qed.
Lemma lem1965753 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1965754 : term31 = term31.
Proof. exact (MK_COMB (@lem1965753) (@lem1965752)). Qed.
Lemma lem1965755 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1965756 : term18 = term18.
Proof. exact (MK_COMB (@lem1965755) (@lem1965754)). Qed.
Lemma lem1965757 : term20 = term20.
Proof. exact (MK_COMB (@lem1965756) (@lem1965746)). Qed.
Lemma lem1965770 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (eq_refl (term32 x y)). Qed.
Lemma lem1965771 (x : real) : (term33 x) = (term33 x).
Proof. exact (fun_ext (fun y : real => @lem1965770 x y)). Qed.
Lemma lem1965772 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1965773 (x : real) : (term34 x) = (term34 x).
Proof. exact (MK_COMB (@lem1965772) (@lem1965771 x)). Qed.
Lemma lem1965774 : term35 = term35.
Proof. exact (fun_ext (fun x : real => @lem1965773 x)). Qed.
Lemma lem1965775 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1965776 : term8 = term8.
Proof. exact (MK_COMB (@lem1965775) (@lem1965774)). Qed.
Lemma lem1965777 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1965778 : term10 = term10.
Proof. exact (MK_COMB (@lem1965777) (@lem1965776)). Qed.
Lemma lem1965779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1965780 : term21 = term21.
Proof. exact (MK_COMB (@lem1965779) (@lem1965778)). Qed.
Lemma lem1965781 : term22 = term22.
Proof. exact (MK_COMB (@lem1965780) (@lem1965757)). Qed.
Lemma lem1965836 : term11 = term22.
Proof. exact (TRANS (@lem1965726) (@lem1965781)). Qed.
Lemma lem1965837 : term22 = term11.
Proof. exact (SYM (@lem1965836)). Qed.
Lemma lem1965838 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1965839 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem1965840 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1965855 (x : real) (y : real) : (term36 x y) = (term37 x y).
Proof. exact (@lem17362 (term38 x y) (term39 x y)). Qed.
Lemma lem1965856 (P : real -> Prop) : (term40 P) = (term41 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1965857 (x : real) : (term42 x) = (term43 x).
Proof. exact (@lem1965856 (term33 x)). Qed.
Lemma lem1965858 (x : real) (y : real) : (term44 x y) = (term32 x y).
Proof. exact (eq_refl (term44 x y)). Qed.
Lemma lem1965859 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1965860 (x : real) (y : real) : (term45 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem1965859) (@lem1965858 x y)). Qed.
Lemma lem1965861 (x : real) (y : real) : (term45 x y) = (term37 x y).
Proof. exact (TRANS (@lem1965860 x y) (@lem1965855 x y)). Qed.
Lemma lem1965862 (x : real) : (term46 x) = (term47 x).
Proof. exact (fun_ext (fun y : real => @lem1965861 x y)). Qed.
Lemma lem1965863 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1965864 (x : real) : (term43 x) = (term48 x).
Proof. exact (MK_COMB (@lem1965863) (@lem1965862 x)). Qed.
Lemma lem1965865 (x : real) : (term42 x) = (term48 x).
Proof. exact (TRANS (@lem1965857 x) (@lem1965864 x)). Qed.
Lemma lem1965866 (P : real -> Prop) : (term40 P) = (term41 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1965867 : term10 = term49.
Proof. exact (@lem1965866 term35). Qed.
Lemma lem1965868 (x : real) : (term50 x) = (term34 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1965869 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1965870 (x : real) : (term51 x) = (term42 x).
Proof. exact (MK_COMB (@lem1965869) (@lem1965868 x)). Qed.
Lemma lem1965871 (x : real) : (term51 x) = (term48 x).
Proof. exact (TRANS (@lem1965870 x) (@lem1965865 x)). Qed.
Lemma lem1965872 : term52 = term53.
Proof. exact (fun_ext (fun x : real => @lem1965871 x)). Qed.
Lemma lem1965873 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1965874 : term49 = term54.
Proof. exact (MK_COMB (@lem1965873) (@lem1965872)). Qed.
Lemma lem1965931 : term10 = term54.
Proof. exact (TRANS (@lem1965867) (@lem1965874)). Qed.
Lemma lem1965932 (h1 : term10) : term54.
Proof. exact (EQ_MP (@lem1965931) (@lem1965838 h1)). Qed.
Lemma lem1965939 (x : real) : (term29 x) = (term55 x).
Proof. exact (@lem17265 (term56 x) ((term57 x) = x)). Qed.
Lemma lem1965940 : term30 = term58.
Proof. exact (fun_ext (fun x : real => @lem1965939 x)). Qed.
Lemma lem1965941 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1965994 : term31 = term59.
Proof. exact (MK_COMB (@lem1965941) (@lem1965940)). Qed.
Lemma lem1965995 (h1 : term31) : term59.
Proof. exact (EQ_MP (@lem1965994) (@lem1965839 h1)). Qed.
Lemma lem1966002 (x : real) (y : real) : (term60 x y) = (term61 x y).
Proof. exact (@lem17045 (term56 x) (real_le x y)). Qed.
Lemma lem1966003 (x : real) (y : real) (n : nat) : (term62 x y n) = (term62 x y n).
Proof. exact (eq_refl (term62 x y n)). Qed.
Lemma lem1966004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1966005 (x : real) (y : real) : (term63 x y) = (term64 x y).
Proof. exact (MK_COMB (@lem1966004) (@lem1966002 x y)). Qed.
Lemma lem1966006 (x : real) (y : real) (n : nat) : (term65 x y n) = (term66 x y n).
Proof. exact (MK_COMB (@lem1966005 x y) (@lem1966003 x y n)). Qed.
Lemma lem1966007 (x : real) (y : real) (n : nat) : (term23 x y n) = (term65 x y n).
Proof. exact (@lem17265 (term67 x y) (term62 x y n)). Qed.
Lemma lem1966008 (x : real) (y : real) (n : nat) : (term23 x y n) = (term66 x y n).
Proof. exact (TRANS (@lem1966007 x y n) (@lem1966006 x y n)). Qed.
Lemma lem1966009 (x : real) (n : nat) : (term24 x n) = (term68 x n).
Proof. exact (fun_ext (fun y : real => @lem1966008 x y n)). Qed.
Lemma lem1966010 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966011 (x : real) (n : nat) : (term25 x n) = (term69 x n).
Proof. exact (MK_COMB (@lem1966010) (@lem1966009 x n)). Qed.
Lemma lem1966012 (n : nat) : (term26 n) = (term70 n).
Proof. exact (fun_ext (fun x : real => @lem1966011 x n)). Qed.
Lemma lem1966013 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966014 (n : nat) : (term27 n) = (term71 n).
Proof. exact (MK_COMB (@lem1966013) (@lem1966012 n)). Qed.
Lemma lem1966015 : term28 = term72.
Proof. exact (fun_ext (fun n : nat => @lem1966014 n)). Qed.
Lemma lem1966016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1966077 : term17 = term73.
Proof. exact (MK_COMB (@lem1966016) (@lem1966015)). Qed.
Lemma lem1966078 (h1 : term17) : term73.
Proof. exact (EQ_MP (@lem1966077) (@lem1965840 h1)). Qed.
Lemma lem1966079 (x : real) (h1 : term48 x) : term48 x.
Proof. exact (h1). Qed.
Lemma lem1966111 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1966112 : term58 = term58.
Proof. exact (fun_ext (fun x : real => @lem1966111 x)). Qed.
Lemma lem1966113 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966114 : term59 = term59.
Proof. exact (MK_COMB (@lem1966113) (@lem1966112)). Qed.
Lemma lem1966115 (h1 : term31) : term59.
Proof. exact (EQ_MP (@lem1966114) (@lem1965995 h1)). Qed.
Lemma lem1966152 (x : real) (y : real) (n : nat) : (term66 x y n) = (term66 x y n).
Proof. exact (eq_refl (term66 x y n)). Qed.
Lemma lem1966153 (x : real) (n : nat) : (term68 x n) = (term68 x n).
Proof. exact (fun_ext (fun y : real => @lem1966152 x y n)). Qed.
Lemma lem1966154 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966155 (x : real) (n : nat) : (term69 x n) = (term69 x n).
Proof. exact (MK_COMB (@lem1966154) (@lem1966153 x n)). Qed.
Lemma lem1966156 (n : nat) : (term70 n) = (term70 n).
Proof. exact (fun_ext (fun x : real => @lem1966155 x n)). Qed.
Lemma lem1966157 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966158 (n : nat) : (term71 n) = (term71 n).
Proof. exact (MK_COMB (@lem1966157) (@lem1966156 n)). Qed.
Lemma lem1966159 : term72 = term72.
Proof. exact (fun_ext (fun n : nat => @lem1966158 n)). Qed.
Lemma lem1966160 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1966161 : term73 = term73.
Proof. exact (MK_COMB (@lem1966160) (@lem1966159)). Qed.
Lemma lem1966162 (h1 : term17) : term73.
Proof. exact (EQ_MP (@lem1966161) (@lem1966078 h1)). Qed.
Lemma lem1966214 (x : real) (y : real) (h1 : term37 x y) : term37 x y.
Proof. exact (h1). Qed.
Lemma lem1966216 (x : real) (y : real) (h1 : term37 x y) : term38 x y.
Proof. exact (proj1 (@lem1966214 x y h1)). Qed.
Lemma lem1966217 (x : real) (y : real) (h1 : term37 x y) : term74 x y.
Proof. exact (proj2 (@lem1966216 x y h1)). Qed.
Lemma lem1966228 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1966229 : term58 = term58.
Proof. exact (fun_ext (fun x : real => @lem1966228 x)). Qed.
Lemma lem1966230 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966232 : term59 = term59.
Proof. exact (MK_COMB (@lem1966230) (@lem1966229)). Qed.
Lemma lem1966233 (h1 : term31) : term59.
Proof. exact (EQ_MP (@lem1966232) (@lem1966115 h1)). Qed.
Lemma lem1966247 (x : real) (y : real) (n : nat) : (term66 x y n) = (term66 x y n).
Proof. exact (eq_refl (term66 x y n)). Qed.
Lemma lem1966248 (x : real) (n : nat) : (term68 x n) = (term68 x n).
Proof. exact (fun_ext (fun y : real => @lem1966247 x y n)). Qed.
Lemma lem1966249 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966250 (x : real) (n : nat) : (term69 x n) = (term69 x n).
Proof. exact (MK_COMB (@lem1966249) (@lem1966248 x n)). Qed.
Lemma lem1966251 (n : nat) : (term70 n) = (term70 n).
Proof. exact (fun_ext (fun x : real => @lem1966250 x n)). Qed.
Lemma lem1966252 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966253 (n : nat) : (term71 n) = (term71 n).
Proof. exact (MK_COMB (@lem1966252) (@lem1966251 n)). Qed.
Lemma lem1966254 : term72 = term72.
Proof. exact (fun_ext (fun n : nat => @lem1966253 n)). Qed.
Lemma lem1966255 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1966257 : term73 = term73.
Proof. exact (MK_COMB (@lem1966255) (@lem1966254)). Qed.
Lemma lem1966258 (h1 : term17) : term73.
Proof. exact (EQ_MP (@lem1966257) (@lem1966162 h1)). Qed.
Lemma lem1966275 (_27639 : real) (h1 : term31) : term75 _27639.
Proof. exact (@lem1966233 h1 _27639). Qed.
Lemma lem1966276 (_27639 : real) : (term75 _27639) = (term55 _27639).
Proof. exact (eq_refl (term75 _27639)). Qed.
Lemma lem1966278 (_27640 : nat) (h1 : term17) : term76 _27640.
Proof. exact (@lem1966258 h1 _27640). Qed.
Lemma lem1966279 (_27640 : nat) : (term76 _27640) = (term71 _27640).
Proof. exact (eq_refl (term76 _27640)). Qed.
Lemma lem1966280 (_27640 : nat) (h1 : term17) : term71 _27640.
Proof. exact (EQ_MP (@lem1966279 _27640) (@lem1966278 _27640 h1)). Qed.
Lemma lem1966281 (_27640 : nat) (_27641 : real) (h1 : term17) : term77 _27640 _27641.
Proof. exact (@lem1966280 _27640 h1 _27641). Qed.
Lemma lem1966282 (_27641 : real) (_27640 : nat) : (term77 _27640 _27641) = (term69 _27641 _27640).
Proof. exact (eq_refl (term77 _27640 _27641)). Qed.
Lemma lem1966283 (_27641 : real) (_27640 : nat) (h1 : term17) : term69 _27641 _27640.
Proof. exact (EQ_MP (@lem1966282 _27641 _27640) (@lem1966281 _27640 _27641 h1)). Qed.
Lemma lem1966284 (_27641 : real) (_27640 : nat) (_27642 : real) (h1 : term17) : term78 _27641 _27640 _27642.
Proof. exact (@lem1966283 _27641 _27640 h1 _27642). Qed.
Lemma lem1966285 (_27641 : real) (_27642 : real) (_27640 : nat) : (term78 _27641 _27640 _27642) = (term66 _27641 _27642 _27640).
Proof. exact (eq_refl (term78 _27641 _27640 _27642)). Qed.
Lemma lem1966286 (_27641 : real) (_27642 : real) (_27640 : nat) (h1 : term17) : term66 _27641 _27642 _27640.
Proof. exact (EQ_MP (@lem1966285 _27641 _27642 _27640) (@lem1966284 _27641 _27640 _27642 h1)). Qed.
Lemma lem1966292 (_27639 : real) (h1 : term31) : term55 _27639.
Proof. exact (EQ_MP (@lem1966276 _27639) (@lem1966275 _27639 h1)). Qed.
Lemma lem1966303 (_27641 : real) (_27642 : real) (_27640 : nat) : (term66 _27641 _27642 _27640) = (term79 _27641 _27642 _27640).
Proof. exact (@lem1965651 (term80 _27641) (term81 _27641 _27642) (term62 _27641 _27642 _27640)). Qed.
Lemma lem1966304 (_27641 : real) (_27642 : real) (_27640 : nat) (h1 : term17) : term79 _27641 _27642 _27640.
Proof. exact (EQ_MP (@lem1966303 _27641 _27642 _27640) (@lem1966286 _27641 _27642 _27640 h1)). Qed.
Lemma lem1966306 (x : real) (y : real) (h1 : term37 x y) : term82 x y.
Proof. exact (proj2 (@lem1966214 x y h1)). Qed.
Lemma lem1966313 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1966314 (_27643 : real) (_27645 : real) (h1 : _27643 = _27645) : _27643 = _27645.
Proof. exact (h1). Qed.
Lemma lem1966315 (_27644 : real) (_27646 : real) (h1 : _27644 = _27646) : _27644 = _27646.
Proof. exact (h1). Qed.
Lemma lem1966316 (_27643 : real) (_27645 : real) (h1 : _27643 = _27645) : (real_le _27643) = (real_le _27645).
Proof. exact (MK_COMB (@lem1966313) (@lem1966314 _27643 _27645 h1)). Qed.
Lemma lem1966317 (_27643 : real) (_27645 : real) (_27644 : real) (_27646 : real) (h1 : _27643 = _27645) (h2 : _27644 = _27646) : (real_le _27643 _27644) = (real_le _27645 _27646).
Proof. exact (MK_COMB (@lem1966316 _27643 _27645 h1) (@lem1966315 _27644 _27646 h2)). Qed.
Lemma lem1966319 (b : Prop) (a : Prop) : term83 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1966320 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : term84 _27645 _27646 _27643 _27644.
Proof. exact (@lem1966319 (real_le _27645 _27646) (real_le _27643 _27644)). Qed.
Lemma lem1966321 (_27643 : real) (_27645 : real) (_27644 : real) (_27646 : real) (h1 : _27643 = _27645) (h2 : _27644 = _27646) : term85 _27645 _27646 _27643 _27644.
Proof. exact (@lem1966320 _27645 _27646 _27643 _27644 (@lem1966317 _27643 _27645 _27644 _27646 h1 h2)). Qed.
Lemma lem1966322 (_27646 : real) (_27644 : real) (_27643 : real) (_27645 : real) (h1 : _27643 = _27645) : term86 _27645 _27646 _27643 _27644.
Proof. exact (fun h0 : _27644 = _27646 => @lem1966321 _27643 _27645 _27644 _27646 h1 h0). Qed.
Lemma lem1966324 (a : Prop) (b : Prop) : (a -> b) = (term87 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1966325 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term86 _27645 _27646 _27643 _27644) = (term88 _27645 _27646 _27643 _27644).
Proof. exact (@lem1966324 (_27644 = _27646) (term85 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966326 (_27646 : real) (_27644 : real) (_27643 : real) (_27645 : real) (h1 : _27643 = _27645) : term88 _27645 _27646 _27643 _27644.
Proof. exact (EQ_MP (@lem1966325 _27645 _27646 _27643 _27644) (@lem1966322 _27646 _27644 _27643 _27645 h1)). Qed.
Lemma lem1966327 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : term89 _27645 _27646 _27643 _27644.
Proof. exact (fun h0 : _27643 = _27645 => @lem1966326 _27646 _27644 _27643 _27645 h0). Qed.
Lemma lem1966329 (a : Prop) (b : Prop) : (a -> b) = (term87 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1966330 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term89 _27645 _27646 _27643 _27644) = (term90 _27645 _27646 _27643 _27644).
Proof. exact (@lem1966329 (_27643 = _27645) (term88 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966331 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : term90 _27645 _27646 _27643 _27644.
Proof. exact (EQ_MP (@lem1966330 _27645 _27646 _27643 _27644) (@lem1966327 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966392 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1966393 (x : real) : (term91 x) = (term91 x).
Proof. exact (@lem1966392 (term91 x)). Qed.
Lemma lem1966394 (x : real) : term92 x.
Proof. exact (fun h0 : term93 x => @lem1966393 x). Qed.
Lemma lem1966396 (p : Prop) : (term94 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1966397 (x : real) : (term92 x) = ((term91 x) = (term91 x)).
Proof. exact (@lem1966396 ((term91 x) = (term91 x))). Qed.
Lemma lem1966398 (x : real) : (term91 x) = (term91 x).
Proof. exact (EQ_MP (@lem1966397 x) (@lem1966394 x)). Qed.
Lemma lem1966400 (x : real) (y : real) (h1 : term37 x y) : term56 y.
Proof. exact (proj1 (@lem1966217 x y h1)). Qed.
Lemma lem1966401 (x : real) (y : real) (h1 : term37 x y) : term95 y.
Proof. exact (fun h0 : term80 y => @lem1966400 x y h1). Qed.
Lemma lem1966403 (p : Prop) : (term94 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1966404 (y : real) : (term95 y) = (term56 y).
Proof. exact (@lem1966403 (term56 y)). Qed.
Lemma lem1966405 (x : real) (y : real) (h1 : term37 x y) : term56 y.
Proof. exact (EQ_MP (@lem1966404 y) (@lem1966401 x y h1)). Qed.
Lemma lem1966411 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1966412 (_27639 : real) : (term55 _27639) = (term96 _27639).
Proof. exact (@lem1966411 ((term57 _27639) = _27639) (term80 _27639)). Qed.
Lemma lem1966420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1966421 (_27639 : real) : (term97 _27639) = (term98 _27639).
Proof. exact (MK_COMB (@lem1966420) (@lem1966412 _27639)). Qed.
Lemma lem1966429 (_27639 : real) : (term96 _27639) = (term96 _27639).
Proof. exact (eq_refl (term96 _27639)). Qed.
Lemma lem1966430 (_27639 : real) : ((term55 _27639) = (term96 _27639)) = ((term96 _27639) = (term96 _27639)).
Proof. exact (MK_COMB (@lem1966421 _27639) (@lem1966429 _27639)). Qed.
Lemma lem1966432 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1966433 (x : Prop) : (x = x) = True.
Proof. exact (@lem1966432 Prop x). Qed.
Lemma lem1966434 (_27639 : real) : ((term96 _27639) = (term96 _27639)) = True.
Proof. exact (@lem1966433 (term96 _27639)). Qed.
Lemma lem1966435 (_27639 : real) : ((term55 _27639) = (term96 _27639)) = True.
Proof. exact (TRANS (@lem1966430 _27639) (@lem1966434 _27639)). Qed.
Lemma lem1966436 (_27639 : real) : True = ((term55 _27639) = (term96 _27639)).
Proof. exact (SYM (@lem1966435 _27639)). Qed.
Lemma lem1966437 (_27639 : real) : (term55 _27639) = (term96 _27639).
Proof. exact (EQ_MP (@lem1966436 _27639) (@lem0)). Qed.
Lemma lem1966438 (_27639 : real) (h1 : term31) : term96 _27639.
Proof. exact (EQ_MP (@lem1966437 _27639) (@lem1966292 _27639 h1)). Qed.
Lemma lem1966440 (b : Prop) (a : Prop) : (a \/ b) = (term99 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1966441 (_27639 : real) : (term96 _27639) = (term100 _27639).
Proof. exact (@lem1966440 (term80 _27639) ((term57 _27639) = _27639)). Qed.
Lemma lem1966443 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1966444 (_27639 : real) : (term102 _27639) = (term56 _27639).
Proof. exact (@lem1966443 (term56 _27639)). Qed.
Lemma lem1966445 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1966446 (_27639 : real) : (term103 _27639) = (term104 _27639).
Proof. exact (MK_COMB (@lem1966445) (@lem1966444 _27639)). Qed.
Lemma lem1966447 (_27639 : real) : ((term57 _27639) = _27639) = ((term57 _27639) = _27639).
Proof. exact (eq_refl ((term57 _27639) = _27639)). Qed.
Lemma lem1966448 (_27639 : real) : (term100 _27639) = (term29 _27639).
Proof. exact (MK_COMB (@lem1966446 _27639) (@lem1966447 _27639)). Qed.
Lemma lem1966449 (_27639 : real) : (term96 _27639) = (term29 _27639).
Proof. exact (TRANS (@lem1966441 _27639) (@lem1966448 _27639)). Qed.
Lemma lem1966452 (_27639 : real) (h1 : term31) : term29 _27639.
Proof. exact (EQ_MP (@lem1966449 _27639) (@lem1966438 _27639 h1)). Qed.
Lemma lem1966453 (y : real) (h1 : term31) : term29 y.
Proof. exact (@lem1966452 y h1). Qed.
Lemma lem1966456 (x : real) (y : real) (h1 : term31) (h2 : term37 x y) : (term57 y) = y.
Proof. exact (@lem1966453 y h1 (@lem1966405 x y h2)). Qed.
Lemma lem1966457 (x : real) (y : real) (h1 : term31) (h2 : term37 x y) : term105 y.
Proof. exact (fun h0 : term106 y => @lem1966456 x y h1 h2). Qed.
Lemma lem1966459 (p : Prop) : (term94 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1966460 (y : real) : (term105 y) = ((term57 y) = y).
Proof. exact (@lem1966459 ((term57 y) = y)). Qed.
Lemma lem1966461 (x : real) (y : real) (h1 : term31) (h2 : term37 x y) : (term57 y) = y.
Proof. exact (EQ_MP (@lem1966460 y) (@lem1966457 x y h1 h2)). Qed.
Lemma lem1966463 (x : real) (y : real) (h1 : term37 x y) : term56 x.
Proof. exact (proj1 (@lem1966216 x y h1)). Qed.
Lemma lem1966464 (x : real) (y : real) (h1 : term37 x y) : term95 x.
Proof. exact (fun h0 : term80 x => @lem1966463 x y h1). Qed.
Lemma lem1966466 (p : Prop) : (term94 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1966467 (x : real) : (term95 x) = (term56 x).
Proof. exact (@lem1966466 (term56 x)). Qed.
Lemma lem1966468 (x : real) (y : real) (h1 : term37 x y) : term56 x.
Proof. exact (EQ_MP (@lem1966467 x) (@lem1966464 x y h1)). Qed.
Lemma lem1966470 (x : real) (y : real) (h1 : term37 x y) : term107 x y.
Proof. exact (proj2 (@lem1966217 x y h1)). Qed.
Lemma lem1966471 (x : real) (y : real) (h1 : term37 x y) : term108 x y.
Proof. exact (fun h0 : term109 x y => @lem1966470 x y h1). Qed.
Lemma lem1966473 (p : Prop) : (term94 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1966474 (x : real) (y : real) : (term108 x y) = (term107 x y).
Proof. exact (@lem1966473 (term107 x y)). Qed.
Lemma lem1966475 (x : real) (y : real) (h1 : term37 x y) : term107 x y.
Proof. exact (EQ_MP (@lem1966474 x y) (@lem1966471 x y h1)). Qed.
Lemma lem1966481 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1966482 (_27641 : real) (_27642 : real) (_27640 : nat) : (term79 _27641 _27642 _27640) = (term110 _27641 _27642 _27640).
Proof. exact (@lem1966481 (term81 _27641 _27642) (term80 _27641) (term62 _27641 _27642 _27640)). Qed.
Lemma lem1966496 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1966497 (_27642 : real) (_27640 : nat) (_27641 : real) : (term111 _27641 _27642 _27640) = (term112 _27642 _27640 _27641).
Proof. exact (@lem1966496 (term62 _27641 _27642 _27640) (term80 _27641)). Qed.
Lemma lem1966503 (_27641 : real) (_27642 : real) : (term113 _27641 _27642) = (term113 _27641 _27642).
Proof. exact (eq_refl (term113 _27641 _27642)). Qed.
Lemma lem1966504 (_27642 : real) (_27640 : nat) (_27641 : real) : (term110 _27641 _27642 _27640) = (term114 _27642 _27640 _27641).
Proof. exact (MK_COMB (@lem1966503 _27641 _27642) (@lem1966497 _27642 _27640 _27641)). Qed.
Lemma lem1966508 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1966509 (_27640 : nat) (_27642 : real) (_27641 : real) : (term114 _27642 _27640 _27641) = (term115 _27640 _27642 _27641).
Proof. exact (@lem1966508 (term62 _27641 _27642 _27640) (term81 _27641 _27642) (term80 _27641)). Qed.
Lemma lem1966525 (_27640 : nat) (_27642 : real) (_27641 : real) : (term110 _27641 _27642 _27640) = (term115 _27640 _27642 _27641).
Proof. exact (TRANS (@lem1966504 _27642 _27640 _27641) (@lem1966509 _27640 _27642 _27641)). Qed.
Lemma lem1966526 (_27640 : nat) (_27642 : real) (_27641 : real) : (term79 _27641 _27642 _27640) = (term115 _27640 _27642 _27641).
Proof. exact (TRANS (@lem1966482 _27641 _27642 _27640) (@lem1966525 _27640 _27642 _27641)). Qed.
Lemma lem1966527 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1966528 (_27640 : nat) (_27642 : real) (_27641 : real) : (term116 _27641 _27642 _27640) = (term117 _27640 _27642 _27641).
Proof. exact (MK_COMB (@lem1966527) (@lem1966526 _27640 _27642 _27641)). Qed.
Lemma lem1966542 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1966543 (_27642 : real) (_27641 : real) : (term61 _27641 _27642) = (term118 _27642 _27641).
Proof. exact (@lem1966542 (term81 _27641 _27642) (term80 _27641)). Qed.
Lemma lem1966549 (_27641 : real) (_27642 : real) (_27640 : nat) : (term119 _27641 _27642 _27640) = (term119 _27641 _27642 _27640).
Proof. exact (eq_refl (term119 _27641 _27642 _27640)). Qed.
Lemma lem1966550 (_27640 : nat) (_27642 : real) (_27641 : real) : (term120 _27640 _27641 _27642) = (term115 _27640 _27642 _27641).
Proof. exact (MK_COMB (@lem1966549 _27641 _27642 _27640) (@lem1966543 _27642 _27641)). Qed.
Lemma lem1966561 (_27640 : nat) (_27642 : real) (_27641 : real) : ((term79 _27641 _27642 _27640) = (term120 _27640 _27641 _27642)) = ((term115 _27640 _27642 _27641) = (term115 _27640 _27642 _27641)).
Proof. exact (MK_COMB (@lem1966528 _27640 _27642 _27641) (@lem1966550 _27640 _27642 _27641)). Qed.
Lemma lem1966563 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1966564 (x : Prop) : (x = x) = True.
Proof. exact (@lem1966563 Prop x). Qed.
Lemma lem1966565 (_27640 : nat) (_27642 : real) (_27641 : real) : ((term115 _27640 _27642 _27641) = (term115 _27640 _27642 _27641)) = True.
Proof. exact (@lem1966564 (term115 _27640 _27642 _27641)). Qed.
Lemma lem1966566 (_27640 : nat) (_27641 : real) (_27642 : real) : ((term79 _27641 _27642 _27640) = (term120 _27640 _27641 _27642)) = True.
Proof. exact (TRANS (@lem1966561 _27640 _27642 _27641) (@lem1966565 _27640 _27642 _27641)). Qed.
Lemma lem1966567 (_27640 : nat) (_27641 : real) (_27642 : real) : True = ((term79 _27641 _27642 _27640) = (term120 _27640 _27641 _27642)).
Proof. exact (SYM (@lem1966566 _27640 _27641 _27642)). Qed.
Lemma lem1966568 (_27640 : nat) (_27641 : real) (_27642 : real) : (term79 _27641 _27642 _27640) = (term120 _27640 _27641 _27642).
Proof. exact (EQ_MP (@lem1966567 _27640 _27641 _27642) (@lem0)). Qed.
Lemma lem1966569 (_27640 : nat) (_27641 : real) (_27642 : real) (h1 : term17) : term120 _27640 _27641 _27642.
Proof. exact (EQ_MP (@lem1966568 _27640 _27641 _27642) (@lem1966304 _27641 _27642 _27640 h1)). Qed.
Lemma lem1966571 (b : Prop) (a : Prop) : (a \/ b) = (term99 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1966572 (_27641 : real) (_27642 : real) (_27640 : nat) : (term120 _27640 _27641 _27642) = (term121 _27641 _27642 _27640).
Proof. exact (@lem1966571 (term61 _27641 _27642) (term62 _27641 _27642 _27640)). Qed.
Lemma lem1966574 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1966575 (_27641 : real) (_27642 : real) : (term124 _27641 _27642) = (term125 _27641 _27642).
Proof. exact (@lem1966574 (term80 _27641) (term81 _27641 _27642)). Qed.
Lemma lem1966577 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1966578 (_27641 : real) : (term102 _27641) = (term56 _27641).
Proof. exact (@lem1966577 (term56 _27641)). Qed.
Lemma lem1966579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1966580 (_27641 : real) : (term126 _27641) = (term127 _27641).
Proof. exact (MK_COMB (@lem1966579) (@lem1966578 _27641)). Qed.
Lemma lem1966582 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1966583 (_27641 : real) (_27642 : real) : (term128 _27641 _27642) = (real_le _27641 _27642).
Proof. exact (@lem1966582 (real_le _27641 _27642)). Qed.
Lemma lem1966584 (_27641 : real) (_27642 : real) : (term125 _27641 _27642) = (term67 _27641 _27642).
Proof. exact (MK_COMB (@lem1966580 _27641) (@lem1966583 _27641 _27642)). Qed.
Lemma lem1966585 (_27641 : real) (_27642 : real) : (term124 _27641 _27642) = (term67 _27641 _27642).
Proof. exact (TRANS (@lem1966575 _27641 _27642) (@lem1966584 _27641 _27642)). Qed.
Lemma lem1966586 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1966587 (_27641 : real) (_27642 : real) : (term129 _27641 _27642) = (term130 _27641 _27642).
Proof. exact (MK_COMB (@lem1966586) (@lem1966585 _27641 _27642)). Qed.
Lemma lem1966588 (_27641 : real) (_27642 : real) (_27640 : nat) : (term62 _27641 _27642 _27640) = (term62 _27641 _27642 _27640).
Proof. exact (eq_refl (term62 _27641 _27642 _27640)). Qed.
Lemma lem1966589 (_27641 : real) (_27642 : real) (_27640 : nat) : (term121 _27641 _27642 _27640) = (term23 _27641 _27642 _27640).
Proof. exact (MK_COMB (@lem1966587 _27641 _27642) (@lem1966588 _27641 _27642 _27640)). Qed.
Lemma lem1966590 (_27641 : real) (_27642 : real) (_27640 : nat) : (term120 _27640 _27641 _27642) = (term23 _27641 _27642 _27640).
Proof. exact (TRANS (@lem1966572 _27641 _27642 _27640) (@lem1966589 _27641 _27642 _27640)). Qed.
Lemma lem1966592 (x : real) (y : real) (h1 : term37 x y) : term131 x y.
Proof. exact (conj (@lem1966468 x y h1) (@lem1966475 x y h1)). Qed.
Lemma lem1966594 (_27641 : real) (_27642 : real) (_27640 : nat) (h1 : term17) : term23 _27641 _27642 _27640.
Proof. exact (EQ_MP (@lem1966590 _27641 _27642 _27640) (@lem1966569 _27640 _27641 _27642 h1)). Qed.
Lemma lem1966595 (x : real) (y : real) (_27640 : nat) (h1 : term17) : term132 x y _27640.
Proof. exact (@lem1966594 x (sqrt y) _27640 h1). Qed.
Lemma lem1966598 (_27640 : nat) (x : real) (y : real) (h1 : term17) (h2 : term37 x y) : term133 x y _27640.
Proof. exact (@lem1966595 x y _27640 h1 (@lem1966592 x y h2)). Qed.
Lemma lem1966599 (x : real) (y : real) (h1 : term17) (h2 : term37 x y) : term134 x y.
Proof. exact (@lem1966598 term135 x y h1 h2). Qed.
Lemma lem1966600 (x : real) (y : real) (h1 : term17) (h2 : term37 x y) : term136 x y.
Proof. exact (fun h0 : term137 x y => @lem1966599 x y h1 h2). Qed.
Lemma lem1966602 (p : Prop) : (term94 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1966603 (x : real) (y : real) : (term136 x y) = (term134 x y).
Proof. exact (@lem1966602 (term134 x y)). Qed.
Lemma lem1966604 (x : real) (y : real) (h1 : term17) (h2 : term37 x y) : term134 x y.
Proof. exact (EQ_MP (@lem1966603 x y) (@lem1966600 x y h1 h2)). Qed.
Lemma lem1966622 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1966623 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term88 _27645 _27646 _27643 _27644) = (term138 _27645 _27646 _27643 _27644).
Proof. exact (@lem1966622 (real_le _27645 _27646) (term139 _27644 _27646) (term81 _27643 _27644)). Qed.
Lemma lem1966641 (_27643 : real) (_27645 : real) : (term140 _27643 _27645) = (term140 _27643 _27645).
Proof. exact (eq_refl (term140 _27643 _27645)). Qed.
Lemma lem1966642 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term90 _27645 _27646 _27643 _27644) = (term141 _27645 _27646 _27643 _27644).
Proof. exact (MK_COMB (@lem1966641 _27643 _27645) (@lem1966623 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966646 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1966647 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term141 _27645 _27646 _27643 _27644) = (term142 _27645 _27646 _27643 _27644).
Proof. exact (@lem1966646 (real_le _27645 _27646) (term139 _27643 _27645) (term143 _27646 _27643 _27644)). Qed.
Lemma lem1966677 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term90 _27645 _27646 _27643 _27644) = (term142 _27645 _27646 _27643 _27644).
Proof. exact (TRANS (@lem1966642 _27645 _27646 _27643 _27644) (@lem1966647 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1966679 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term144 _27645 _27646 _27643 _27644) = (term145 _27645 _27646 _27643 _27644).
Proof. exact (MK_COMB (@lem1966678) (@lem1966677 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966709 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term142 _27645 _27646 _27643 _27644) = (term142 _27645 _27646 _27643 _27644).
Proof. exact (eq_refl (term142 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966710 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : ((term90 _27645 _27646 _27643 _27644) = (term142 _27645 _27646 _27643 _27644)) = ((term142 _27645 _27646 _27643 _27644) = (term142 _27645 _27646 _27643 _27644)).
Proof. exact (MK_COMB (@lem1966679 _27645 _27646 _27643 _27644) (@lem1966709 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966712 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1966713 (x : Prop) : (x = x) = True.
Proof. exact (@lem1966712 Prop x). Qed.
Lemma lem1966714 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : ((term142 _27645 _27646 _27643 _27644) = (term142 _27645 _27646 _27643 _27644)) = True.
Proof. exact (@lem1966713 (term142 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966715 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : ((term90 _27645 _27646 _27643 _27644) = (term142 _27645 _27646 _27643 _27644)) = True.
Proof. exact (TRANS (@lem1966710 _27645 _27646 _27643 _27644) (@lem1966714 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966716 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : True = ((term90 _27645 _27646 _27643 _27644) = (term142 _27645 _27646 _27643 _27644)).
Proof. exact (SYM (@lem1966715 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966717 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term90 _27645 _27646 _27643 _27644) = (term142 _27645 _27646 _27643 _27644).
Proof. exact (EQ_MP (@lem1966716 _27645 _27646 _27643 _27644) (@lem0)). Qed.
Lemma lem1966718 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : term142 _27645 _27646 _27643 _27644.
Proof. exact (EQ_MP (@lem1966717 _27645 _27646 _27643 _27644) (@lem1966331 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966720 (b : Prop) (a : Prop) : (a \/ b) = (term99 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1966721 (_27643 : real) (_27644 : real) (_27645 : real) (_27646 : real) : (term142 _27645 _27646 _27643 _27644) = (term146 _27643 _27644 _27645 _27646).
Proof. exact (@lem1966720 (term147 _27645 _27646 _27643 _27644) (real_le _27645 _27646)). Qed.
Lemma lem1966723 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1966724 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term148 _27645 _27646 _27643 _27644) = (term149 _27645 _27646 _27643 _27644).
Proof. exact (@lem1966723 (term139 _27643 _27645) (term143 _27646 _27643 _27644)). Qed.
Lemma lem1966726 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1966727 (_27643 : real) (_27645 : real) : (term150 _27643 _27645) = (_27643 = _27645).
Proof. exact (@lem1966726 (_27643 = _27645)). Qed.
Lemma lem1966728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1966729 (_27643 : real) (_27645 : real) : (term151 _27643 _27645) = (term152 _27643 _27645).
Proof. exact (MK_COMB (@lem1966728) (@lem1966727 _27643 _27645)). Qed.
Lemma lem1966731 (a : Prop) (b : Prop) : (term122 a b) = (term123 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1966732 (_27646 : real) (_27643 : real) (_27644 : real) : (term153 _27646 _27643 _27644) = (term154 _27646 _27643 _27644).
Proof. exact (@lem1966731 (term139 _27644 _27646) (term81 _27643 _27644)). Qed.
Lemma lem1966734 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1966735 (_27644 : real) (_27646 : real) : (term150 _27644 _27646) = (_27644 = _27646).
Proof. exact (@lem1966734 (_27644 = _27646)). Qed.
Lemma lem1966736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1966737 (_27644 : real) (_27646 : real) : (term151 _27644 _27646) = (term152 _27644 _27646).
Proof. exact (MK_COMB (@lem1966736) (@lem1966735 _27644 _27646)). Qed.
Lemma lem1966739 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1966740 (_27643 : real) (_27644 : real) : (term128 _27643 _27644) = (real_le _27643 _27644).
Proof. exact (@lem1966739 (real_le _27643 _27644)). Qed.
Lemma lem1966741 (_27646 : real) (_27643 : real) (_27644 : real) : (term154 _27646 _27643 _27644) = (term155 _27646 _27643 _27644).
Proof. exact (MK_COMB (@lem1966737 _27644 _27646) (@lem1966740 _27643 _27644)). Qed.
Lemma lem1966742 (_27646 : real) (_27643 : real) (_27644 : real) : (term153 _27646 _27643 _27644) = (term155 _27646 _27643 _27644).
Proof. exact (TRANS (@lem1966732 _27646 _27643 _27644) (@lem1966741 _27646 _27643 _27644)). Qed.
Lemma lem1966743 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term149 _27645 _27646 _27643 _27644) = (term156 _27645 _27646 _27643 _27644).
Proof. exact (MK_COMB (@lem1966729 _27643 _27645) (@lem1966742 _27646 _27643 _27644)). Qed.
Lemma lem1966744 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term148 _27645 _27646 _27643 _27644) = (term156 _27645 _27646 _27643 _27644).
Proof. exact (TRANS (@lem1966724 _27645 _27646 _27643 _27644) (@lem1966743 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966745 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1966746 (_27645 : real) (_27646 : real) (_27643 : real) (_27644 : real) : (term157 _27645 _27646 _27643 _27644) = (term158 _27645 _27646 _27643 _27644).
Proof. exact (MK_COMB (@lem1966745) (@lem1966744 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966747 (_27645 : real) (_27646 : real) : (real_le _27645 _27646) = (real_le _27645 _27646).
Proof. exact (eq_refl (real_le _27645 _27646)). Qed.
Lemma lem1966748 (_27643 : real) (_27644 : real) (_27645 : real) (_27646 : real) : (term146 _27643 _27644 _27645 _27646) = (term159 _27643 _27644 _27645 _27646).
Proof. exact (MK_COMB (@lem1966746 _27645 _27646 _27643 _27644) (@lem1966747 _27645 _27646)). Qed.
Lemma lem1966749 (_27643 : real) (_27644 : real) (_27645 : real) (_27646 : real) : (term142 _27645 _27646 _27643 _27644) = (term159 _27643 _27644 _27645 _27646).
Proof. exact (TRANS (@lem1966721 _27643 _27644 _27645 _27646) (@lem1966748 _27643 _27644 _27645 _27646)). Qed.
Lemma lem1966751 (x : real) (y : real) (h1 : term17) (h2 : term31) (h3 : term37 x y) : term160 x y.
Proof. exact (conj (@lem1966461 x y h2 h3) (@lem1966604 x y h1 h3)). Qed.
Lemma lem1966752 (x : real) (y : real) (h1 : term17) (h2 : term31) (h3 : term37 x y) : term161 x y.
Proof. exact (conj (@lem1966398 x) (@lem1966751 x y h1 h2 h3)). Qed.
Lemma lem1966754 (_27643 : real) (_27644 : real) (_27645 : real) (_27646 : real) : term159 _27643 _27644 _27645 _27646.
Proof. exact (EQ_MP (@lem1966749 _27643 _27644 _27645 _27646) (@lem1966718 _27645 _27646 _27643 _27644)). Qed.
Lemma lem1966755 (x : real) (y : real) : term162 x y.
Proof. exact (@lem1966754 (term91 x) (term57 y) (term91 x) y). Qed.
Lemma lem1966758 (x : real) (y : real) (h1 : term17) (h2 : term31) (h3 : term37 x y) : term39 x y.
Proof. exact (@lem1966755 x y (@lem1966752 x y h1 h2 h3)). Qed.
Lemma lem1966759 (x : real) (y : real) (h1 : term17) (h2 : term31) (h3 : term37 x y) : term163 x y.
Proof. exact (fun h0 : term82 x y => @lem1966758 x y h1 h2 h3). Qed.
Lemma lem1966761 (p : Prop) : (term94 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1966762 (x : real) (y : real) : (term163 x y) = (term39 x y).
Proof. exact (@lem1966761 (term39 x y)). Qed.
Lemma lem1966763 (x : real) (y : real) (h1 : term17) (h2 : term31) (h3 : term37 x y) : term39 x y.
Proof. exact (EQ_MP (@lem1966762 x y) (@lem1966759 x y h1 h2 h3)). Qed.
Lemma lem1966766 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1966768 (x : real) (y : real) : (term82 x y) = (term164 x y).
Proof. exact (@lem1966766 (term39 x y)). Qed.
Lemma lem1966771 (x : real) (y : real) (h1 : term37 x y) : term164 x y.
Proof. exact (EQ_MP (@lem1966768 x y) (@lem1966306 x y h1)). Qed.
Lemma lem1966774 (x : real) (y : real) (h1 : term17) (h2 : term31) (h3 : term37 x y) : False.
Proof. exact (@lem1966771 x y h3 (@lem1966763 x y h1 h2 h3)). Qed.
Lemma lem1966775 (x : real) (y : real) (h1 : term17) (h2 : term31) (h3 : term37 x y) : term165.
Proof. exact (fun h0 : ~ False => @lem1966774 x y h1 h2 h3). Qed.
Lemma lem1966777 (p : Prop) : (term94 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1966778 : term165 = False.
Proof. exact (@lem1966777 False). Qed.
Lemma lem1966779 (x : real) (y : real) (h1 : term17) (h2 : term31) (h3 : term37 x y) : False.
Proof. exact (EQ_MP (@lem1966778) (@lem1966775 x y h1 h2 h3)). Qed.
Lemma lem1966780 (x : real) (y : real) (h1 : term17) (h2 : term31) (h3 : term37 x y) : (term37 x y) = False.
Proof. exact (prop_ext (fun h4 : term37 x y => @lem1966779 x y h1 h2 h3) (fun h4 : False => @lem1966214 x y h3)). Qed.
Lemma lem1966781 (x : real) (y : real) (h1 : term17) (h2 : term31) (h3 : term37 x y) : False.
Proof. exact (EQ_MP (@lem1966780 x y h1 h2 h3) (@lem1966214 x y h3)). Qed.
Lemma lem1966782 (x : real) (h1 : term17) (h2 : term31) (h3 : term48 x) : False.
Proof. exact (ex_elim (@lem1966079 x h3) (fun y : real => fun h0 : term47 x y => @lem1966781 x y h1 h2 h0)). Qed.
Lemma lem1966783 (h1 : term17) (h2 : term31) (h3 : term10) : False.
Proof. exact (ex_elim (@lem1965932 h3) (fun x : real => fun h0 : term53 x => @lem1966782 x h1 h2 h0)). Qed.
Lemma lem1966784 (h1 : term31) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1966783 h0 h1 h2). Qed.
Lemma lem1966785 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1966786 (h1 : term31) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem1966785) (@lem1966784 h1 h2)). Qed.
Lemma lem1966787 (h1 : term10) : term20.
Proof. exact (fun h0 : term31 => @lem1966786 h0 h1). Qed.
Lemma lem1966788 : term22.
Proof. exact (fun h0 : term10 => @lem1966787 h0). Qed.
Lemma lem1966789 : term11.
Proof. exact (EQ_MP (@lem1965837) (@lem1966788)). Qed.
Lemma lem1966791 : term11.
Proof. exact (@lem1965671 (@lem1966789)). Qed.
Lemma lem1966792 (h1 : term10) : term19.
Proof. exact (@lem1966791 (@lem1965656 h1)). Qed.
Lemma lem1966793 (h1 : term10) : term15.
Proof. exact (@lem1966792 h1 (@lem1945848)). Qed.
Lemma lem1966794 (h1 : term10) : False.
Proof. exact (@lem1966793 h1 (@lem1636714)). Qed.
Lemma lem1966795 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1966794 h1) (fun h2 : False => @lem1965656 h1)). Qed.
Lemma lem1966796 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1966795 h1) (@lem1965656 h1)). Qed.
Lemma lem1966797 : term9.
Proof. exact (fun h0 : term10 => @lem1966796 h0). Qed.
Lemma lem1966798 : term8.
Proof. exact (EQ_MP (@lem1965655) (@lem1966797)). Qed.
