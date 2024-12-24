Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2427002_term_abbrevs.
Require Import INT_ENTIRE_spec.
Require Import INT_SUB_0_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032609_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16451_spec.
Require Import thm16452_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982727_spec.
Require Import thm1982729_spec.
Require Import thm1982733_spec.
Require Import thm1982737_spec.
Require Import thm1982745_spec.
Require Import thm1982749_spec.
Require Import thm1982751_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm2318497_spec.
Require Import thm2318526_spec.
Require Import thm2318527_spec.
Require Import thm2318532_spec.
Require Import thm2318533_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2416597 (x : int) (y : int) (h1 : ((int_mul x y) = term0) = (term1 x y)) : ((int_mul x y) = term0) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem2416598 (x : int) (y : int) (h1 : ((int_mul x y) = term0) = (term1 x y)) : (term1 x y) = ((int_mul x y) = term0).
Proof. exact (SYM (@lem2416597 x y h1)). Qed.
Lemma lem2416599 (x : int) (y : int) (h1 : (term1 x y) = ((int_mul x y) = term0)) : (term1 x y) = ((int_mul x y) = term0).
Proof. exact (h1). Qed.
Lemma lem2416600 (x : int) (y : int) (h1 : (term1 x y) = ((int_mul x y) = term0)) : ((int_mul x y) = term0) = (term1 x y).
Proof. exact (SYM (@lem2416599 x y h1)). Qed.
Lemma lem2416601 (x : int) (y : int) : (((int_mul x y) = term0) = (term1 x y)) = ((term1 x y) = ((int_mul x y) = term0)).
Proof. exact (prop_ext (fun h1 : ((int_mul x y) = term0) = (term1 x y) => @lem2416598 x y h1) (fun h1 : (term1 x y) = ((int_mul x y) = term0) => @lem2416600 x y h1)). Qed.
Lemma lem2416602 (x : int) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun y : int => @lem2416601 x y)). Qed.
Lemma lem2416603 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2416604 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2416603) (@lem2416602 x)). Qed.
Lemma lem2416605 : term6 = term7.
Proof. exact (fun_ext (fun x : int => @lem2416604 x)). Qed.
Lemma lem2416606 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2416607 : term8 = term9.
Proof. exact (MK_COMB (@lem2416606) (@lem2416605)). Qed.
Lemma lem2416608 : term9.
Proof. exact (EQ_MP (@lem2416607) (@lem2301483)). Qed.
Lemma lem2416609 (x : int) : term10 x.
Proof. exact (@lem2416608 x). Qed.
Lemma lem2416610 (x : int) : (term10 x) = (term5 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem2416611 (x : int) : term5 x.
Proof. exact (EQ_MP (@lem2416610 x) (@lem2416609 x)). Qed.
Lemma lem2416612 (x : int) (y : int) : term11 x y.
Proof. exact (@lem2416611 x y). Qed.
Lemma lem2416613 (x : int) (y : int) : (term11 x y) = ((term1 x y) = ((int_mul x y) = term0)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem2416617 (x : int) (y : int) (h1 : ((int_sub x y) = term0) = (x = y)) : ((int_sub x y) = term0) = (x = y).
Proof. exact (h1). Qed.
Lemma lem2416618 (x : int) (y : int) (h1 : ((int_sub x y) = term0) = (x = y)) : (x = y) = ((int_sub x y) = term0).
Proof. exact (SYM (@lem2416617 x y h1)). Qed.
Lemma lem2416619 (x : int) (y : int) (h1 : (x = y) = ((int_sub x y) = term0)) : (x = y) = ((int_sub x y) = term0).
Proof. exact (h1). Qed.
Lemma lem2416620 (x : int) (y : int) (h1 : (x = y) = ((int_sub x y) = term0)) : ((int_sub x y) = term0) = (x = y).
Proof. exact (SYM (@lem2416619 x y h1)). Qed.
Lemma lem2416621 (x : int) (y : int) : (((int_sub x y) = term0) = (x = y)) = ((x = y) = ((int_sub x y) = term0)).
Proof. exact (prop_ext (fun h1 : ((int_sub x y) = term0) = (x = y) => @lem2416618 x y h1) (fun h1 : (x = y) = ((int_sub x y) = term0) => @lem2416620 x y h1)). Qed.
Lemma lem2416622 (x : int) : (term12 x) = (term13 x).
Proof. exact (fun_ext (fun y : int => @lem2416621 x y)). Qed.
Lemma lem2416623 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2416624 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2416623) (@lem2416622 x)). Qed.
Lemma lem2416625 : term16 = term17.
Proof. exact (fun_ext (fun x : int => @lem2416624 x)). Qed.
Lemma lem2416626 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2416627 : term18 = term19.
Proof. exact (MK_COMB (@lem2416626) (@lem2416625)). Qed.
Lemma lem2416628 : term19.
Proof. exact (EQ_MP (@lem2416627) (@lem2310063)). Qed.
Lemma lem2416629 (x : int) : term20 x.
Proof. exact (@lem2416628 x). Qed.
Lemma lem2416630 (x : int) : (term20 x) = (term15 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem2416631 (x : int) : term15 x.
Proof. exact (EQ_MP (@lem2416630 x) (@lem2416629 x)). Qed.
Lemma lem2416632 (x : int) (y : int) : term21 x y.
Proof. exact (@lem2416631 x y). Qed.
Lemma lem2416633 (x : int) (y : int) : (term21 x y) = ((x = y) = ((int_sub x y) = term0)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem2416875 (x : int) (y : int) : (x = y) = ((int_sub x y) = term0).
Proof. exact (EQ_MP (@lem2416633 x y) (@lem2416632 x y)). Qed.
Lemma lem2416876 (x : int) : ((term22 x) = term0) = ((term23 x) = term0).
Proof. exact (@lem2416875 (term22 x) term0). Qed.
Lemma lem2416877 : term24 = term25.
Proof. exact (fun_ext (fun x : int => @lem2416876 x)). Qed.
Lemma lem2416878 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2416879 : term26 = term27.
Proof. exact (MK_COMB (@lem2416878) (@lem2416877)). Qed.
Lemma lem2416880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2416881 : term28 = term29.
Proof. exact (MK_COMB (@lem2416880) (@lem2416879)). Qed.
Lemma lem2416903 (x : int) (y : int) : (x = y) = ((int_sub x y) = term0).
Proof. exact (EQ_MP (@lem2416633 x y) (@lem2416632 x y)). Qed.
Lemma lem2416904 (y : int) (x : int) (z : int) : ((int_add x y) = (int_add x z)) = ((term30 y x z) = term0).
Proof. exact (@lem2416903 (int_add x y) (int_add x z)). Qed.
Lemma lem2416905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2416906 (y : int) (x : int) (z : int) : (term31 y x z) = (term32 y x z).
Proof. exact (MK_COMB (@lem2416905) (@lem2416904 y x z)). Qed.
Lemma lem2416910 (x : int) (y : int) : (x = y) = ((int_sub x y) = term0).
Proof. exact (EQ_MP (@lem2416633 x y) (@lem2416632 x y)). Qed.
Lemma lem2416911 (y : int) (z : int) : (y = z) = ((int_sub y z) = term0).
Proof. exact (@lem2416910 y z). Qed.
Lemma lem2416912 (x : int) (y : int) (z : int) : (((int_add x y) = (int_add x z)) = (y = z)) = (((term30 y x z) = term0) = ((int_sub y z) = term0)).
Proof. exact (MK_COMB (@lem2416906 y x z) (@lem2416911 y z)). Qed.
Lemma lem2416913 (x : int) (y : int) : (term33 x y) = (term34 x y).
Proof. exact (fun_ext (fun z : int => @lem2416912 x y z)). Qed.
Lemma lem2416914 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2416915 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem2416914) (@lem2416913 x y)). Qed.
Lemma lem2416916 (x : int) : (term37 x) = (term38 x).
Proof. exact (fun_ext (fun y : int => @lem2416915 x y)). Qed.
Lemma lem2416917 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2416918 (x : int) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem2416917) (@lem2416916 x)). Qed.
Lemma lem2416919 : term41 = term42.
Proof. exact (fun_ext (fun x : int => @lem2416918 x)). Qed.
Lemma lem2416920 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2416921 : term43 = term44.
Proof. exact (MK_COMB (@lem2416920) (@lem2416919)). Qed.
Lemma lem2416922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2416923 : term45 = term46.
Proof. exact (MK_COMB (@lem2416922) (@lem2416921)). Qed.
Lemma lem2416947 (x : int) (y : int) : (x = y) = ((int_sub x y) = term0).
Proof. exact (EQ_MP (@lem2416633 x y) (@lem2416632 x y)). Qed.
Lemma lem2416948 (w : int) (z : int) (x : int) (y : int) : ((term47 w y x z) = (term47 w z x y)) = ((term48 w z x y) = term0).
Proof. exact (@lem2416947 (term47 w y x z) (term47 w z x y)). Qed.
Lemma lem2416949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2416950 (w : int) (z : int) (x : int) (y : int) : (term49 w z x y) = (term50 w z x y).
Proof. exact (MK_COMB (@lem2416949) (@lem2416948 w z x y)). Qed.
Lemma lem2416956 (x : int) (y : int) : (x = y) = ((int_sub x y) = term0).
Proof. exact (EQ_MP (@lem2416633 x y) (@lem2416632 x y)). Qed.
Lemma lem2416957 (w : int) (x : int) : (w = x) = ((int_sub w x) = term0).
Proof. exact (@lem2416956 w x). Qed.
Lemma lem2416958 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2416959 (w : int) (x : int) : (term51 w x) = (term52 w x).
Proof. exact (MK_COMB (@lem2416958) (@lem2416957 w x)). Qed.
Lemma lem2416963 (x : int) (y : int) : (x = y) = ((int_sub x y) = term0).
Proof. exact (EQ_MP (@lem2416633 x y) (@lem2416632 x y)). Qed.
Lemma lem2416964 (y : int) (z : int) : (y = z) = ((int_sub y z) = term0).
Proof. exact (@lem2416963 y z). Qed.
Lemma lem2416965 (w : int) (x : int) (y : int) (z : int) : (term53 w x y z) = (term54 w x y z).
Proof. exact (MK_COMB (@lem2416959 w x) (@lem2416964 y z)). Qed.
Lemma lem2416966 (w : int) (x : int) (y : int) (z : int) : (((term47 w y x z) = (term47 w z x y)) = (term53 w x y z)) = (((term48 w z x y) = term0) = (term54 w x y z)).
Proof. exact (MK_COMB (@lem2416950 w z x y) (@lem2416965 w x y z)). Qed.
Lemma lem2416967 (w : int) (x : int) (y : int) : (term55 w x y) = (term56 w x y).
Proof. exact (fun_ext (fun z : int => @lem2416966 w x y z)). Qed.
Lemma lem2416968 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2416969 (w : int) (x : int) (y : int) : (term57 w x y) = (term58 w x y).
Proof. exact (MK_COMB (@lem2416968) (@lem2416967 w x y)). Qed.
Lemma lem2416970 (w : int) (x : int) : (term59 w x) = (term60 w x).
Proof. exact (fun_ext (fun y : int => @lem2416969 w x y)). Qed.
Lemma lem2416971 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2416972 (w : int) (x : int) : (term61 w x) = (term62 w x).
Proof. exact (MK_COMB (@lem2416971) (@lem2416970 w x)). Qed.
Lemma lem2416973 (w : int) : (term63 w) = (term64 w).
Proof. exact (fun_ext (fun x : int => @lem2416972 w x)). Qed.
Lemma lem2416974 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2416975 (w : int) : (term65 w) = (term66 w).
Proof. exact (MK_COMB (@lem2416974) (@lem2416973 w)). Qed.
Lemma lem2416976 : term67 = term68.
Proof. exact (fun_ext (fun w : int => @lem2416975 w)). Qed.
Lemma lem2416977 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2416978 : term69 = term70.
Proof. exact (MK_COMB (@lem2416977) (@lem2416976)). Qed.
Lemma lem2416979 : term71 = term72.
Proof. exact (MK_COMB (@lem2416923) (@lem2416978)). Qed.
Lemma lem2416980 : term73 = term74.
Proof. exact (MK_COMB (@lem2416881) (@lem2416979)). Qed.
Lemma lem2416981 : term74 = term73.
Proof. exact (SYM (@lem2416980)). Qed.
Lemma lem2417031 (x : int) (y : int) : (term1 x y) = ((int_mul x y) = term0).
Proof. exact (EQ_MP (@lem2416613 x y) (@lem2416612 x y)). Qed.
Lemma lem2417032 (w : int) (x : int) (y : int) (z : int) : (term54 w x y z) = ((term75 w x y z) = term0).
Proof. exact (@lem2417031 (int_sub w x) (int_sub y z)). Qed.
Lemma lem2417035 (w : int) (z : int) (x : int) (y : int) : (term50 w z x y) = (term50 w z x y).
Proof. exact (eq_refl (term50 w z x y)). Qed.
Lemma lem2417036 (w : int) (x : int) (y : int) (z : int) : (((term48 w z x y) = term0) = (term54 w x y z)) = (((term48 w z x y) = term0) = ((term75 w x y z) = term0)).
Proof. exact (MK_COMB (@lem2417035 w z x y) (@lem2417032 w x y z)). Qed.
Lemma lem2417039 (w : int) (x : int) (y : int) : (term56 w x y) = (term76 w x y).
Proof. exact (fun_ext (fun z : int => @lem2417036 w x y z)). Qed.
Lemma lem2417040 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2417041 (w : int) (x : int) (y : int) : (term58 w x y) = (term77 w x y).
Proof. exact (MK_COMB (@lem2417040) (@lem2417039 w x y)). Qed.
Lemma lem2417046 (w : int) (x : int) : (term60 w x) = (term78 w x).
Proof. exact (fun_ext (fun y : int => @lem2417041 w x y)). Qed.
Lemma lem2417047 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2417048 (w : int) (x : int) : (term62 w x) = (term79 w x).
Proof. exact (MK_COMB (@lem2417047) (@lem2417046 w x)). Qed.
Lemma lem2417053 (w : int) : (term64 w) = (term80 w).
Proof. exact (fun_ext (fun x : int => @lem2417048 w x)). Qed.
Lemma lem2417054 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2417055 (w : int) : (term66 w) = (term81 w).
Proof. exact (MK_COMB (@lem2417054) (@lem2417053 w)). Qed.
Lemma lem2417060 : term68 = term82.
Proof. exact (fun_ext (fun w : int => @lem2417055 w)). Qed.
Lemma lem2417061 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2417062 : term70 = term83.
Proof. exact (MK_COMB (@lem2417061) (@lem2417060)). Qed.
Lemma lem2417067 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem2417068 : term72 = term84.
Proof. exact (MK_COMB (@lem2417067) (@lem2417062)). Qed.
Lemma lem2417071 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem2417072 : term74 = term85.
Proof. exact (MK_COMB (@lem2417071) (@lem2417068)). Qed.
Lemma lem2417075 : term85 = term74.
Proof. exact (SYM (@lem2417072)). Qed.
Lemma lem2417076 : term86 = term85.
Proof. exact (@lem2318604 term85). Qed.
Lemma lem2417119 (P : int -> Prop) : (term87 P) = (term88 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2417120 : term89 = term90.
Proof. exact (@lem2417119 term25). Qed.
Lemma lem2417121 (x : int) : (term91 x) = ((term23 x) = term0).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem2417122 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2417124 (x : int) : (term92 x) = (term93 x).
Proof. exact (MK_COMB (@lem2417122) (@lem2417121 x)). Qed.
Lemma lem2417125 : term94 = term95.
Proof. exact (fun_ext (fun x : int => @lem2417124 x)). Qed.
Lemma lem2417126 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417127 : term90 = term96.
Proof. exact (MK_COMB (@lem2417126) (@lem2417125)). Qed.
Lemma lem2417128 : term89 = term96.
Proof. exact (TRANS (@lem2417120) (@lem2417127)). Qed.
Lemma lem2417143 (x : int) (y : int) (z : int) : (term97 x y z) = (term98 x y z).
Proof. exact (@lem17646 ((term30 y x z) = term0) ((int_sub y z) = term0)). Qed.
Lemma lem2417144 (P : int -> Prop) : (term87 P) = (term88 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2417145 (x : int) (y : int) : (term99 x y) = (term100 x y).
Proof. exact (@lem2417144 (term34 x y)). Qed.
Lemma lem2417146 (x : int) (y : int) (z : int) : (term101 x y z) = (((term30 y x z) = term0) = ((int_sub y z) = term0)).
Proof. exact (eq_refl (term101 x y z)). Qed.
Lemma lem2417147 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2417148 (x : int) (y : int) (z : int) : (term102 x y z) = (term97 x y z).
Proof. exact (MK_COMB (@lem2417147) (@lem2417146 x y z)). Qed.
Lemma lem2417149 (x : int) (y : int) (z : int) : (term102 x y z) = (term98 x y z).
Proof. exact (TRANS (@lem2417148 x y z) (@lem2417143 x y z)). Qed.
Lemma lem2417150 (x : int) (y : int) : (term103 x y) = (term104 x y).
Proof. exact (fun_ext (fun z : int => @lem2417149 x y z)). Qed.
Lemma lem2417151 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417152 (x : int) (y : int) : (term100 x y) = (term105 x y).
Proof. exact (MK_COMB (@lem2417151) (@lem2417150 x y)). Qed.
Lemma lem2417153 (x : int) (y : int) : (term99 x y) = (term105 x y).
Proof. exact (TRANS (@lem2417145 x y) (@lem2417152 x y)). Qed.
Lemma lem2417154 (P : int -> Prop) : (term87 P) = (term88 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2417155 (x : int) : (term106 x) = (term107 x).
Proof. exact (@lem2417154 (term38 x)). Qed.
Lemma lem2417156 (x : int) (y : int) : (term108 x y) = (term36 x y).
Proof. exact (eq_refl (term108 x y)). Qed.
Lemma lem2417157 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2417158 (x : int) (y : int) : (term109 x y) = (term99 x y).
Proof. exact (MK_COMB (@lem2417157) (@lem2417156 x y)). Qed.
Lemma lem2417159 (x : int) (y : int) : (term109 x y) = (term105 x y).
Proof. exact (TRANS (@lem2417158 x y) (@lem2417153 x y)). Qed.
Lemma lem2417160 (x : int) : (term110 x) = (term111 x).
Proof. exact (fun_ext (fun y : int => @lem2417159 x y)). Qed.
Lemma lem2417161 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417162 (x : int) : (term107 x) = (term112 x).
Proof. exact (MK_COMB (@lem2417161) (@lem2417160 x)). Qed.
Lemma lem2417163 (x : int) : (term106 x) = (term112 x).
Proof. exact (TRANS (@lem2417155 x) (@lem2417162 x)). Qed.
Lemma lem2417164 (P : int -> Prop) : (term87 P) = (term88 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2417165 : term113 = term114.
Proof. exact (@lem2417164 term42). Qed.
Lemma lem2417166 (x : int) : (term115 x) = (term40 x).
Proof. exact (eq_refl (term115 x)). Qed.
Lemma lem2417167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2417168 (x : int) : (term116 x) = (term106 x).
Proof. exact (MK_COMB (@lem2417167) (@lem2417166 x)). Qed.
Lemma lem2417169 (x : int) : (term116 x) = (term112 x).
Proof. exact (TRANS (@lem2417168 x) (@lem2417163 x)). Qed.
Lemma lem2417170 : term117 = term118.
Proof. exact (fun_ext (fun x : int => @lem2417169 x)). Qed.
Lemma lem2417171 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417172 : term114 = term119.
Proof. exact (MK_COMB (@lem2417171) (@lem2417170)). Qed.
Lemma lem2417173 : term113 = term119.
Proof. exact (TRANS (@lem2417165) (@lem2417172)). Qed.
Lemma lem2417188 (w : int) (x : int) (y : int) (z : int) : (term120 w x y z) = (term121 w x y z).
Proof. exact (@lem17646 ((term48 w z x y) = term0) ((term75 w x y z) = term0)). Qed.
Lemma lem2417189 (P : int -> Prop) : (term87 P) = (term88 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2417190 (w : int) (x : int) (y : int) : (term122 w x y) = (term123 w x y).
Proof. exact (@lem2417189 (term76 w x y)). Qed.
Lemma lem2417191 (w : int) (x : int) (y : int) (z : int) : (term124 w x y z) = (((term48 w z x y) = term0) = ((term75 w x y z) = term0)).
Proof. exact (eq_refl (term124 w x y z)). Qed.
Lemma lem2417192 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2417193 (w : int) (x : int) (y : int) (z : int) : (term125 w x y z) = (term120 w x y z).
Proof. exact (MK_COMB (@lem2417192) (@lem2417191 w x y z)). Qed.
Lemma lem2417194 (w : int) (x : int) (y : int) (z : int) : (term125 w x y z) = (term121 w x y z).
Proof. exact (TRANS (@lem2417193 w x y z) (@lem2417188 w x y z)). Qed.
Lemma lem2417195 (w : int) (x : int) (y : int) : (term126 w x y) = (term127 w x y).
Proof. exact (fun_ext (fun z : int => @lem2417194 w x y z)). Qed.
Lemma lem2417196 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417197 (w : int) (x : int) (y : int) : (term123 w x y) = (term128 w x y).
Proof. exact (MK_COMB (@lem2417196) (@lem2417195 w x y)). Qed.
Lemma lem2417198 (w : int) (x : int) (y : int) : (term122 w x y) = (term128 w x y).
Proof. exact (TRANS (@lem2417190 w x y) (@lem2417197 w x y)). Qed.
Lemma lem2417199 (P : int -> Prop) : (term87 P) = (term88 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2417200 (w : int) (x : int) : (term129 w x) = (term130 w x).
Proof. exact (@lem2417199 (term78 w x)). Qed.
Lemma lem2417201 (w : int) (x : int) (y : int) : (term131 w x y) = (term77 w x y).
Proof. exact (eq_refl (term131 w x y)). Qed.
Lemma lem2417202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2417203 (w : int) (x : int) (y : int) : (term132 w x y) = (term122 w x y).
Proof. exact (MK_COMB (@lem2417202) (@lem2417201 w x y)). Qed.
Lemma lem2417204 (w : int) (x : int) (y : int) : (term132 w x y) = (term128 w x y).
Proof. exact (TRANS (@lem2417203 w x y) (@lem2417198 w x y)). Qed.
Lemma lem2417205 (w : int) (x : int) : (term133 w x) = (term134 w x).
Proof. exact (fun_ext (fun y : int => @lem2417204 w x y)). Qed.
Lemma lem2417206 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417207 (w : int) (x : int) : (term130 w x) = (term135 w x).
Proof. exact (MK_COMB (@lem2417206) (@lem2417205 w x)). Qed.
Lemma lem2417208 (w : int) (x : int) : (term129 w x) = (term135 w x).
Proof. exact (TRANS (@lem2417200 w x) (@lem2417207 w x)). Qed.
Lemma lem2417209 (P : int -> Prop) : (term87 P) = (term88 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2417210 (w : int) : (term136 w) = (term137 w).
Proof. exact (@lem2417209 (term80 w)). Qed.
Lemma lem2417211 (w : int) (x : int) : (term138 w x) = (term79 w x).
Proof. exact (eq_refl (term138 w x)). Qed.
Lemma lem2417212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2417213 (w : int) (x : int) : (term139 w x) = (term129 w x).
Proof. exact (MK_COMB (@lem2417212) (@lem2417211 w x)). Qed.
Lemma lem2417214 (w : int) (x : int) : (term139 w x) = (term135 w x).
Proof. exact (TRANS (@lem2417213 w x) (@lem2417208 w x)). Qed.
Lemma lem2417215 (w : int) : (term140 w) = (term141 w).
Proof. exact (fun_ext (fun x : int => @lem2417214 w x)). Qed.
Lemma lem2417216 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417217 (w : int) : (term137 w) = (term142 w).
Proof. exact (MK_COMB (@lem2417216) (@lem2417215 w)). Qed.
Lemma lem2417218 (w : int) : (term136 w) = (term142 w).
Proof. exact (TRANS (@lem2417210 w) (@lem2417217 w)). Qed.
Lemma lem2417219 (P : int -> Prop) : (term87 P) = (term88 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2417220 : term143 = term144.
Proof. exact (@lem2417219 term82). Qed.
Lemma lem2417221 (w : int) : (term145 w) = (term81 w).
Proof. exact (eq_refl (term145 w)). Qed.
Lemma lem2417222 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2417223 (w : int) : (term146 w) = (term136 w).
Proof. exact (MK_COMB (@lem2417222) (@lem2417221 w)). Qed.
Lemma lem2417224 (w : int) : (term146 w) = (term142 w).
Proof. exact (TRANS (@lem2417223 w) (@lem2417218 w)). Qed.
Lemma lem2417225 : term147 = term148.
Proof. exact (fun_ext (fun w : int => @lem2417224 w)). Qed.
Lemma lem2417226 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417227 : term144 = term149.
Proof. exact (MK_COMB (@lem2417226) (@lem2417225)). Qed.
Lemma lem2417228 : term143 = term149.
Proof. exact (TRANS (@lem2417220) (@lem2417227)). Qed.
Lemma lem2417229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417230 : term150 = term151.
Proof. exact (MK_COMB (@lem2417229) (@lem2417173)). Qed.
Lemma lem2417231 : term152 = term153.
Proof. exact (MK_COMB (@lem2417230) (@lem2417228)). Qed.
Lemma lem2417232 : term154 = term152.
Proof. exact (@lem17045 term44 term83). Qed.
Lemma lem2417233 : term154 = term153.
Proof. exact (TRANS (@lem2417232) (@lem2417231)). Qed.
Lemma lem2417234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417235 : term155 = term156.
Proof. exact (MK_COMB (@lem2417234) (@lem2417128)). Qed.
Lemma lem2417236 : term157 = term158.
Proof. exact (MK_COMB (@lem2417235) (@lem2417233)). Qed.
Lemma lem2417237 : term159 = term157.
Proof. exact (@lem17045 term27 term84). Qed.
Lemma lem2417239 : term159 = term158.
Proof. exact (TRANS (@lem2417237) (@lem2417236)). Qed.
Lemma lem2417242 (x : int) : (term93 x) = (term93 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem2417243 : term95 = term95.
Proof. exact (fun_ext (fun x : int => @lem2417242 x)). Qed.
Lemma lem2417244 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417245 : term96 = term96.
Proof. exact (MK_COMB (@lem2417244) (@lem2417243)). Qed.
Lemma lem2417262 (x : int) (y : int) (z : int) : (term98 x y z) = (term98 x y z).
Proof. exact (eq_refl (term98 x y z)). Qed.
Lemma lem2417263 (x : int) (y : int) : (term104 x y) = (term104 x y).
Proof. exact (fun_ext (fun z : int => @lem2417262 x y z)). Qed.
Lemma lem2417264 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417265 (x : int) (y : int) : (term105 x y) = (term105 x y).
Proof. exact (MK_COMB (@lem2417264) (@lem2417263 x y)). Qed.
Lemma lem2417266 (x : int) : (term111 x) = (term111 x).
Proof. exact (fun_ext (fun y : int => @lem2417265 x y)). Qed.
Lemma lem2417267 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417268 (x : int) : (term112 x) = (term112 x).
Proof. exact (MK_COMB (@lem2417267) (@lem2417266 x)). Qed.
Lemma lem2417269 : term118 = term118.
Proof. exact (fun_ext (fun x : int => @lem2417268 x)). Qed.
Lemma lem2417270 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417271 : term119 = term119.
Proof. exact (MK_COMB (@lem2417270) (@lem2417269)). Qed.
Lemma lem2417288 (w : int) (x : int) (y : int) (z : int) : (term121 w x y z) = (term121 w x y z).
Proof. exact (eq_refl (term121 w x y z)). Qed.
Lemma lem2417289 (w : int) (x : int) (y : int) : (term127 w x y) = (term127 w x y).
Proof. exact (fun_ext (fun z : int => @lem2417288 w x y z)). Qed.
Lemma lem2417290 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417291 (w : int) (x : int) (y : int) : (term128 w x y) = (term128 w x y).
Proof. exact (MK_COMB (@lem2417290) (@lem2417289 w x y)). Qed.
Lemma lem2417292 (w : int) (x : int) : (term134 w x) = (term134 w x).
Proof. exact (fun_ext (fun y : int => @lem2417291 w x y)). Qed.
Lemma lem2417293 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417294 (w : int) (x : int) : (term135 w x) = (term135 w x).
Proof. exact (MK_COMB (@lem2417293) (@lem2417292 w x)). Qed.
Lemma lem2417295 (w : int) : (term141 w) = (term141 w).
Proof. exact (fun_ext (fun x : int => @lem2417294 w x)). Qed.
Lemma lem2417296 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417297 (w : int) : (term142 w) = (term142 w).
Proof. exact (MK_COMB (@lem2417296) (@lem2417295 w)). Qed.
Lemma lem2417298 : term148 = term148.
Proof. exact (fun_ext (fun w : int => @lem2417297 w)). Qed.
Lemma lem2417299 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417300 : term149 = term149.
Proof. exact (MK_COMB (@lem2417299) (@lem2417298)). Qed.
Lemma lem2417301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417302 : term151 = term151.
Proof. exact (MK_COMB (@lem2417301) (@lem2417271)). Qed.
Lemma lem2417303 : term153 = term153.
Proof. exact (MK_COMB (@lem2417302) (@lem2417300)). Qed.
Lemma lem2417304 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417305 : term156 = term156.
Proof. exact (MK_COMB (@lem2417304) (@lem2417245)). Qed.
Lemma lem2417306 : term158 = term158.
Proof. exact (MK_COMB (@lem2417305) (@lem2417303)). Qed.
Lemma lem2417307 : term159 = term158.
Proof. exact (TRANS (@lem2417239) (@lem2417306)). Qed.
Lemma lem2417309 (y : int) (x : int) : (term160 x y) = (term161 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2417310 (x : int) : (term93 x) = (term162 x).
Proof. exact (@lem2417309 term0 (term23 x)). Qed.
Lemma lem2417312 (x : int) (y : int) : (int_le x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2417313 (x : int) : (term164 x) = (term165 x).
Proof. exact (@lem2417312 (term166 x) term0). Qed.
Lemma lem2417315 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417316 (x : int) : (term169 x) = (term170 x).
Proof. exact (@lem2417315 (term23 x) term171). Qed.
Lemma lem2417318 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417319 (x : int) : (term174 x) = (term175 x).
Proof. exact (@lem2417318 (term22 x) term0). Qed.
Lemma lem2417321 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417322 (x : int) : (term178 x) = (term179 x).
Proof. exact (@lem2417321 term0 x). Qed.
Lemma lem2417324 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417325 : term181 = term182.
Proof. exact (@lem2417324 (NUMERAL 0)). Qed.
Lemma lem2417326 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2417327 : term183 = term184.
Proof. exact (MK_COMB (@lem2417326) (@lem2417325)). Qed.
Lemma lem2417328 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2417329 (x : int) : (term179 x) = (term185 x).
Proof. exact (MK_COMB (@lem2417327) (@lem2417328 x)). Qed.
Lemma lem2417330 (x : int) : (term178 x) = (term185 x).
Proof. exact (TRANS (@lem2417322 x) (@lem2417329 x)). Qed.
Lemma lem2417331 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2417332 (x : int) : (term186 x) = (term187 x).
Proof. exact (MK_COMB (@lem2417331) (@lem2417330 x)). Qed.
Lemma lem2417334 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417335 : term181 = term182.
Proof. exact (@lem2417334 (NUMERAL 0)). Qed.
Lemma lem2417336 (x : int) : (term175 x) = (term188 x).
Proof. exact (MK_COMB (@lem2417332 x) (@lem2417335)). Qed.
Lemma lem2417337 (x : int) : (term174 x) = (term188 x).
Proof. exact (TRANS (@lem2417319 x) (@lem2417336 x)). Qed.
Lemma lem2417338 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417339 (x : int) : (term189 x) = (term190 x).
Proof. exact (MK_COMB (@lem2417338) (@lem2417337 x)). Qed.
Lemma lem2417341 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417342 : term191 = term192.
Proof. exact (@lem2417341 term193). Qed.
Lemma lem2417343 (x : int) : (term170 x) = (term194 x).
Proof. exact (MK_COMB (@lem2417339 x) (@lem2417342)). Qed.
Lemma lem2417344 (x : int) : (term169 x) = (term194 x).
Proof. exact (TRANS (@lem2417316 x) (@lem2417343 x)). Qed.
Lemma lem2417345 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2417346 (x : int) : (term195 x) = (term196 x).
Proof. exact (MK_COMB (@lem2417345) (@lem2417344 x)). Qed.
Lemma lem2417348 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417349 : term181 = term182.
Proof. exact (@lem2417348 (NUMERAL 0)). Qed.
Lemma lem2417350 (x : int) : (term165 x) = (term197 x).
Proof. exact (MK_COMB (@lem2417346 x) (@lem2417349)). Qed.
Lemma lem2417351 (x : int) : (term164 x) = (term197 x).
Proof. exact (TRANS (@lem2417313 x) (@lem2417350 x)). Qed.
Lemma lem2417352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417353 (x : int) : (term198 x) = (term199 x).
Proof. exact (MK_COMB (@lem2417352) (@lem2417351 x)). Qed.
Lemma lem2417355 (x : int) (y : int) : (int_le x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2417356 (x : int) : (term200 x) = (term201 x).
Proof. exact (@lem2417355 term202 (term23 x)). Qed.
Lemma lem2417358 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417359 : term203 = term204.
Proof. exact (@lem2417358 term0 term171). Qed.
Lemma lem2417361 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417362 : term181 = term182.
Proof. exact (@lem2417361 (NUMERAL 0)). Qed.
Lemma lem2417363 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417364 : term205 = term206.
Proof. exact (MK_COMB (@lem2417363) (@lem2417362)). Qed.
Lemma lem2417366 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417367 : term191 = term192.
Proof. exact (@lem2417366 term193). Qed.
Lemma lem2417368 : term204 = term207.
Proof. exact (MK_COMB (@lem2417364) (@lem2417367)). Qed.
Lemma lem2417369 : term203 = term207.
Proof. exact (TRANS (@lem2417359) (@lem2417368)). Qed.
Lemma lem2417370 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2417371 : term208 = term209.
Proof. exact (MK_COMB (@lem2417370) (@lem2417369)). Qed.
Lemma lem2417373 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417374 (x : int) : (term174 x) = (term175 x).
Proof. exact (@lem2417373 (term22 x) term0). Qed.
Lemma lem2417376 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417377 (x : int) : (term178 x) = (term179 x).
Proof. exact (@lem2417376 term0 x). Qed.
Lemma lem2417379 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417380 : term181 = term182.
Proof. exact (@lem2417379 (NUMERAL 0)). Qed.
Lemma lem2417381 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2417382 : term183 = term184.
Proof. exact (MK_COMB (@lem2417381) (@lem2417380)). Qed.
Lemma lem2417383 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2417384 (x : int) : (term179 x) = (term185 x).
Proof. exact (MK_COMB (@lem2417382) (@lem2417383 x)). Qed.
Lemma lem2417385 (x : int) : (term178 x) = (term185 x).
Proof. exact (TRANS (@lem2417377 x) (@lem2417384 x)). Qed.
Lemma lem2417386 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2417387 (x : int) : (term186 x) = (term187 x).
Proof. exact (MK_COMB (@lem2417386) (@lem2417385 x)). Qed.
Lemma lem2417389 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417390 : term181 = term182.
Proof. exact (@lem2417389 (NUMERAL 0)). Qed.
Lemma lem2417391 (x : int) : (term175 x) = (term188 x).
Proof. exact (MK_COMB (@lem2417387 x) (@lem2417390)). Qed.
Lemma lem2417392 (x : int) : (term174 x) = (term188 x).
Proof. exact (TRANS (@lem2417374 x) (@lem2417391 x)). Qed.
Lemma lem2417393 (x : int) : (term201 x) = (term210 x).
Proof. exact (MK_COMB (@lem2417371) (@lem2417392 x)). Qed.
Lemma lem2417394 (x : int) : (term200 x) = (term210 x).
Proof. exact (TRANS (@lem2417356 x) (@lem2417393 x)). Qed.
Lemma lem2417395 (x : int) : (term162 x) = (term211 x).
Proof. exact (MK_COMB (@lem2417353 x) (@lem2417394 x)). Qed.
Lemma lem2417396 (x : int) : (term93 x) = (term211 x).
Proof. exact (TRANS (@lem2417310 x) (@lem2417395 x)). Qed.
Lemma lem2417397 : term95 = term212.
Proof. exact (fun_ext (fun x : int => @lem2417396 x)). Qed.
Lemma lem2417398 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417399 : term96 = term213.
Proof. exact (MK_COMB (@lem2417398) (@lem2417397)). Qed.
Lemma lem2417402 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2417403 (y : int) (x : int) (z : int) : ((term30 y x z) = term0) = ((term214 y x z) = term181).
Proof. exact (@lem2417402 (term30 y x z) term0). Qed.
Lemma lem2417407 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417408 (y : int) (x : int) (z : int) : (term214 y x z) = (term215 y x z).
Proof. exact (@lem2417407 (int_add x y) (int_add x z)). Qed.
Lemma lem2417410 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417411 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2417412 (x : int) (y : int) : (term216 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem2417411) (@lem2417410 x y)). Qed.
Lemma lem2417414 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417415 (x : int) (z : int) : (term167 x z) = (term168 x z).
Proof. exact (@lem2417414 x z). Qed.
Lemma lem2417416 (y : int) (x : int) (z : int) : (term215 y x z) = (term218 y x z).
Proof. exact (MK_COMB (@lem2417412 x y) (@lem2417415 x z)). Qed.
Lemma lem2417417 (y : int) (x : int) (z : int) : (term214 y x z) = (term218 y x z).
Proof. exact (TRANS (@lem2417408 y x z) (@lem2417416 y x z)). Qed.
Lemma lem2417418 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2417419 (y : int) (x : int) (z : int) : (term219 y x z) = (term220 y x z).
Proof. exact (MK_COMB (@lem2417418) (@lem2417417 y x z)). Qed.
Lemma lem2417421 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417422 : term181 = term182.
Proof. exact (@lem2417421 (NUMERAL 0)). Qed.
Lemma lem2417423 (y : int) (x : int) (z : int) : ((term214 y x z) = term181) = ((term218 y x z) = term182).
Proof. exact (MK_COMB (@lem2417419 y x z) (@lem2417422)). Qed.
Lemma lem2417425 (y : int) (x : int) (z : int) : ((term30 y x z) = term0) = ((term218 y x z) = term182).
Proof. exact (TRANS (@lem2417403 y x z) (@lem2417423 y x z)). Qed.
Lemma lem2417427 (y : int) (x : int) : (term160 x y) = (term161 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2417428 (y : int) (z : int) : (term221 y z) = (term222 y z).
Proof. exact (@lem2417427 term0 (int_sub y z)). Qed.
Lemma lem2417430 (x : int) (y : int) : (int_le x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2417431 (y : int) (z : int) : (term223 y z) = (term224 y z).
Proof. exact (@lem2417430 (term225 y z) term0). Qed.
Lemma lem2417433 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417434 (y : int) (z : int) : (term226 y z) = (term227 y z).
Proof. exact (@lem2417433 (int_sub y z) term171). Qed.
Lemma lem2417436 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417437 (y : int) (z : int) : (term172 y z) = (term173 y z).
Proof. exact (@lem2417436 y z). Qed.
Lemma lem2417438 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417439 (y : int) (z : int) : (term228 y z) = (term229 y z).
Proof. exact (MK_COMB (@lem2417438) (@lem2417437 y z)). Qed.
Lemma lem2417441 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417442 : term191 = term192.
Proof. exact (@lem2417441 term193). Qed.
Lemma lem2417443 (y : int) (z : int) : (term227 y z) = (term230 y z).
Proof. exact (MK_COMB (@lem2417439 y z) (@lem2417442)). Qed.
Lemma lem2417444 (y : int) (z : int) : (term226 y z) = (term230 y z).
Proof. exact (TRANS (@lem2417434 y z) (@lem2417443 y z)). Qed.
Lemma lem2417445 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2417446 (y : int) (z : int) : (term231 y z) = (term232 y z).
Proof. exact (MK_COMB (@lem2417445) (@lem2417444 y z)). Qed.
Lemma lem2417448 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417449 : term181 = term182.
Proof. exact (@lem2417448 (NUMERAL 0)). Qed.
Lemma lem2417450 (y : int) (z : int) : (term224 y z) = (term233 y z).
Proof. exact (MK_COMB (@lem2417446 y z) (@lem2417449)). Qed.
Lemma lem2417451 (y : int) (z : int) : (term223 y z) = (term233 y z).
Proof. exact (TRANS (@lem2417431 y z) (@lem2417450 y z)). Qed.
Lemma lem2417452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417453 (y : int) (z : int) : (term234 y z) = (term235 y z).
Proof. exact (MK_COMB (@lem2417452) (@lem2417451 y z)). Qed.
Lemma lem2417455 (x : int) (y : int) : (int_le x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2417456 (y : int) (z : int) : (term236 y z) = (term237 y z).
Proof. exact (@lem2417455 term202 (int_sub y z)). Qed.
Lemma lem2417458 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417459 : term203 = term204.
Proof. exact (@lem2417458 term0 term171). Qed.
Lemma lem2417461 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417462 : term181 = term182.
Proof. exact (@lem2417461 (NUMERAL 0)). Qed.
Lemma lem2417463 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417464 : term205 = term206.
Proof. exact (MK_COMB (@lem2417463) (@lem2417462)). Qed.
Lemma lem2417466 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417467 : term191 = term192.
Proof. exact (@lem2417466 term193). Qed.
Lemma lem2417468 : term204 = term207.
Proof. exact (MK_COMB (@lem2417464) (@lem2417467)). Qed.
Lemma lem2417469 : term203 = term207.
Proof. exact (TRANS (@lem2417459) (@lem2417468)). Qed.
Lemma lem2417470 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2417471 : term208 = term209.
Proof. exact (MK_COMB (@lem2417470) (@lem2417469)). Qed.
Lemma lem2417473 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417474 (y : int) (z : int) : (term172 y z) = (term173 y z).
Proof. exact (@lem2417473 y z). Qed.
Lemma lem2417475 (y : int) (z : int) : (term237 y z) = (term238 y z).
Proof. exact (MK_COMB (@lem2417471) (@lem2417474 y z)). Qed.
Lemma lem2417476 (y : int) (z : int) : (term236 y z) = (term238 y z).
Proof. exact (TRANS (@lem2417456 y z) (@lem2417475 y z)). Qed.
Lemma lem2417477 (y : int) (z : int) : (term222 y z) = (term239 y z).
Proof. exact (MK_COMB (@lem2417453 y z) (@lem2417476 y z)). Qed.
Lemma lem2417478 (y : int) (z : int) : (term221 y z) = (term239 y z).
Proof. exact (TRANS (@lem2417428 y z) (@lem2417477 y z)). Qed.
Lemma lem2417479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2417480 (y : int) (x : int) (z : int) : (term240 y x z) = (term241 y x z).
Proof. exact (MK_COMB (@lem2417479) (@lem2417425 y x z)). Qed.
Lemma lem2417481 (x : int) (y : int) (z : int) : (term242 x y z) = (term243 x y z).
Proof. exact (MK_COMB (@lem2417480 y x z) (@lem2417478 y z)). Qed.
Lemma lem2417483 (y : int) (x : int) : (term160 x y) = (term161 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2417484 (y : int) (x : int) (z : int) : (term244 y x z) = (term245 y x z).
Proof. exact (@lem2417483 term0 (term30 y x z)). Qed.
Lemma lem2417486 (x : int) (y : int) : (int_le x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2417487 (y : int) (x : int) (z : int) : (term246 y x z) = (term247 y x z).
Proof. exact (@lem2417486 (term248 y x z) term0). Qed.
Lemma lem2417489 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417490 (y : int) (x : int) (z : int) : (term249 y x z) = (term250 y x z).
Proof. exact (@lem2417489 (term30 y x z) term171). Qed.
Lemma lem2417492 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417493 (y : int) (x : int) (z : int) : (term214 y x z) = (term215 y x z).
Proof. exact (@lem2417492 (int_add x y) (int_add x z)). Qed.
Lemma lem2417495 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417496 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2417497 (x : int) (y : int) : (term216 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem2417496) (@lem2417495 x y)). Qed.
Lemma lem2417499 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417500 (x : int) (z : int) : (term167 x z) = (term168 x z).
Proof. exact (@lem2417499 x z). Qed.
Lemma lem2417501 (y : int) (x : int) (z : int) : (term215 y x z) = (term218 y x z).
Proof. exact (MK_COMB (@lem2417497 x y) (@lem2417500 x z)). Qed.
Lemma lem2417502 (y : int) (x : int) (z : int) : (term214 y x z) = (term218 y x z).
Proof. exact (TRANS (@lem2417493 y x z) (@lem2417501 y x z)). Qed.
Lemma lem2417503 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417504 (y : int) (x : int) (z : int) : (term251 y x z) = (term252 y x z).
Proof. exact (MK_COMB (@lem2417503) (@lem2417502 y x z)). Qed.
Lemma lem2417506 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417507 : term191 = term192.
Proof. exact (@lem2417506 term193). Qed.
Lemma lem2417508 (y : int) (x : int) (z : int) : (term250 y x z) = (term253 y x z).
Proof. exact (MK_COMB (@lem2417504 y x z) (@lem2417507)). Qed.
Lemma lem2417509 (y : int) (x : int) (z : int) : (term249 y x z) = (term253 y x z).
Proof. exact (TRANS (@lem2417490 y x z) (@lem2417508 y x z)). Qed.
Lemma lem2417510 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2417511 (y : int) (x : int) (z : int) : (term254 y x z) = (term255 y x z).
Proof. exact (MK_COMB (@lem2417510) (@lem2417509 y x z)). Qed.
Lemma lem2417513 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417514 : term181 = term182.
Proof. exact (@lem2417513 (NUMERAL 0)). Qed.
Lemma lem2417515 (y : int) (x : int) (z : int) : (term247 y x z) = (term256 y x z).
Proof. exact (MK_COMB (@lem2417511 y x z) (@lem2417514)). Qed.
Lemma lem2417516 (y : int) (x : int) (z : int) : (term246 y x z) = (term256 y x z).
Proof. exact (TRANS (@lem2417487 y x z) (@lem2417515 y x z)). Qed.
Lemma lem2417517 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417518 (y : int) (x : int) (z : int) : (term257 y x z) = (term258 y x z).
Proof. exact (MK_COMB (@lem2417517) (@lem2417516 y x z)). Qed.
Lemma lem2417520 (x : int) (y : int) : (int_le x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2417521 (y : int) (x : int) (z : int) : (term259 y x z) = (term260 y x z).
Proof. exact (@lem2417520 term202 (term30 y x z)). Qed.
Lemma lem2417523 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417524 : term203 = term204.
Proof. exact (@lem2417523 term0 term171). Qed.
Lemma lem2417526 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417527 : term181 = term182.
Proof. exact (@lem2417526 (NUMERAL 0)). Qed.
Lemma lem2417528 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417529 : term205 = term206.
Proof. exact (MK_COMB (@lem2417528) (@lem2417527)). Qed.
Lemma lem2417531 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417532 : term191 = term192.
Proof. exact (@lem2417531 term193). Qed.
Lemma lem2417533 : term204 = term207.
Proof. exact (MK_COMB (@lem2417529) (@lem2417532)). Qed.
Lemma lem2417534 : term203 = term207.
Proof. exact (TRANS (@lem2417524) (@lem2417533)). Qed.
Lemma lem2417535 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2417536 : term208 = term209.
Proof. exact (MK_COMB (@lem2417535) (@lem2417534)). Qed.
Lemma lem2417538 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417539 (y : int) (x : int) (z : int) : (term214 y x z) = (term215 y x z).
Proof. exact (@lem2417538 (int_add x y) (int_add x z)). Qed.
Lemma lem2417541 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417542 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2417543 (x : int) (y : int) : (term216 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem2417542) (@lem2417541 x y)). Qed.
Lemma lem2417545 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417546 (x : int) (z : int) : (term167 x z) = (term168 x z).
Proof. exact (@lem2417545 x z). Qed.
Lemma lem2417547 (y : int) (x : int) (z : int) : (term215 y x z) = (term218 y x z).
Proof. exact (MK_COMB (@lem2417543 x y) (@lem2417546 x z)). Qed.
Lemma lem2417548 (y : int) (x : int) (z : int) : (term214 y x z) = (term218 y x z).
Proof. exact (TRANS (@lem2417539 y x z) (@lem2417547 y x z)). Qed.
Lemma lem2417549 (y : int) (x : int) (z : int) : (term260 y x z) = (term261 y x z).
Proof. exact (MK_COMB (@lem2417536) (@lem2417548 y x z)). Qed.
Lemma lem2417550 (y : int) (x : int) (z : int) : (term259 y x z) = (term261 y x z).
Proof. exact (TRANS (@lem2417521 y x z) (@lem2417549 y x z)). Qed.
Lemma lem2417551 (y : int) (x : int) (z : int) : (term245 y x z) = (term262 y x z).
Proof. exact (MK_COMB (@lem2417518 y x z) (@lem2417550 y x z)). Qed.
Lemma lem2417552 (y : int) (x : int) (z : int) : (term244 y x z) = (term262 y x z).
Proof. exact (TRANS (@lem2417484 y x z) (@lem2417551 y x z)). Qed.
Lemma lem2417555 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2417556 (y : int) (z : int) : ((int_sub y z) = term0) = ((term172 y z) = term181).
Proof. exact (@lem2417555 (int_sub y z) term0). Qed.
Lemma lem2417560 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417561 (y : int) (z : int) : (term172 y z) = (term173 y z).
Proof. exact (@lem2417560 y z). Qed.
Lemma lem2417562 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2417563 (y : int) (z : int) : (term263 y z) = (term264 y z).
Proof. exact (MK_COMB (@lem2417562) (@lem2417561 y z)). Qed.
Lemma lem2417565 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417566 : term181 = term182.
Proof. exact (@lem2417565 (NUMERAL 0)). Qed.
Lemma lem2417567 (y : int) (z : int) : ((term172 y z) = term181) = ((term173 y z) = term182).
Proof. exact (MK_COMB (@lem2417563 y z) (@lem2417566)). Qed.
Lemma lem2417569 (y : int) (z : int) : ((int_sub y z) = term0) = ((term173 y z) = term182).
Proof. exact (TRANS (@lem2417556 y z) (@lem2417567 y z)). Qed.
Lemma lem2417570 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2417571 (y : int) (x : int) (z : int) : (term265 y x z) = (term266 y x z).
Proof. exact (MK_COMB (@lem2417570) (@lem2417552 y x z)). Qed.
Lemma lem2417572 (x : int) (y : int) (z : int) : (term267 x y z) = (term268 x y z).
Proof. exact (MK_COMB (@lem2417571 y x z) (@lem2417569 y z)). Qed.
Lemma lem2417573 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417574 (x : int) (y : int) (z : int) : (term269 x y z) = (term270 x y z).
Proof. exact (MK_COMB (@lem2417573) (@lem2417481 x y z)). Qed.
Lemma lem2417575 (x : int) (y : int) (z : int) : (term98 x y z) = (term271 x y z).
Proof. exact (MK_COMB (@lem2417574 x y z) (@lem2417572 x y z)). Qed.
Lemma lem2417576 (x : int) (y : int) : (term104 x y) = (term272 x y).
Proof. exact (fun_ext (fun z : int => @lem2417575 x y z)). Qed.
Lemma lem2417577 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417578 (x : int) (y : int) : (term105 x y) = (term273 x y).
Proof. exact (MK_COMB (@lem2417577) (@lem2417576 x y)). Qed.
Lemma lem2417579 (x : int) : (term111 x) = (term274 x).
Proof. exact (fun_ext (fun y : int => @lem2417578 x y)). Qed.
Lemma lem2417580 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417581 (x : int) : (term112 x) = (term275 x).
Proof. exact (MK_COMB (@lem2417580) (@lem2417579 x)). Qed.
Lemma lem2417582 : term118 = term276.
Proof. exact (fun_ext (fun x : int => @lem2417581 x)). Qed.
Lemma lem2417583 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417584 : term119 = term277.
Proof. exact (MK_COMB (@lem2417583) (@lem2417582)). Qed.
Lemma lem2417587 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2417588 (w : int) (z : int) (x : int) (y : int) : ((term48 w z x y) = term0) = ((term278 w z x y) = term181).
Proof. exact (@lem2417587 (term48 w z x y) term0). Qed.
Lemma lem2417592 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417593 (w : int) (z : int) (x : int) (y : int) : (term278 w z x y) = (term279 w z x y).
Proof. exact (@lem2417592 (term47 w y x z) (term47 w z x y)). Qed.
Lemma lem2417595 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417596 (w : int) (y : int) (x : int) (z : int) : (term280 w y x z) = (term281 w y x z).
Proof. exact (@lem2417595 (int_mul w y) (int_mul x z)). Qed.
Lemma lem2417598 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417599 (w : int) (y : int) : (term176 w y) = (term177 w y).
Proof. exact (@lem2417598 w y). Qed.
Lemma lem2417600 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417601 (w : int) (y : int) : (term282 w y) = (term283 w y).
Proof. exact (MK_COMB (@lem2417600) (@lem2417599 w y)). Qed.
Lemma lem2417603 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417604 (x : int) (z : int) : (term176 x z) = (term177 x z).
Proof. exact (@lem2417603 x z). Qed.
Lemma lem2417605 (w : int) (y : int) (x : int) (z : int) : (term281 w y x z) = (term284 w y x z).
Proof. exact (MK_COMB (@lem2417601 w y) (@lem2417604 x z)). Qed.
Lemma lem2417606 (w : int) (y : int) (x : int) (z : int) : (term280 w y x z) = (term284 w y x z).
Proof. exact (TRANS (@lem2417596 w y x z) (@lem2417605 w y x z)). Qed.
Lemma lem2417607 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2417608 (w : int) (y : int) (x : int) (z : int) : (term285 w y x z) = (term286 w y x z).
Proof. exact (MK_COMB (@lem2417607) (@lem2417606 w y x z)). Qed.
Lemma lem2417610 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417611 (w : int) (z : int) (x : int) (y : int) : (term280 w z x y) = (term281 w z x y).
Proof. exact (@lem2417610 (int_mul w z) (int_mul x y)). Qed.
Lemma lem2417613 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417614 (w : int) (z : int) : (term176 w z) = (term177 w z).
Proof. exact (@lem2417613 w z). Qed.
Lemma lem2417615 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417616 (w : int) (z : int) : (term282 w z) = (term283 w z).
Proof. exact (MK_COMB (@lem2417615) (@lem2417614 w z)). Qed.
Lemma lem2417618 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417619 (w : int) (z : int) (x : int) (y : int) : (term281 w z x y) = (term284 w z x y).
Proof. exact (MK_COMB (@lem2417616 w z) (@lem2417618 x y)). Qed.
Lemma lem2417620 (w : int) (z : int) (x : int) (y : int) : (term280 w z x y) = (term284 w z x y).
Proof. exact (TRANS (@lem2417611 w z x y) (@lem2417619 w z x y)). Qed.
Lemma lem2417621 (w : int) (z : int) (x : int) (y : int) : (term279 w z x y) = (term287 w z x y).
Proof. exact (MK_COMB (@lem2417608 w y x z) (@lem2417620 w z x y)). Qed.
Lemma lem2417622 (w : int) (z : int) (x : int) (y : int) : (term278 w z x y) = (term287 w z x y).
Proof. exact (TRANS (@lem2417593 w z x y) (@lem2417621 w z x y)). Qed.
Lemma lem2417623 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2417624 (w : int) (z : int) (x : int) (y : int) : (term288 w z x y) = (term289 w z x y).
Proof. exact (MK_COMB (@lem2417623) (@lem2417622 w z x y)). Qed.
Lemma lem2417626 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417627 : term181 = term182.
Proof. exact (@lem2417626 (NUMERAL 0)). Qed.
Lemma lem2417628 (w : int) (z : int) (x : int) (y : int) : ((term278 w z x y) = term181) = ((term287 w z x y) = term182).
Proof. exact (MK_COMB (@lem2417624 w z x y) (@lem2417627)). Qed.
Lemma lem2417630 (w : int) (z : int) (x : int) (y : int) : ((term48 w z x y) = term0) = ((term287 w z x y) = term182).
Proof. exact (TRANS (@lem2417588 w z x y) (@lem2417628 w z x y)). Qed.
Lemma lem2417632 (y : int) (x : int) : (term160 x y) = (term161 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2417633 (w : int) (x : int) (y : int) (z : int) : (term290 w x y z) = (term291 w x y z).
Proof. exact (@lem2417632 term0 (term75 w x y z)). Qed.
Lemma lem2417635 (x : int) (y : int) : (int_le x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2417636 (w : int) (x : int) (y : int) (z : int) : (term292 w x y z) = (term293 w x y z).
Proof. exact (@lem2417635 (term294 w x y z) term0). Qed.
Lemma lem2417638 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417639 (w : int) (x : int) (y : int) (z : int) : (term295 w x y z) = (term296 w x y z).
Proof. exact (@lem2417638 (term75 w x y z) term171). Qed.
Lemma lem2417641 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417642 (w : int) (x : int) (y : int) (z : int) : (term297 w x y z) = (term298 w x y z).
Proof. exact (@lem2417641 (int_sub w x) (int_sub y z)). Qed.
Lemma lem2417644 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417645 (w : int) (x : int) : (term172 w x) = (term173 w x).
Proof. exact (@lem2417644 w x). Qed.
Lemma lem2417646 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2417647 (w : int) (x : int) : (term299 w x) = (term300 w x).
Proof. exact (MK_COMB (@lem2417646) (@lem2417645 w x)). Qed.
Lemma lem2417649 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417650 (y : int) (z : int) : (term172 y z) = (term173 y z).
Proof. exact (@lem2417649 y z). Qed.
Lemma lem2417651 (w : int) (x : int) (y : int) (z : int) : (term298 w x y z) = (term301 w x y z).
Proof. exact (MK_COMB (@lem2417647 w x) (@lem2417650 y z)). Qed.
Lemma lem2417652 (w : int) (x : int) (y : int) (z : int) : (term297 w x y z) = (term301 w x y z).
Proof. exact (TRANS (@lem2417642 w x y z) (@lem2417651 w x y z)). Qed.
Lemma lem2417653 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417654 (w : int) (x : int) (y : int) (z : int) : (term302 w x y z) = (term303 w x y z).
Proof. exact (MK_COMB (@lem2417653) (@lem2417652 w x y z)). Qed.
Lemma lem2417656 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417657 : term191 = term192.
Proof. exact (@lem2417656 term193). Qed.
Lemma lem2417658 (w : int) (x : int) (y : int) (z : int) : (term296 w x y z) = (term304 w x y z).
Proof. exact (MK_COMB (@lem2417654 w x y z) (@lem2417657)). Qed.
Lemma lem2417659 (w : int) (x : int) (y : int) (z : int) : (term295 w x y z) = (term304 w x y z).
Proof. exact (TRANS (@lem2417639 w x y z) (@lem2417658 w x y z)). Qed.
Lemma lem2417660 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2417661 (w : int) (x : int) (y : int) (z : int) : (term305 w x y z) = (term306 w x y z).
Proof. exact (MK_COMB (@lem2417660) (@lem2417659 w x y z)). Qed.
Lemma lem2417663 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417664 : term181 = term182.
Proof. exact (@lem2417663 (NUMERAL 0)). Qed.
Lemma lem2417665 (w : int) (x : int) (y : int) (z : int) : (term293 w x y z) = (term307 w x y z).
Proof. exact (MK_COMB (@lem2417661 w x y z) (@lem2417664)). Qed.
Lemma lem2417666 (w : int) (x : int) (y : int) (z : int) : (term292 w x y z) = (term307 w x y z).
Proof. exact (TRANS (@lem2417636 w x y z) (@lem2417665 w x y z)). Qed.
Lemma lem2417667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417668 (w : int) (x : int) (y : int) (z : int) : (term308 w x y z) = (term309 w x y z).
Proof. exact (MK_COMB (@lem2417667) (@lem2417666 w x y z)). Qed.
Lemma lem2417670 (x : int) (y : int) : (int_le x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2417671 (w : int) (x : int) (y : int) (z : int) : (term310 w x y z) = (term311 w x y z).
Proof. exact (@lem2417670 term202 (term75 w x y z)). Qed.
Lemma lem2417673 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417674 : term203 = term204.
Proof. exact (@lem2417673 term0 term171). Qed.
Lemma lem2417676 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417677 : term181 = term182.
Proof. exact (@lem2417676 (NUMERAL 0)). Qed.
Lemma lem2417678 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417679 : term205 = term206.
Proof. exact (MK_COMB (@lem2417678) (@lem2417677)). Qed.
Lemma lem2417681 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417682 : term191 = term192.
Proof. exact (@lem2417681 term193). Qed.
Lemma lem2417683 : term204 = term207.
Proof. exact (MK_COMB (@lem2417679) (@lem2417682)). Qed.
Lemma lem2417684 : term203 = term207.
Proof. exact (TRANS (@lem2417674) (@lem2417683)). Qed.
Lemma lem2417685 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2417686 : term208 = term209.
Proof. exact (MK_COMB (@lem2417685) (@lem2417684)). Qed.
Lemma lem2417688 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417689 (w : int) (x : int) (y : int) (z : int) : (term297 w x y z) = (term298 w x y z).
Proof. exact (@lem2417688 (int_sub w x) (int_sub y z)). Qed.
Lemma lem2417691 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417692 (w : int) (x : int) : (term172 w x) = (term173 w x).
Proof. exact (@lem2417691 w x). Qed.
Lemma lem2417693 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2417694 (w : int) (x : int) : (term299 w x) = (term300 w x).
Proof. exact (MK_COMB (@lem2417693) (@lem2417692 w x)). Qed.
Lemma lem2417696 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417697 (y : int) (z : int) : (term172 y z) = (term173 y z).
Proof. exact (@lem2417696 y z). Qed.
Lemma lem2417698 (w : int) (x : int) (y : int) (z : int) : (term298 w x y z) = (term301 w x y z).
Proof. exact (MK_COMB (@lem2417694 w x) (@lem2417697 y z)). Qed.
Lemma lem2417699 (w : int) (x : int) (y : int) (z : int) : (term297 w x y z) = (term301 w x y z).
Proof. exact (TRANS (@lem2417689 w x y z) (@lem2417698 w x y z)). Qed.
Lemma lem2417700 (w : int) (x : int) (y : int) (z : int) : (term311 w x y z) = (term312 w x y z).
Proof. exact (MK_COMB (@lem2417686) (@lem2417699 w x y z)). Qed.
Lemma lem2417701 (w : int) (x : int) (y : int) (z : int) : (term310 w x y z) = (term312 w x y z).
Proof. exact (TRANS (@lem2417671 w x y z) (@lem2417700 w x y z)). Qed.
Lemma lem2417702 (w : int) (x : int) (y : int) (z : int) : (term291 w x y z) = (term313 w x y z).
Proof. exact (MK_COMB (@lem2417668 w x y z) (@lem2417701 w x y z)). Qed.
Lemma lem2417703 (w : int) (x : int) (y : int) (z : int) : (term290 w x y z) = (term313 w x y z).
Proof. exact (TRANS (@lem2417633 w x y z) (@lem2417702 w x y z)). Qed.
Lemma lem2417704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2417705 (w : int) (z : int) (x : int) (y : int) : (term314 w z x y) = (term315 w z x y).
Proof. exact (MK_COMB (@lem2417704) (@lem2417630 w z x y)). Qed.
Lemma lem2417706 (w : int) (x : int) (y : int) (z : int) : (term316 w x y z) = (term317 w x y z).
Proof. exact (MK_COMB (@lem2417705 w z x y) (@lem2417703 w x y z)). Qed.
Lemma lem2417708 (y : int) (x : int) : (term160 x y) = (term161 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2417709 (w : int) (z : int) (x : int) (y : int) : (term318 w z x y) = (term319 w z x y).
Proof. exact (@lem2417708 term0 (term48 w z x y)). Qed.
Lemma lem2417711 (x : int) (y : int) : (int_le x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2417712 (w : int) (z : int) (x : int) (y : int) : (term320 w z x y) = (term321 w z x y).
Proof. exact (@lem2417711 (term322 w z x y) term0). Qed.
Lemma lem2417714 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417715 (w : int) (z : int) (x : int) (y : int) : (term323 w z x y) = (term324 w z x y).
Proof. exact (@lem2417714 (term48 w z x y) term171). Qed.
Lemma lem2417717 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417718 (w : int) (z : int) (x : int) (y : int) : (term278 w z x y) = (term279 w z x y).
Proof. exact (@lem2417717 (term47 w y x z) (term47 w z x y)). Qed.
Lemma lem2417720 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417721 (w : int) (y : int) (x : int) (z : int) : (term280 w y x z) = (term281 w y x z).
Proof. exact (@lem2417720 (int_mul w y) (int_mul x z)). Qed.
Lemma lem2417723 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417724 (w : int) (y : int) : (term176 w y) = (term177 w y).
Proof. exact (@lem2417723 w y). Qed.
Lemma lem2417725 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417726 (w : int) (y : int) : (term282 w y) = (term283 w y).
Proof. exact (MK_COMB (@lem2417725) (@lem2417724 w y)). Qed.
Lemma lem2417728 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417729 (x : int) (z : int) : (term176 x z) = (term177 x z).
Proof. exact (@lem2417728 x z). Qed.
Lemma lem2417730 (w : int) (y : int) (x : int) (z : int) : (term281 w y x z) = (term284 w y x z).
Proof. exact (MK_COMB (@lem2417726 w y) (@lem2417729 x z)). Qed.
Lemma lem2417731 (w : int) (y : int) (x : int) (z : int) : (term280 w y x z) = (term284 w y x z).
Proof. exact (TRANS (@lem2417721 w y x z) (@lem2417730 w y x z)). Qed.
Lemma lem2417732 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2417733 (w : int) (y : int) (x : int) (z : int) : (term285 w y x z) = (term286 w y x z).
Proof. exact (MK_COMB (@lem2417732) (@lem2417731 w y x z)). Qed.
Lemma lem2417735 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417736 (w : int) (z : int) (x : int) (y : int) : (term280 w z x y) = (term281 w z x y).
Proof. exact (@lem2417735 (int_mul w z) (int_mul x y)). Qed.
Lemma lem2417738 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417739 (w : int) (z : int) : (term176 w z) = (term177 w z).
Proof. exact (@lem2417738 w z). Qed.
Lemma lem2417740 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417741 (w : int) (z : int) : (term282 w z) = (term283 w z).
Proof. exact (MK_COMB (@lem2417740) (@lem2417739 w z)). Qed.
Lemma lem2417743 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417744 (w : int) (z : int) (x : int) (y : int) : (term281 w z x y) = (term284 w z x y).
Proof. exact (MK_COMB (@lem2417741 w z) (@lem2417743 x y)). Qed.
Lemma lem2417745 (w : int) (z : int) (x : int) (y : int) : (term280 w z x y) = (term284 w z x y).
Proof. exact (TRANS (@lem2417736 w z x y) (@lem2417744 w z x y)). Qed.
Lemma lem2417746 (w : int) (z : int) (x : int) (y : int) : (term279 w z x y) = (term287 w z x y).
Proof. exact (MK_COMB (@lem2417733 w y x z) (@lem2417745 w z x y)). Qed.
Lemma lem2417747 (w : int) (z : int) (x : int) (y : int) : (term278 w z x y) = (term287 w z x y).
Proof. exact (TRANS (@lem2417718 w z x y) (@lem2417746 w z x y)). Qed.
Lemma lem2417748 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417749 (w : int) (z : int) (x : int) (y : int) : (term325 w z x y) = (term326 w z x y).
Proof. exact (MK_COMB (@lem2417748) (@lem2417747 w z x y)). Qed.
Lemma lem2417751 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417752 : term191 = term192.
Proof. exact (@lem2417751 term193). Qed.
Lemma lem2417753 (w : int) (z : int) (x : int) (y : int) : (term324 w z x y) = (term327 w z x y).
Proof. exact (MK_COMB (@lem2417749 w z x y) (@lem2417752)). Qed.
Lemma lem2417754 (w : int) (z : int) (x : int) (y : int) : (term323 w z x y) = (term327 w z x y).
Proof. exact (TRANS (@lem2417715 w z x y) (@lem2417753 w z x y)). Qed.
Lemma lem2417755 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2417756 (w : int) (z : int) (x : int) (y : int) : (term328 w z x y) = (term329 w z x y).
Proof. exact (MK_COMB (@lem2417755) (@lem2417754 w z x y)). Qed.
Lemma lem2417758 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417759 : term181 = term182.
Proof. exact (@lem2417758 (NUMERAL 0)). Qed.
Lemma lem2417760 (w : int) (z : int) (x : int) (y : int) : (term321 w z x y) = (term330 w z x y).
Proof. exact (MK_COMB (@lem2417756 w z x y) (@lem2417759)). Qed.
Lemma lem2417761 (w : int) (z : int) (x : int) (y : int) : (term320 w z x y) = (term330 w z x y).
Proof. exact (TRANS (@lem2417712 w z x y) (@lem2417760 w z x y)). Qed.
Lemma lem2417762 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417763 (w : int) (z : int) (x : int) (y : int) : (term331 w z x y) = (term332 w z x y).
Proof. exact (MK_COMB (@lem2417762) (@lem2417761 w z x y)). Qed.
Lemma lem2417765 (x : int) (y : int) : (int_le x y) = (term163 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2417766 (w : int) (z : int) (x : int) (y : int) : (term333 w z x y) = (term334 w z x y).
Proof. exact (@lem2417765 term202 (term48 w z x y)). Qed.
Lemma lem2417768 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417769 : term203 = term204.
Proof. exact (@lem2417768 term0 term171). Qed.
Lemma lem2417771 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417772 : term181 = term182.
Proof. exact (@lem2417771 (NUMERAL 0)). Qed.
Lemma lem2417773 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417774 : term205 = term206.
Proof. exact (MK_COMB (@lem2417773) (@lem2417772)). Qed.
Lemma lem2417776 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417777 : term191 = term192.
Proof. exact (@lem2417776 term193). Qed.
Lemma lem2417778 : term204 = term207.
Proof. exact (MK_COMB (@lem2417774) (@lem2417777)). Qed.
Lemma lem2417779 : term203 = term207.
Proof. exact (TRANS (@lem2417769) (@lem2417778)). Qed.
Lemma lem2417780 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2417781 : term208 = term209.
Proof. exact (MK_COMB (@lem2417780) (@lem2417779)). Qed.
Lemma lem2417783 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417784 (w : int) (z : int) (x : int) (y : int) : (term278 w z x y) = (term279 w z x y).
Proof. exact (@lem2417783 (term47 w y x z) (term47 w z x y)). Qed.
Lemma lem2417786 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417787 (w : int) (y : int) (x : int) (z : int) : (term280 w y x z) = (term281 w y x z).
Proof. exact (@lem2417786 (int_mul w y) (int_mul x z)). Qed.
Lemma lem2417789 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417790 (w : int) (y : int) : (term176 w y) = (term177 w y).
Proof. exact (@lem2417789 w y). Qed.
Lemma lem2417791 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417792 (w : int) (y : int) : (term282 w y) = (term283 w y).
Proof. exact (MK_COMB (@lem2417791) (@lem2417790 w y)). Qed.
Lemma lem2417794 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417795 (x : int) (z : int) : (term176 x z) = (term177 x z).
Proof. exact (@lem2417794 x z). Qed.
Lemma lem2417796 (w : int) (y : int) (x : int) (z : int) : (term281 w y x z) = (term284 w y x z).
Proof. exact (MK_COMB (@lem2417792 w y) (@lem2417795 x z)). Qed.
Lemma lem2417797 (w : int) (y : int) (x : int) (z : int) : (term280 w y x z) = (term284 w y x z).
Proof. exact (TRANS (@lem2417787 w y x z) (@lem2417796 w y x z)). Qed.
Lemma lem2417798 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2417799 (w : int) (y : int) (x : int) (z : int) : (term285 w y x z) = (term286 w y x z).
Proof. exact (MK_COMB (@lem2417798) (@lem2417797 w y x z)). Qed.
Lemma lem2417801 (x : int) (y : int) : (term167 x y) = (term168 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2417802 (w : int) (z : int) (x : int) (y : int) : (term280 w z x y) = (term281 w z x y).
Proof. exact (@lem2417801 (int_mul w z) (int_mul x y)). Qed.
Lemma lem2417804 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417805 (w : int) (z : int) : (term176 w z) = (term177 w z).
Proof. exact (@lem2417804 w z). Qed.
Lemma lem2417806 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2417807 (w : int) (z : int) : (term282 w z) = (term283 w z).
Proof. exact (MK_COMB (@lem2417806) (@lem2417805 w z)). Qed.
Lemma lem2417809 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417810 (w : int) (z : int) (x : int) (y : int) : (term281 w z x y) = (term284 w z x y).
Proof. exact (MK_COMB (@lem2417807 w z) (@lem2417809 x y)). Qed.
Lemma lem2417811 (w : int) (z : int) (x : int) (y : int) : (term280 w z x y) = (term284 w z x y).
Proof. exact (TRANS (@lem2417802 w z x y) (@lem2417810 w z x y)). Qed.
Lemma lem2417812 (w : int) (z : int) (x : int) (y : int) : (term279 w z x y) = (term287 w z x y).
Proof. exact (MK_COMB (@lem2417799 w y x z) (@lem2417811 w z x y)). Qed.
Lemma lem2417813 (w : int) (z : int) (x : int) (y : int) : (term278 w z x y) = (term287 w z x y).
Proof. exact (TRANS (@lem2417784 w z x y) (@lem2417812 w z x y)). Qed.
Lemma lem2417814 (w : int) (z : int) (x : int) (y : int) : (term334 w z x y) = (term335 w z x y).
Proof. exact (MK_COMB (@lem2417781) (@lem2417813 w z x y)). Qed.
Lemma lem2417815 (w : int) (z : int) (x : int) (y : int) : (term333 w z x y) = (term335 w z x y).
Proof. exact (TRANS (@lem2417766 w z x y) (@lem2417814 w z x y)). Qed.
Lemma lem2417816 (w : int) (z : int) (x : int) (y : int) : (term319 w z x y) = (term336 w z x y).
Proof. exact (MK_COMB (@lem2417763 w z x y) (@lem2417815 w z x y)). Qed.
Lemma lem2417817 (w : int) (z : int) (x : int) (y : int) : (term318 w z x y) = (term336 w z x y).
Proof. exact (TRANS (@lem2417709 w z x y) (@lem2417816 w z x y)). Qed.
Lemma lem2417820 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2417821 (w : int) (x : int) (y : int) (z : int) : ((term75 w x y z) = term0) = ((term297 w x y z) = term181).
Proof. exact (@lem2417820 (term75 w x y z) term0). Qed.
Lemma lem2417825 (x : int) (y : int) : (term176 x y) = (term177 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2417826 (w : int) (x : int) (y : int) (z : int) : (term297 w x y z) = (term298 w x y z).
Proof. exact (@lem2417825 (int_sub w x) (int_sub y z)). Qed.
Lemma lem2417828 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417829 (w : int) (x : int) : (term172 w x) = (term173 w x).
Proof. exact (@lem2417828 w x). Qed.
Lemma lem2417830 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2417831 (w : int) (x : int) : (term299 w x) = (term300 w x).
Proof. exact (MK_COMB (@lem2417830) (@lem2417829 w x)). Qed.
Lemma lem2417833 (x : int) (y : int) : (term172 x y) = (term173 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2417834 (y : int) (z : int) : (term172 y z) = (term173 y z).
Proof. exact (@lem2417833 y z). Qed.
Lemma lem2417835 (w : int) (x : int) (y : int) (z : int) : (term298 w x y z) = (term301 w x y z).
Proof. exact (MK_COMB (@lem2417831 w x) (@lem2417834 y z)). Qed.
Lemma lem2417836 (w : int) (x : int) (y : int) (z : int) : (term297 w x y z) = (term301 w x y z).
Proof. exact (TRANS (@lem2417826 w x y z) (@lem2417835 w x y z)). Qed.
Lemma lem2417837 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2417838 (w : int) (x : int) (y : int) (z : int) : (term337 w x y z) = (term338 w x y z).
Proof. exact (MK_COMB (@lem2417837) (@lem2417836 w x y z)). Qed.
Lemma lem2417840 (n : nat) : (term180 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2417841 : term181 = term182.
Proof. exact (@lem2417840 (NUMERAL 0)). Qed.
Lemma lem2417842 (w : int) (x : int) (y : int) (z : int) : ((term297 w x y z) = term181) = ((term301 w x y z) = term182).
Proof. exact (MK_COMB (@lem2417838 w x y z) (@lem2417841)). Qed.
Lemma lem2417844 (w : int) (x : int) (y : int) (z : int) : ((term75 w x y z) = term0) = ((term301 w x y z) = term182).
Proof. exact (TRANS (@lem2417821 w x y z) (@lem2417842 w x y z)). Qed.
Lemma lem2417845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2417846 (w : int) (z : int) (x : int) (y : int) : (term339 w z x y) = (term340 w z x y).
Proof. exact (MK_COMB (@lem2417845) (@lem2417817 w z x y)). Qed.
Lemma lem2417847 (w : int) (x : int) (y : int) (z : int) : (term341 w x y z) = (term342 w x y z).
Proof. exact (MK_COMB (@lem2417846 w z x y) (@lem2417844 w x y z)). Qed.
Lemma lem2417848 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417849 (w : int) (x : int) (y : int) (z : int) : (term343 w x y z) = (term344 w x y z).
Proof. exact (MK_COMB (@lem2417848) (@lem2417706 w x y z)). Qed.
Lemma lem2417850 (w : int) (x : int) (y : int) (z : int) : (term121 w x y z) = (term345 w x y z).
Proof. exact (MK_COMB (@lem2417849 w x y z) (@lem2417847 w x y z)). Qed.
Lemma lem2417851 (w : int) (x : int) (y : int) : (term127 w x y) = (term346 w x y).
Proof. exact (fun_ext (fun z : int => @lem2417850 w x y z)). Qed.
Lemma lem2417852 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417853 (w : int) (x : int) (y : int) : (term128 w x y) = (term347 w x y).
Proof. exact (MK_COMB (@lem2417852) (@lem2417851 w x y)). Qed.
Lemma lem2417854 (w : int) (x : int) : (term134 w x) = (term348 w x).
Proof. exact (fun_ext (fun y : int => @lem2417853 w x y)). Qed.
Lemma lem2417855 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417856 (w : int) (x : int) : (term135 w x) = (term349 w x).
Proof. exact (MK_COMB (@lem2417855) (@lem2417854 w x)). Qed.
Lemma lem2417857 (w : int) : (term141 w) = (term350 w).
Proof. exact (fun_ext (fun x : int => @lem2417856 w x)). Qed.
Lemma lem2417858 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417859 (w : int) : (term142 w) = (term351 w).
Proof. exact (MK_COMB (@lem2417858) (@lem2417857 w)). Qed.
Lemma lem2417860 : term148 = term352.
Proof. exact (fun_ext (fun w : int => @lem2417859 w)). Qed.
Lemma lem2417861 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417862 : term149 = term353.
Proof. exact (MK_COMB (@lem2417861) (@lem2417860)). Qed.
Lemma lem2417863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417864 : term151 = term354.
Proof. exact (MK_COMB (@lem2417863) (@lem2417584)). Qed.
Lemma lem2417865 : term153 = term355.
Proof. exact (MK_COMB (@lem2417864) (@lem2417862)). Qed.
Lemma lem2417866 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417867 : term156 = term356.
Proof. exact (MK_COMB (@lem2417866) (@lem2417399)). Qed.
Lemma lem2417868 : term158 = term357.
Proof. exact (MK_COMB (@lem2417867) (@lem2417865)). Qed.
Lemma lem2417869 : term159 = term357.
Proof. exact (TRANS (@lem2417307) (@lem2417868)). Qed.
Lemma lem2417873 (t : Prop) : (term358 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2417874 : term359 = term357.
Proof. exact (@lem2417873 term357). Qed.
Lemma lem2417878 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term360 A P Q) = (term361 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2417879 (P : int -> Prop) (Q : int -> Prop) : (term362 P Q) = (term363 P Q).
Proof. exact (@lem2417878 int P Q). Qed.
Lemma lem2417880 : term364 = term365.
Proof. exact (@lem2417879 term366 term367). Qed.
Lemma lem2417881 (x : int) : (term368 x) = (term197 x).
Proof. exact (eq_refl (term368 x)). Qed.
Lemma lem2417882 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417883 (x : int) : (term369 x) = (term199 x).
Proof. exact (MK_COMB (@lem2417882) (@lem2417881 x)). Qed.
Lemma lem2417884 (x : int) : (term370 x) = (term210 x).
Proof. exact (eq_refl (term370 x)). Qed.
Lemma lem2417885 (x : int) : (term371 x) = (term211 x).
Proof. exact (MK_COMB (@lem2417883 x) (@lem2417884 x)). Qed.
Lemma lem2417886 : term372 = term212.
Proof. exact (fun_ext (fun x : int => @lem2417885 x)). Qed.
Lemma lem2417887 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417888 : term364 = term213.
Proof. exact (MK_COMB (@lem2417887) (@lem2417886)). Qed.
Lemma lem2417889 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2417890 : term373 = term374.
Proof. exact (MK_COMB (@lem2417889) (@lem2417888)). Qed.
Lemma lem2417891 (x : int) : (term368 x) = (term197 x).
Proof. exact (eq_refl (term368 x)). Qed.
Lemma lem2417892 : term375 = term366.
Proof. exact (fun_ext (fun x : int => @lem2417891 x)). Qed.
Lemma lem2417893 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417894 : term376 = term377.
Proof. exact (MK_COMB (@lem2417893) (@lem2417892)). Qed.
Lemma lem2417895 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417896 : term378 = term379.
Proof. exact (MK_COMB (@lem2417895) (@lem2417894)). Qed.
Lemma lem2417897 (x : int) : (term370 x) = (term210 x).
Proof. exact (eq_refl (term370 x)). Qed.
Lemma lem2417898 : term380 = term367.
Proof. exact (fun_ext (fun x : int => @lem2417897 x)). Qed.
Lemma lem2417899 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417900 : term381 = term382.
Proof. exact (MK_COMB (@lem2417899) (@lem2417898)). Qed.
Lemma lem2417901 : term365 = term383.
Proof. exact (MK_COMB (@lem2417896) (@lem2417900)). Qed.
Lemma lem2417902 : (term364 = term365) = (term213 = term383).
Proof. exact (MK_COMB (@lem2417890) (@lem2417901)). Qed.
Lemma lem2417903 : term213 = term383.
Proof. exact (EQ_MP (@lem2417902) (@lem2417880)). Qed.
Lemma lem2417914 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417915 : term356 = term384.
Proof. exact (MK_COMB (@lem2417914) (@lem2417903)). Qed.
Lemma lem2417927 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term360 A P Q) = (term361 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2417928 (P : int -> Prop) (Q : int -> Prop) : (term362 P Q) = (term363 P Q).
Proof. exact (@lem2417927 int P Q). Qed.
Lemma lem2417929 (x : int) (y : int) : (term385 x y) = (term386 x y).
Proof. exact (@lem2417928 (term387 x y) (term388 x y)). Qed.
Lemma lem2417930 (x : int) (y : int) (z : int) : (term389 x y z) = (term243 x y z).
Proof. exact (eq_refl (term389 x y z)). Qed.
Lemma lem2417931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417932 (x : int) (y : int) (z : int) : (term390 x y z) = (term270 x y z).
Proof. exact (MK_COMB (@lem2417931) (@lem2417930 x y z)). Qed.
Lemma lem2417933 (x : int) (y : int) (z : int) : (term391 x y z) = (term268 x y z).
Proof. exact (eq_refl (term391 x y z)). Qed.
Lemma lem2417934 (x : int) (y : int) (z : int) : (term392 x y z) = (term271 x y z).
Proof. exact (MK_COMB (@lem2417932 x y z) (@lem2417933 x y z)). Qed.
Lemma lem2417935 (x : int) (y : int) : (term393 x y) = (term272 x y).
Proof. exact (fun_ext (fun z : int => @lem2417934 x y z)). Qed.
Lemma lem2417936 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417937 (x : int) (y : int) : (term385 x y) = (term273 x y).
Proof. exact (MK_COMB (@lem2417936) (@lem2417935 x y)). Qed.
Lemma lem2417938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2417939 (x : int) (y : int) : (term394 x y) = (term395 x y).
Proof. exact (MK_COMB (@lem2417938) (@lem2417937 x y)). Qed.
Lemma lem2417940 (x : int) (y : int) (z : int) : (term389 x y z) = (term243 x y z).
Proof. exact (eq_refl (term389 x y z)). Qed.
Lemma lem2417941 (x : int) (y : int) : (term396 x y) = (term387 x y).
Proof. exact (fun_ext (fun z : int => @lem2417940 x y z)). Qed.
Lemma lem2417942 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417943 (x : int) (y : int) : (term397 x y) = (term398 x y).
Proof. exact (MK_COMB (@lem2417942) (@lem2417941 x y)). Qed.
Lemma lem2417944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2417945 (x : int) (y : int) : (term399 x y) = (term400 x y).
Proof. exact (MK_COMB (@lem2417944) (@lem2417943 x y)). Qed.
Lemma lem2417946 (x : int) (y : int) (z : int) : (term391 x y z) = (term268 x y z).
Proof. exact (eq_refl (term391 x y z)). Qed.
Lemma lem2417947 (x : int) (y : int) : (term401 x y) = (term388 x y).
Proof. exact (fun_ext (fun z : int => @lem2417946 x y z)). Qed.
Lemma lem2417948 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2417949 (x : int) (y : int) : (term402 x y) = (term403 x y).
Proof. exact (MK_COMB (@lem2417948) (@lem2417947 x y)). Qed.
Lemma lem2417950 (x : int) (y : int) : (term386 x y) = (term404 x y).
Proof. exact (MK_COMB (@lem2417945 x y) (@lem2417949 x y)). Qed.
Lemma lem2417951 (x : int) (y : int) : ((term385 x y) = (term386 x y)) = ((term273 x y) = (term404 x y)).
Proof. exact (MK_COMB (@lem2417939 x y) (@lem2417950 x y)). Qed.
Lemma lem2417952 (x : int) (y : int) : (term273 x y) = (term404 x y).
Proof. exact (EQ_MP (@lem2417951 x y) (@lem2417929 x y)). Qed.
Lemma lem2418059 (x : int) : (term274 x) = (term405 x).
Proof. exact (fun_ext (fun y : int => @lem2417952 x y)). Qed.
Lemma lem2418060 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418061 (x : int) : (term275 x) = (term406 x).
Proof. exact (MK_COMB (@lem2418060) (@lem2418059 x)). Qed.
Lemma lem2418063 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term360 A P Q) = (term361 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2418064 (P : int -> Prop) (Q : int -> Prop) : (term362 P Q) = (term363 P Q).
Proof. exact (@lem2418063 int P Q). Qed.
Lemma lem2418065 (x : int) : (term407 x) = (term408 x).
Proof. exact (@lem2418064 (term409 x) (term410 x)). Qed.
Lemma lem2418066 (x : int) (y : int) : (term411 x y) = (term398 x y).
Proof. exact (eq_refl (term411 x y)). Qed.
Lemma lem2418067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418068 (x : int) (y : int) : (term412 x y) = (term400 x y).
Proof. exact (MK_COMB (@lem2418067) (@lem2418066 x y)). Qed.
Lemma lem2418069 (x : int) (y : int) : (term413 x y) = (term403 x y).
Proof. exact (eq_refl (term413 x y)). Qed.
Lemma lem2418070 (x : int) (y : int) : (term414 x y) = (term404 x y).
Proof. exact (MK_COMB (@lem2418068 x y) (@lem2418069 x y)). Qed.
Lemma lem2418071 (x : int) : (term415 x) = (term405 x).
Proof. exact (fun_ext (fun y : int => @lem2418070 x y)). Qed.
Lemma lem2418072 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418073 (x : int) : (term407 x) = (term406 x).
Proof. exact (MK_COMB (@lem2418072) (@lem2418071 x)). Qed.
Lemma lem2418074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2418075 (x : int) : (term416 x) = (term417 x).
Proof. exact (MK_COMB (@lem2418074) (@lem2418073 x)). Qed.
Lemma lem2418076 (x : int) (y : int) : (term411 x y) = (term398 x y).
Proof. exact (eq_refl (term411 x y)). Qed.
Lemma lem2418077 (x : int) : (term418 x) = (term409 x).
Proof. exact (fun_ext (fun y : int => @lem2418076 x y)). Qed.
Lemma lem2418078 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418079 (x : int) : (term419 x) = (term420 x).
Proof. exact (MK_COMB (@lem2418078) (@lem2418077 x)). Qed.
Lemma lem2418080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418081 (x : int) : (term421 x) = (term422 x).
Proof. exact (MK_COMB (@lem2418080) (@lem2418079 x)). Qed.
Lemma lem2418082 (x : int) (y : int) : (term413 x y) = (term403 x y).
Proof. exact (eq_refl (term413 x y)). Qed.
Lemma lem2418083 (x : int) : (term423 x) = (term410 x).
Proof. exact (fun_ext (fun y : int => @lem2418082 x y)). Qed.
Lemma lem2418084 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418085 (x : int) : (term424 x) = (term425 x).
Proof. exact (MK_COMB (@lem2418084) (@lem2418083 x)). Qed.
Lemma lem2418086 (x : int) : (term408 x) = (term426 x).
Proof. exact (MK_COMB (@lem2418081 x) (@lem2418085 x)). Qed.
Lemma lem2418087 (x : int) : ((term407 x) = (term408 x)) = ((term406 x) = (term426 x)).
Proof. exact (MK_COMB (@lem2418075 x) (@lem2418086 x)). Qed.
Lemma lem2418088 (x : int) : (term406 x) = (term426 x).
Proof. exact (EQ_MP (@lem2418087 x) (@lem2418065 x)). Qed.
Lemma lem2418203 (x : int) : (term275 x) = (term426 x).
Proof. exact (TRANS (@lem2418061 x) (@lem2418088 x)). Qed.
Lemma lem2418204 : term276 = term427.
Proof. exact (fun_ext (fun x : int => @lem2418203 x)). Qed.
Lemma lem2418205 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418206 : term277 = term428.
Proof. exact (MK_COMB (@lem2418205) (@lem2418204)). Qed.
Lemma lem2418208 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term360 A P Q) = (term361 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2418209 (P : int -> Prop) (Q : int -> Prop) : (term362 P Q) = (term363 P Q).
Proof. exact (@lem2418208 int P Q). Qed.
Lemma lem2418210 : term429 = term430.
Proof. exact (@lem2418209 term431 term432). Qed.
Lemma lem2418211 (x : int) : (term433 x) = (term420 x).
Proof. exact (eq_refl (term433 x)). Qed.
Lemma lem2418212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418213 (x : int) : (term434 x) = (term422 x).
Proof. exact (MK_COMB (@lem2418212) (@lem2418211 x)). Qed.
Lemma lem2418214 (x : int) : (term435 x) = (term425 x).
Proof. exact (eq_refl (term435 x)). Qed.
Lemma lem2418215 (x : int) : (term436 x) = (term426 x).
Proof. exact (MK_COMB (@lem2418213 x) (@lem2418214 x)). Qed.
Lemma lem2418216 : term437 = term427.
Proof. exact (fun_ext (fun x : int => @lem2418215 x)). Qed.
Lemma lem2418217 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418218 : term429 = term428.
Proof. exact (MK_COMB (@lem2418217) (@lem2418216)). Qed.
Lemma lem2418219 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2418220 : term438 = term439.
Proof. exact (MK_COMB (@lem2418219) (@lem2418218)). Qed.
Lemma lem2418221 (x : int) : (term433 x) = (term420 x).
Proof. exact (eq_refl (term433 x)). Qed.
Lemma lem2418222 : term440 = term431.
Proof. exact (fun_ext (fun x : int => @lem2418221 x)). Qed.
Lemma lem2418223 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418224 : term441 = term442.
Proof. exact (MK_COMB (@lem2418223) (@lem2418222)). Qed.
Lemma lem2418225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418226 : term443 = term444.
Proof. exact (MK_COMB (@lem2418225) (@lem2418224)). Qed.
Lemma lem2418227 (x : int) : (term435 x) = (term425 x).
Proof. exact (eq_refl (term435 x)). Qed.
Lemma lem2418228 : term445 = term432.
Proof. exact (fun_ext (fun x : int => @lem2418227 x)). Qed.
Lemma lem2418229 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418230 : term446 = term447.
Proof. exact (MK_COMB (@lem2418229) (@lem2418228)). Qed.
Lemma lem2418231 : term430 = term448.
Proof. exact (MK_COMB (@lem2418226) (@lem2418230)). Qed.
Lemma lem2418232 : (term429 = term430) = (term428 = term448).
Proof. exact (MK_COMB (@lem2418220) (@lem2418231)). Qed.
Lemma lem2418233 : term428 = term448.
Proof. exact (EQ_MP (@lem2418232) (@lem2418210)). Qed.
Lemma lem2418356 : term277 = term448.
Proof. exact (TRANS (@lem2418206) (@lem2418233)). Qed.
Lemma lem2418357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418358 : term354 = term449.
Proof. exact (MK_COMB (@lem2418357) (@lem2418356)). Qed.
Lemma lem2418372 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term360 A P Q) = (term361 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2418373 (P : int -> Prop) (Q : int -> Prop) : (term362 P Q) = (term363 P Q).
Proof. exact (@lem2418372 int P Q). Qed.
Lemma lem2418374 (w : int) (x : int) (y : int) : (term450 w x y) = (term451 w x y).
Proof. exact (@lem2418373 (term452 w x y) (term453 w x y)). Qed.
Lemma lem2418375 (w : int) (x : int) (y : int) (z : int) : (term454 w x y z) = (term317 w x y z).
Proof. exact (eq_refl (term454 w x y z)). Qed.
Lemma lem2418376 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418377 (w : int) (x : int) (y : int) (z : int) : (term455 w x y z) = (term344 w x y z).
Proof. exact (MK_COMB (@lem2418376) (@lem2418375 w x y z)). Qed.
Lemma lem2418378 (w : int) (x : int) (y : int) (z : int) : (term456 w x y z) = (term342 w x y z).
Proof. exact (eq_refl (term456 w x y z)). Qed.
Lemma lem2418379 (w : int) (x : int) (y : int) (z : int) : (term457 w x y z) = (term345 w x y z).
Proof. exact (MK_COMB (@lem2418377 w x y z) (@lem2418378 w x y z)). Qed.
Lemma lem2418380 (w : int) (x : int) (y : int) : (term458 w x y) = (term346 w x y).
Proof. exact (fun_ext (fun z : int => @lem2418379 w x y z)). Qed.
Lemma lem2418381 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418382 (w : int) (x : int) (y : int) : (term450 w x y) = (term347 w x y).
Proof. exact (MK_COMB (@lem2418381) (@lem2418380 w x y)). Qed.
Lemma lem2418383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2418384 (w : int) (x : int) (y : int) : (term459 w x y) = (term460 w x y).
Proof. exact (MK_COMB (@lem2418383) (@lem2418382 w x y)). Qed.
Lemma lem2418385 (w : int) (x : int) (y : int) (z : int) : (term454 w x y z) = (term317 w x y z).
Proof. exact (eq_refl (term454 w x y z)). Qed.
Lemma lem2418386 (w : int) (x : int) (y : int) : (term461 w x y) = (term452 w x y).
Proof. exact (fun_ext (fun z : int => @lem2418385 w x y z)). Qed.
Lemma lem2418387 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418388 (w : int) (x : int) (y : int) : (term462 w x y) = (term463 w x y).
Proof. exact (MK_COMB (@lem2418387) (@lem2418386 w x y)). Qed.
Lemma lem2418389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418390 (w : int) (x : int) (y : int) : (term464 w x y) = (term465 w x y).
Proof. exact (MK_COMB (@lem2418389) (@lem2418388 w x y)). Qed.
Lemma lem2418391 (w : int) (x : int) (y : int) (z : int) : (term456 w x y z) = (term342 w x y z).
Proof. exact (eq_refl (term456 w x y z)). Qed.
Lemma lem2418392 (w : int) (x : int) (y : int) : (term466 w x y) = (term453 w x y).
Proof. exact (fun_ext (fun z : int => @lem2418391 w x y z)). Qed.
Lemma lem2418393 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418394 (w : int) (x : int) (y : int) : (term467 w x y) = (term468 w x y).
Proof. exact (MK_COMB (@lem2418393) (@lem2418392 w x y)). Qed.
Lemma lem2418395 (w : int) (x : int) (y : int) : (term451 w x y) = (term469 w x y).
Proof. exact (MK_COMB (@lem2418390 w x y) (@lem2418394 w x y)). Qed.
Lemma lem2418396 (w : int) (x : int) (y : int) : ((term450 w x y) = (term451 w x y)) = ((term347 w x y) = (term469 w x y)).
Proof. exact (MK_COMB (@lem2418384 w x y) (@lem2418395 w x y)). Qed.
Lemma lem2418397 (w : int) (x : int) (y : int) : (term347 w x y) = (term469 w x y).
Proof. exact (EQ_MP (@lem2418396 w x y) (@lem2418374 w x y)). Qed.
Lemma lem2418504 (w : int) (x : int) : (term348 w x) = (term470 w x).
Proof. exact (fun_ext (fun y : int => @lem2418397 w x y)). Qed.
Lemma lem2418505 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418506 (w : int) (x : int) : (term349 w x) = (term471 w x).
Proof. exact (MK_COMB (@lem2418505) (@lem2418504 w x)). Qed.
Lemma lem2418508 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term360 A P Q) = (term361 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2418509 (P : int -> Prop) (Q : int -> Prop) : (term362 P Q) = (term363 P Q).
Proof. exact (@lem2418508 int P Q). Qed.
Lemma lem2418510 (w : int) (x : int) : (term472 w x) = (term473 w x).
Proof. exact (@lem2418509 (term474 w x) (term475 w x)). Qed.
Lemma lem2418511 (w : int) (x : int) (y : int) : (term476 w x y) = (term463 w x y).
Proof. exact (eq_refl (term476 w x y)). Qed.
Lemma lem2418512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418513 (w : int) (x : int) (y : int) : (term477 w x y) = (term465 w x y).
Proof. exact (MK_COMB (@lem2418512) (@lem2418511 w x y)). Qed.
Lemma lem2418514 (w : int) (x : int) (y : int) : (term478 w x y) = (term468 w x y).
Proof. exact (eq_refl (term478 w x y)). Qed.
Lemma lem2418515 (w : int) (x : int) (y : int) : (term479 w x y) = (term469 w x y).
Proof. exact (MK_COMB (@lem2418513 w x y) (@lem2418514 w x y)). Qed.
Lemma lem2418516 (w : int) (x : int) : (term480 w x) = (term470 w x).
Proof. exact (fun_ext (fun y : int => @lem2418515 w x y)). Qed.
Lemma lem2418517 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418518 (w : int) (x : int) : (term472 w x) = (term471 w x).
Proof. exact (MK_COMB (@lem2418517) (@lem2418516 w x)). Qed.
Lemma lem2418519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2418520 (w : int) (x : int) : (term481 w x) = (term482 w x).
Proof. exact (MK_COMB (@lem2418519) (@lem2418518 w x)). Qed.
Lemma lem2418521 (w : int) (x : int) (y : int) : (term476 w x y) = (term463 w x y).
Proof. exact (eq_refl (term476 w x y)). Qed.
Lemma lem2418522 (w : int) (x : int) : (term483 w x) = (term474 w x).
Proof. exact (fun_ext (fun y : int => @lem2418521 w x y)). Qed.
Lemma lem2418523 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418524 (w : int) (x : int) : (term484 w x) = (term485 w x).
Proof. exact (MK_COMB (@lem2418523) (@lem2418522 w x)). Qed.
Lemma lem2418525 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418526 (w : int) (x : int) : (term486 w x) = (term487 w x).
Proof. exact (MK_COMB (@lem2418525) (@lem2418524 w x)). Qed.
Lemma lem2418527 (w : int) (x : int) (y : int) : (term478 w x y) = (term468 w x y).
Proof. exact (eq_refl (term478 w x y)). Qed.
Lemma lem2418528 (w : int) (x : int) : (term488 w x) = (term475 w x).
Proof. exact (fun_ext (fun y : int => @lem2418527 w x y)). Qed.
Lemma lem2418529 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418530 (w : int) (x : int) : (term489 w x) = (term490 w x).
Proof. exact (MK_COMB (@lem2418529) (@lem2418528 w x)). Qed.
Lemma lem2418531 (w : int) (x : int) : (term473 w x) = (term491 w x).
Proof. exact (MK_COMB (@lem2418526 w x) (@lem2418530 w x)). Qed.
Lemma lem2418532 (w : int) (x : int) : ((term472 w x) = (term473 w x)) = ((term471 w x) = (term491 w x)).
Proof. exact (MK_COMB (@lem2418520 w x) (@lem2418531 w x)). Qed.
Lemma lem2418533 (w : int) (x : int) : (term471 w x) = (term491 w x).
Proof. exact (EQ_MP (@lem2418532 w x) (@lem2418510 w x)). Qed.
Lemma lem2418648 (w : int) (x : int) : (term349 w x) = (term491 w x).
Proof. exact (TRANS (@lem2418506 w x) (@lem2418533 w x)). Qed.
Lemma lem2418649 (w : int) : (term350 w) = (term492 w).
Proof. exact (fun_ext (fun x : int => @lem2418648 w x)). Qed.
Lemma lem2418650 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418651 (w : int) : (term351 w) = (term493 w).
Proof. exact (MK_COMB (@lem2418650) (@lem2418649 w)). Qed.
Lemma lem2418653 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term360 A P Q) = (term361 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2418654 (P : int -> Prop) (Q : int -> Prop) : (term362 P Q) = (term363 P Q).
Proof. exact (@lem2418653 int P Q). Qed.
Lemma lem2418655 (w : int) : (term494 w) = (term495 w).
Proof. exact (@lem2418654 (term496 w) (term497 w)). Qed.
Lemma lem2418656 (w : int) (x : int) : (term498 w x) = (term485 w x).
Proof. exact (eq_refl (term498 w x)). Qed.
Lemma lem2418657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418658 (w : int) (x : int) : (term499 w x) = (term487 w x).
Proof. exact (MK_COMB (@lem2418657) (@lem2418656 w x)). Qed.
Lemma lem2418659 (w : int) (x : int) : (term500 w x) = (term490 w x).
Proof. exact (eq_refl (term500 w x)). Qed.
Lemma lem2418660 (w : int) (x : int) : (term501 w x) = (term491 w x).
Proof. exact (MK_COMB (@lem2418658 w x) (@lem2418659 w x)). Qed.
Lemma lem2418661 (w : int) : (term502 w) = (term492 w).
Proof. exact (fun_ext (fun x : int => @lem2418660 w x)). Qed.
Lemma lem2418662 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418663 (w : int) : (term494 w) = (term493 w).
Proof. exact (MK_COMB (@lem2418662) (@lem2418661 w)). Qed.
Lemma lem2418664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2418665 (w : int) : (term503 w) = (term504 w).
Proof. exact (MK_COMB (@lem2418664) (@lem2418663 w)). Qed.
Lemma lem2418666 (w : int) (x : int) : (term498 w x) = (term485 w x).
Proof. exact (eq_refl (term498 w x)). Qed.
Lemma lem2418667 (w : int) : (term505 w) = (term496 w).
Proof. exact (fun_ext (fun x : int => @lem2418666 w x)). Qed.
Lemma lem2418668 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418669 (w : int) : (term506 w) = (term507 w).
Proof. exact (MK_COMB (@lem2418668) (@lem2418667 w)). Qed.
Lemma lem2418670 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418671 (w : int) : (term508 w) = (term509 w).
Proof. exact (MK_COMB (@lem2418670) (@lem2418669 w)). Qed.
Lemma lem2418672 (w : int) (x : int) : (term500 w x) = (term490 w x).
Proof. exact (eq_refl (term500 w x)). Qed.
Lemma lem2418673 (w : int) : (term510 w) = (term497 w).
Proof. exact (fun_ext (fun x : int => @lem2418672 w x)). Qed.
Lemma lem2418674 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418675 (w : int) : (term511 w) = (term512 w).
Proof. exact (MK_COMB (@lem2418674) (@lem2418673 w)). Qed.
Lemma lem2418676 (w : int) : (term495 w) = (term513 w).
Proof. exact (MK_COMB (@lem2418671 w) (@lem2418675 w)). Qed.
Lemma lem2418677 (w : int) : ((term494 w) = (term495 w)) = ((term493 w) = (term513 w)).
Proof. exact (MK_COMB (@lem2418665 w) (@lem2418676 w)). Qed.
Lemma lem2418678 (w : int) : (term493 w) = (term513 w).
Proof. exact (EQ_MP (@lem2418677 w) (@lem2418655 w)). Qed.
Lemma lem2418801 (w : int) : (term351 w) = (term513 w).
Proof. exact (TRANS (@lem2418651 w) (@lem2418678 w)). Qed.
Lemma lem2418802 : term352 = term514.
Proof. exact (fun_ext (fun w : int => @lem2418801 w)). Qed.
Lemma lem2418803 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418804 : term353 = term515.
Proof. exact (MK_COMB (@lem2418803) (@lem2418802)). Qed.
Lemma lem2418806 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term360 A P Q) = (term361 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2418807 (P : int -> Prop) (Q : int -> Prop) : (term362 P Q) = (term363 P Q).
Proof. exact (@lem2418806 int P Q). Qed.
Lemma lem2418808 : term516 = term517.
Proof. exact (@lem2418807 term518 term519). Qed.
Lemma lem2418809 (w : int) : (term520 w) = (term507 w).
Proof. exact (eq_refl (term520 w)). Qed.
Lemma lem2418810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418811 (w : int) : (term521 w) = (term509 w).
Proof. exact (MK_COMB (@lem2418810) (@lem2418809 w)). Qed.
Lemma lem2418812 (w : int) : (term522 w) = (term512 w).
Proof. exact (eq_refl (term522 w)). Qed.
Lemma lem2418813 (w : int) : (term523 w) = (term513 w).
Proof. exact (MK_COMB (@lem2418811 w) (@lem2418812 w)). Qed.
Lemma lem2418814 : term524 = term514.
Proof. exact (fun_ext (fun w : int => @lem2418813 w)). Qed.
Lemma lem2418815 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418816 : term516 = term515.
Proof. exact (MK_COMB (@lem2418815) (@lem2418814)). Qed.
Lemma lem2418817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2418818 : term525 = term526.
Proof. exact (MK_COMB (@lem2418817) (@lem2418816)). Qed.
Lemma lem2418819 (w : int) : (term520 w) = (term507 w).
Proof. exact (eq_refl (term520 w)). Qed.
Lemma lem2418820 : term527 = term518.
Proof. exact (fun_ext (fun w : int => @lem2418819 w)). Qed.
Lemma lem2418821 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418822 : term528 = term529.
Proof. exact (MK_COMB (@lem2418821) (@lem2418820)). Qed.
Lemma lem2418823 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418824 : term530 = term531.
Proof. exact (MK_COMB (@lem2418823) (@lem2418822)). Qed.
Lemma lem2418825 (w : int) : (term522 w) = (term512 w).
Proof. exact (eq_refl (term522 w)). Qed.
Lemma lem2418826 : term532 = term519.
Proof. exact (fun_ext (fun w : int => @lem2418825 w)). Qed.
Lemma lem2418827 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418828 : term533 = term534.
Proof. exact (MK_COMB (@lem2418827) (@lem2418826)). Qed.
Lemma lem2418829 : term517 = term535.
Proof. exact (MK_COMB (@lem2418824) (@lem2418828)). Qed.
Lemma lem2418830 : (term516 = term517) = (term515 = term535).
Proof. exact (MK_COMB (@lem2418818) (@lem2418829)). Qed.
Lemma lem2418831 : term515 = term535.
Proof. exact (EQ_MP (@lem2418830) (@lem2418808)). Qed.
Lemma lem2418962 : term353 = term535.
Proof. exact (TRANS (@lem2418804) (@lem2418831)). Qed.
Lemma lem2418963 : term355 = term536.
Proof. exact (MK_COMB (@lem2418358) (@lem2418962)). Qed.
Lemma lem2418966 : term357 = term537.
Proof. exact (MK_COMB (@lem2417915) (@lem2418963)). Qed.
Lemma lem2418970 : term359 = term537.
Proof. exact (TRANS (@lem2417874) (@lem2418966)). Qed.
Lemma lem2418971 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2418972 : term366 = term366.
Proof. exact (fun_ext (fun x : int => @lem2418971 x)). Qed.
Lemma lem2418973 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418974 : term377 = term377.
Proof. exact (MK_COMB (@lem2418973) (@lem2418972)). Qed.
Lemma lem2418975 (x : int) : (term210 x) = (term210 x).
Proof. exact (eq_refl (term210 x)). Qed.
Lemma lem2418976 : term367 = term367.
Proof. exact (fun_ext (fun x : int => @lem2418975 x)). Qed.
Lemma lem2418977 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418978 : term382 = term382.
Proof. exact (MK_COMB (@lem2418977) (@lem2418976)). Qed.
Lemma lem2418979 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2418980 : term379 = term379.
Proof. exact (MK_COMB (@lem2418979) (@lem2418974)). Qed.
Lemma lem2418981 : term383 = term383.
Proof. exact (MK_COMB (@lem2418980) (@lem2418978)). Qed.
Lemma lem2418990 (x : int) (y : int) (z : int) : (term243 x y z) = (term243 x y z).
Proof. exact (eq_refl (term243 x y z)). Qed.
Lemma lem2418991 (x : int) (y : int) : (term387 x y) = (term387 x y).
Proof. exact (fun_ext (fun z : int => @lem2418990 x y z)). Qed.
Lemma lem2418992 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418993 (x : int) (y : int) : (term398 x y) = (term398 x y).
Proof. exact (MK_COMB (@lem2418992) (@lem2418991 x y)). Qed.
Lemma lem2418994 (x : int) : (term409 x) = (term409 x).
Proof. exact (fun_ext (fun y : int => @lem2418993 x y)). Qed.
Lemma lem2418995 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418996 (x : int) : (term420 x) = (term420 x).
Proof. exact (MK_COMB (@lem2418995) (@lem2418994 x)). Qed.
Lemma lem2418997 : term431 = term431.
Proof. exact (fun_ext (fun x : int => @lem2418996 x)). Qed.
Lemma lem2418998 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2418999 : term442 = term442.
Proof. exact (MK_COMB (@lem2418998) (@lem2418997)). Qed.
Lemma lem2419008 (x : int) (y : int) (z : int) : (term268 x y z) = (term268 x y z).
Proof. exact (eq_refl (term268 x y z)). Qed.
Lemma lem2419009 (x : int) (y : int) : (term388 x y) = (term388 x y).
Proof. exact (fun_ext (fun z : int => @lem2419008 x y z)). Qed.
Lemma lem2419010 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419011 (x : int) (y : int) : (term403 x y) = (term403 x y).
Proof. exact (MK_COMB (@lem2419010) (@lem2419009 x y)). Qed.
Lemma lem2419012 (x : int) : (term410 x) = (term410 x).
Proof. exact (fun_ext (fun y : int => @lem2419011 x y)). Qed.
Lemma lem2419013 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419014 (x : int) : (term425 x) = (term425 x).
Proof. exact (MK_COMB (@lem2419013) (@lem2419012 x)). Qed.
Lemma lem2419015 : term432 = term432.
Proof. exact (fun_ext (fun x : int => @lem2419014 x)). Qed.
Lemma lem2419016 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419017 : term447 = term447.
Proof. exact (MK_COMB (@lem2419016) (@lem2419015)). Qed.
Lemma lem2419018 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2419019 : term444 = term444.
Proof. exact (MK_COMB (@lem2419018) (@lem2418999)). Qed.
Lemma lem2419020 : term448 = term448.
Proof. exact (MK_COMB (@lem2419019) (@lem2419017)). Qed.
Lemma lem2419029 (w : int) (x : int) (y : int) (z : int) : (term317 w x y z) = (term317 w x y z).
Proof. exact (eq_refl (term317 w x y z)). Qed.
Lemma lem2419030 (w : int) (x : int) (y : int) : (term452 w x y) = (term452 w x y).
Proof. exact (fun_ext (fun z : int => @lem2419029 w x y z)). Qed.
Lemma lem2419031 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419032 (w : int) (x : int) (y : int) : (term463 w x y) = (term463 w x y).
Proof. exact (MK_COMB (@lem2419031) (@lem2419030 w x y)). Qed.
Lemma lem2419033 (w : int) (x : int) : (term474 w x) = (term474 w x).
Proof. exact (fun_ext (fun y : int => @lem2419032 w x y)). Qed.
Lemma lem2419034 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419035 (w : int) (x : int) : (term485 w x) = (term485 w x).
Proof. exact (MK_COMB (@lem2419034) (@lem2419033 w x)). Qed.
Lemma lem2419036 (w : int) : (term496 w) = (term496 w).
Proof. exact (fun_ext (fun x : int => @lem2419035 w x)). Qed.
Lemma lem2419037 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419038 (w : int) : (term507 w) = (term507 w).
Proof. exact (MK_COMB (@lem2419037) (@lem2419036 w)). Qed.
Lemma lem2419039 : term518 = term518.
Proof. exact (fun_ext (fun w : int => @lem2419038 w)). Qed.
Lemma lem2419040 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419041 : term529 = term529.
Proof. exact (MK_COMB (@lem2419040) (@lem2419039)). Qed.
Lemma lem2419050 (w : int) (x : int) (y : int) (z : int) : (term342 w x y z) = (term342 w x y z).
Proof. exact (eq_refl (term342 w x y z)). Qed.
Lemma lem2419051 (w : int) (x : int) (y : int) : (term453 w x y) = (term453 w x y).
Proof. exact (fun_ext (fun z : int => @lem2419050 w x y z)). Qed.
Lemma lem2419052 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419053 (w : int) (x : int) (y : int) : (term468 w x y) = (term468 w x y).
Proof. exact (MK_COMB (@lem2419052) (@lem2419051 w x y)). Qed.
Lemma lem2419054 (w : int) (x : int) : (term475 w x) = (term475 w x).
Proof. exact (fun_ext (fun y : int => @lem2419053 w x y)). Qed.
Lemma lem2419055 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419056 (w : int) (x : int) : (term490 w x) = (term490 w x).
Proof. exact (MK_COMB (@lem2419055) (@lem2419054 w x)). Qed.
Lemma lem2419057 (w : int) : (term497 w) = (term497 w).
Proof. exact (fun_ext (fun x : int => @lem2419056 w x)). Qed.
Lemma lem2419058 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419059 (w : int) : (term512 w) = (term512 w).
Proof. exact (MK_COMB (@lem2419058) (@lem2419057 w)). Qed.
Lemma lem2419060 : term519 = term519.
Proof. exact (fun_ext (fun w : int => @lem2419059 w)). Qed.
Lemma lem2419061 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419062 : term534 = term534.
Proof. exact (MK_COMB (@lem2419061) (@lem2419060)). Qed.
Lemma lem2419063 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2419064 : term531 = term531.
Proof. exact (MK_COMB (@lem2419063) (@lem2419041)). Qed.
Lemma lem2419065 : term535 = term535.
Proof. exact (MK_COMB (@lem2419064) (@lem2419062)). Qed.
Lemma lem2419066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2419067 : term449 = term449.
Proof. exact (MK_COMB (@lem2419066) (@lem2419020)). Qed.
Lemma lem2419068 : term536 = term536.
Proof. exact (MK_COMB (@lem2419067) (@lem2419065)). Qed.
Lemma lem2419069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2419070 : term384 = term384.
Proof. exact (MK_COMB (@lem2419069) (@lem2418981)). Qed.
Lemma lem2419071 : term537 = term537.
Proof. exact (MK_COMB (@lem2419070) (@lem2419068)). Qed.
Lemma lem2419072 : term359 = term537.
Proof. exact (TRANS (@lem2418970) (@lem2419071)). Qed.
Lemma lem2419073 (x : int) : (term197 x) = (term197 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem2419074 : term366 = term366.
Proof. exact (fun_ext (fun x : int => @lem2419073 x)). Qed.
Lemma lem2419075 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419076 : term377 = term377.
Proof. exact (MK_COMB (@lem2419075) (@lem2419074)). Qed.
Lemma lem2419077 (x : int) : (term210 x) = (term210 x).
Proof. exact (eq_refl (term210 x)). Qed.
Lemma lem2419078 : term367 = term367.
Proof. exact (fun_ext (fun x : int => @lem2419077 x)). Qed.
Lemma lem2419079 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419080 : term382 = term382.
Proof. exact (MK_COMB (@lem2419079) (@lem2419078)). Qed.
Lemma lem2419081 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2419082 : term379 = term379.
Proof. exact (MK_COMB (@lem2419081) (@lem2419076)). Qed.
Lemma lem2419083 : term383 = term383.
Proof. exact (MK_COMB (@lem2419082) (@lem2419080)). Qed.
Lemma lem2419092 (x : int) (y : int) (z : int) : (term243 x y z) = (term243 x y z).
Proof. exact (eq_refl (term243 x y z)). Qed.
Lemma lem2419093 (x : int) (y : int) : (term387 x y) = (term387 x y).
Proof. exact (fun_ext (fun z : int => @lem2419092 x y z)). Qed.
Lemma lem2419094 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419095 (x : int) (y : int) : (term398 x y) = (term398 x y).
Proof. exact (MK_COMB (@lem2419094) (@lem2419093 x y)). Qed.
Lemma lem2419096 (x : int) : (term409 x) = (term409 x).
Proof. exact (fun_ext (fun y : int => @lem2419095 x y)). Qed.
Lemma lem2419097 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419098 (x : int) : (term420 x) = (term420 x).
Proof. exact (MK_COMB (@lem2419097) (@lem2419096 x)). Qed.
Lemma lem2419099 : term431 = term431.
Proof. exact (fun_ext (fun x : int => @lem2419098 x)). Qed.
Lemma lem2419100 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419101 : term442 = term442.
Proof. exact (MK_COMB (@lem2419100) (@lem2419099)). Qed.
Lemma lem2419110 (x : int) (y : int) (z : int) : (term268 x y z) = (term268 x y z).
Proof. exact (eq_refl (term268 x y z)). Qed.
Lemma lem2419111 (x : int) (y : int) : (term388 x y) = (term388 x y).
Proof. exact (fun_ext (fun z : int => @lem2419110 x y z)). Qed.
Lemma lem2419112 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419113 (x : int) (y : int) : (term403 x y) = (term403 x y).
Proof. exact (MK_COMB (@lem2419112) (@lem2419111 x y)). Qed.
Lemma lem2419114 (x : int) : (term410 x) = (term410 x).
Proof. exact (fun_ext (fun y : int => @lem2419113 x y)). Qed.
Lemma lem2419115 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419116 (x : int) : (term425 x) = (term425 x).
Proof. exact (MK_COMB (@lem2419115) (@lem2419114 x)). Qed.
Lemma lem2419117 : term432 = term432.
Proof. exact (fun_ext (fun x : int => @lem2419116 x)). Qed.
Lemma lem2419118 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419119 : term447 = term447.
Proof. exact (MK_COMB (@lem2419118) (@lem2419117)). Qed.
Lemma lem2419120 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2419121 : term444 = term444.
Proof. exact (MK_COMB (@lem2419120) (@lem2419101)). Qed.
Lemma lem2419122 : term448 = term448.
Proof. exact (MK_COMB (@lem2419121) (@lem2419119)). Qed.
Lemma lem2419131 (w : int) (x : int) (y : int) (z : int) : (term317 w x y z) = (term317 w x y z).
Proof. exact (eq_refl (term317 w x y z)). Qed.
Lemma lem2419132 (w : int) (x : int) (y : int) : (term452 w x y) = (term452 w x y).
Proof. exact (fun_ext (fun z : int => @lem2419131 w x y z)). Qed.
Lemma lem2419133 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419134 (w : int) (x : int) (y : int) : (term463 w x y) = (term463 w x y).
Proof. exact (MK_COMB (@lem2419133) (@lem2419132 w x y)). Qed.
Lemma lem2419135 (w : int) (x : int) : (term474 w x) = (term474 w x).
Proof. exact (fun_ext (fun y : int => @lem2419134 w x y)). Qed.
Lemma lem2419136 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419137 (w : int) (x : int) : (term485 w x) = (term485 w x).
Proof. exact (MK_COMB (@lem2419136) (@lem2419135 w x)). Qed.
Lemma lem2419138 (w : int) : (term496 w) = (term496 w).
Proof. exact (fun_ext (fun x : int => @lem2419137 w x)). Qed.
Lemma lem2419139 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419140 (w : int) : (term507 w) = (term507 w).
Proof. exact (MK_COMB (@lem2419139) (@lem2419138 w)). Qed.
Lemma lem2419141 : term518 = term518.
Proof. exact (fun_ext (fun w : int => @lem2419140 w)). Qed.
Lemma lem2419142 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419143 : term529 = term529.
Proof. exact (MK_COMB (@lem2419142) (@lem2419141)). Qed.
Lemma lem2419152 (w : int) (x : int) (y : int) (z : int) : (term342 w x y z) = (term342 w x y z).
Proof. exact (eq_refl (term342 w x y z)). Qed.
Lemma lem2419153 (w : int) (x : int) (y : int) : (term453 w x y) = (term453 w x y).
Proof. exact (fun_ext (fun z : int => @lem2419152 w x y z)). Qed.
Lemma lem2419154 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419155 (w : int) (x : int) (y : int) : (term468 w x y) = (term468 w x y).
Proof. exact (MK_COMB (@lem2419154) (@lem2419153 w x y)). Qed.
Lemma lem2419156 (w : int) (x : int) : (term475 w x) = (term475 w x).
Proof. exact (fun_ext (fun y : int => @lem2419155 w x y)). Qed.
Lemma lem2419157 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419158 (w : int) (x : int) : (term490 w x) = (term490 w x).
Proof. exact (MK_COMB (@lem2419157) (@lem2419156 w x)). Qed.
Lemma lem2419159 (w : int) : (term497 w) = (term497 w).
Proof. exact (fun_ext (fun x : int => @lem2419158 w x)). Qed.
Lemma lem2419160 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419161 (w : int) : (term512 w) = (term512 w).
Proof. exact (MK_COMB (@lem2419160) (@lem2419159 w)). Qed.
Lemma lem2419162 : term519 = term519.
Proof. exact (fun_ext (fun w : int => @lem2419161 w)). Qed.
Lemma lem2419163 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419164 : term534 = term534.
Proof. exact (MK_COMB (@lem2419163) (@lem2419162)). Qed.
Lemma lem2419165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2419166 : term531 = term531.
Proof. exact (MK_COMB (@lem2419165) (@lem2419143)). Qed.
Lemma lem2419167 : term535 = term535.
Proof. exact (MK_COMB (@lem2419166) (@lem2419164)). Qed.
Lemma lem2419168 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2419169 : term449 = term449.
Proof. exact (MK_COMB (@lem2419168) (@lem2419122)). Qed.
Lemma lem2419170 : term536 = term536.
Proof. exact (MK_COMB (@lem2419169) (@lem2419167)). Qed.
Lemma lem2419171 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2419172 : term384 = term384.
Proof. exact (MK_COMB (@lem2419171) (@lem2419083)). Qed.
Lemma lem2419173 : term537 = term537.
Proof. exact (MK_COMB (@lem2419172) (@lem2419170)). Qed.
Lemma lem2419174 : term359 = term537.
Proof. exact (TRANS (@lem2419072) (@lem2419173)). Qed.
Lemma lem2419175 (x : int) : (term197 x) = (term538 x).
Proof. exact (@lem1988287 term182 (term194 x)). Qed.
Lemma lem2419176 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2419177 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2419184 (x : int) : (term185 x) = term182.
Proof. exact (@lem1982729 (real_of_int x)). Qed.
Lemma lem2419185 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2419186 (x : int) : (term187 x) = term539.
Proof. exact (MK_COMB (@lem2419185) (@lem2419184 x)). Qed.
Lemma lem2419187 (x : int) : (term188 x) = term540.
Proof. exact (MK_COMB (@lem2419186 x) (@lem2419177)). Qed.
Lemma lem2419188 : term540 = term541.
Proof. exact (@lem1982792 term182 term182). Qed.
Lemma lem2419190 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2419191 : term182 = term543.
Proof. exact (@lem2419190 (NUMERAL 0)). Qed.
Lemma lem2419193 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2419194 : term546 = term547.
Proof. exact (@lem2419193 term193). Qed.
Lemma lem2419195 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419196 : term548 = term549.
Proof. exact (MK_COMB (@lem2419195) (@lem2419194)). Qed.
Lemma lem2419197 : term550 = term551.
Proof. exact (MK_COMB (@lem2419196) (@lem2419191)). Qed.
Lemma lem2419198 : term551 = term552.
Proof. exact (@lem1981613 term546 term182 term192 term192). Qed.
Lemma lem2419200 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419201 : term555 = term556.
Proof. exact (@lem2419200 term193 term193). Qed.
Lemma lem2419202 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419203 : term558 = term193.
Proof. exact (EQ_MP (@lem2419202) (@lem940073)). Qed.
Lemma lem2419204 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419205 : term556 = term192.
Proof. exact (MK_COMB (@lem2419204) (@lem2419203)). Qed.
Lemma lem2419206 : term555 = term192.
Proof. exact (TRANS (@lem2419201) (@lem2419205)). Qed.
Lemma lem2419208 (x : nat) : (term559 x) = term182.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2419209 : term550 = term182.
Proof. exact (@lem2419208 term193). Qed.
Lemma lem2419210 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2419211 : term560 = term561.
Proof. exact (MK_COMB (@lem2419210) (@lem2419209)). Qed.
Lemma lem2419212 : term552 = term543.
Proof. exact (MK_COMB (@lem2419211) (@lem2419206)). Qed.
Lemma lem2419213 : term551 = term543.
Proof. exact (TRANS (@lem2419198) (@lem2419212)). Qed.
Lemma lem2419214 : term550 = term543.
Proof. exact (TRANS (@lem2419197) (@lem2419213)). Qed.
Lemma lem2419216 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2419217 : term543 = term182.
Proof. exact (@lem2419216 term182). Qed.
Lemma lem2419218 : term550 = term182.
Proof. exact (TRANS (@lem2419214) (@lem2419217)). Qed.
Lemma lem2419219 : term206 = term206.
Proof. exact (eq_refl term206). Qed.
Lemma lem2419220 : term541 = term563.
Proof. exact (MK_COMB (@lem2419219) (@lem2419218)). Qed.
Lemma lem2419221 : term563 = term182.
Proof. exact (@lem1982721 term182). Qed.
Lemma lem2419222 : term541 = term182.
Proof. exact (TRANS (@lem2419220) (@lem2419221)). Qed.
Lemma lem2419223 : term540 = term182.
Proof. exact (TRANS (@lem2419188) (@lem2419222)). Qed.
Lemma lem2419224 (x : int) : (term188 x) = term182.
Proof. exact (TRANS (@lem2419187 x) (@lem2419223)). Qed.
Lemma lem2419225 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2419226 (x : int) : (term190 x) = term206.
Proof. exact (MK_COMB (@lem2419225) (@lem2419224 x)). Qed.
Lemma lem2419227 (x : int) : (term194 x) = term207.
Proof. exact (MK_COMB (@lem2419226 x) (@lem2419176)). Qed.
Lemma lem2419228 : term207 = term192.
Proof. exact (@lem1982721 term192). Qed.
Lemma lem2419229 (x : int) : (term194 x) = term192.
Proof. exact (TRANS (@lem2419227 x) (@lem2419228)). Qed.
Lemma lem2419232 : term539 = term539.
Proof. exact (eq_refl term539). Qed.
Lemma lem2419233 (x : int) : (term564 x) = term565.
Proof. exact (MK_COMB (@lem2419232) (@lem2419229 x)). Qed.
Lemma lem2419234 : term565 = term566.
Proof. exact (@lem1982792 term182 term192). Qed.
Lemma lem2419236 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2419237 : term192 = term567.
Proof. exact (@lem2419236 term193). Qed.
Lemma lem2419239 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2419240 : term546 = term547.
Proof. exact (@lem2419239 term193). Qed.
Lemma lem2419241 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419242 : term548 = term549.
Proof. exact (MK_COMB (@lem2419241) (@lem2419240)). Qed.
Lemma lem2419243 : term568 = term569.
Proof. exact (MK_COMB (@lem2419242) (@lem2419237)). Qed.
Lemma lem2419244 : term569 = term570.
Proof. exact (@lem1981613 term546 term192 term192 term192). Qed.
Lemma lem2419246 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419247 : term555 = term556.
Proof. exact (@lem2419246 term193 term193). Qed.
Lemma lem2419248 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419249 : term558 = term193.
Proof. exact (EQ_MP (@lem2419248) (@lem940073)). Qed.
Lemma lem2419250 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419251 : term556 = term192.
Proof. exact (MK_COMB (@lem2419250) (@lem2419249)). Qed.
Lemma lem2419252 : term555 = term192.
Proof. exact (TRANS (@lem2419247) (@lem2419251)). Qed.
Lemma lem2419254 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2419255 : term568 = term573.
Proof. exact (@lem2419254 term193 term193). Qed.
Lemma lem2419256 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419257 : term558 = term193.
Proof. exact (EQ_MP (@lem2419256) (@lem940073)). Qed.
Lemma lem2419258 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419259 : term556 = term192.
Proof. exact (MK_COMB (@lem2419258) (@lem2419257)). Qed.
Lemma lem2419260 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2419261 : term573 = term546.
Proof. exact (MK_COMB (@lem2419260) (@lem2419259)). Qed.
Lemma lem2419262 : term568 = term546.
Proof. exact (TRANS (@lem2419255) (@lem2419261)). Qed.
Lemma lem2419263 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2419264 : term574 = term575.
Proof. exact (MK_COMB (@lem2419263) (@lem2419262)). Qed.
Lemma lem2419265 : term570 = term547.
Proof. exact (MK_COMB (@lem2419264) (@lem2419252)). Qed.
Lemma lem2419266 : term569 = term547.
Proof. exact (TRANS (@lem2419244) (@lem2419265)). Qed.
Lemma lem2419267 : term568 = term547.
Proof. exact (TRANS (@lem2419243) (@lem2419266)). Qed.
Lemma lem2419269 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2419270 : term547 = term546.
Proof. exact (@lem2419269 term546). Qed.
Lemma lem2419271 : term568 = term546.
Proof. exact (TRANS (@lem2419267) (@lem2419270)). Qed.
Lemma lem2419272 : term206 = term206.
Proof. exact (eq_refl term206). Qed.
Lemma lem2419273 : term566 = term576.
Proof. exact (MK_COMB (@lem2419272) (@lem2419271)). Qed.
Lemma lem2419274 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2419275 : term566 = term546.
Proof. exact (TRANS (@lem2419273) (@lem2419274)). Qed.
Lemma lem2419276 : term565 = term546.
Proof. exact (TRANS (@lem2419234) (@lem2419275)). Qed.
Lemma lem2419277 (x : int) : (term564 x) = term546.
Proof. exact (TRANS (@lem2419233 x) (@lem2419276)). Qed.
Lemma lem2419278 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2419279 (x : int) : (term577 x) = term578.
Proof. exact (MK_COMB (@lem2419278) (@lem2419277 x)). Qed.
Lemma lem2419280 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2419281 (x : int) : (term538 x) = term579.
Proof. exact (MK_COMB (@lem2419279 x) (@lem2419280)). Qed.
Lemma lem2419282 (x : int) : (term197 x) = term579.
Proof. exact (TRANS (@lem2419175 x) (@lem2419281 x)). Qed.
Lemma lem2419283 : term366 = term580.
Proof. exact (fun_ext (fun x : int => @lem2419282 x)). Qed.
Lemma lem2419284 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419285 : term377 = term581.
Proof. exact (MK_COMB (@lem2419284) (@lem2419283)). Qed.
Lemma lem2419286 (x : int) : (term210 x) = (term582 x).
Proof. exact (@lem1988287 (term188 x) term207). Qed.
Lemma lem2419293 : term207 = term192.
Proof. exact (@lem1982721 term192). Qed.
Lemma lem2419294 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2419301 (x : int) : (term185 x) = term182.
Proof. exact (@lem1982729 (real_of_int x)). Qed.
Lemma lem2419302 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2419303 (x : int) : (term187 x) = term539.
Proof. exact (MK_COMB (@lem2419302) (@lem2419301 x)). Qed.
Lemma lem2419304 (x : int) : (term188 x) = term540.
Proof. exact (MK_COMB (@lem2419303 x) (@lem2419294)). Qed.
Lemma lem2419305 : term540 = term541.
Proof. exact (@lem1982792 term182 term182). Qed.
Lemma lem2419307 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2419308 : term182 = term543.
Proof. exact (@lem2419307 (NUMERAL 0)). Qed.
Lemma lem2419310 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2419311 : term546 = term547.
Proof. exact (@lem2419310 term193). Qed.
Lemma lem2419312 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419313 : term548 = term549.
Proof. exact (MK_COMB (@lem2419312) (@lem2419311)). Qed.
Lemma lem2419314 : term550 = term551.
Proof. exact (MK_COMB (@lem2419313) (@lem2419308)). Qed.
Lemma lem2419315 : term551 = term552.
Proof. exact (@lem1981613 term546 term182 term192 term192). Qed.
Lemma lem2419317 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419318 : term555 = term556.
Proof. exact (@lem2419317 term193 term193). Qed.
Lemma lem2419319 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419320 : term558 = term193.
Proof. exact (EQ_MP (@lem2419319) (@lem940073)). Qed.
Lemma lem2419321 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419322 : term556 = term192.
Proof. exact (MK_COMB (@lem2419321) (@lem2419320)). Qed.
Lemma lem2419323 : term555 = term192.
Proof. exact (TRANS (@lem2419318) (@lem2419322)). Qed.
Lemma lem2419325 (x : nat) : (term559 x) = term182.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2419326 : term550 = term182.
Proof. exact (@lem2419325 term193). Qed.
Lemma lem2419327 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2419328 : term560 = term561.
Proof. exact (MK_COMB (@lem2419327) (@lem2419326)). Qed.
Lemma lem2419329 : term552 = term543.
Proof. exact (MK_COMB (@lem2419328) (@lem2419323)). Qed.
Lemma lem2419330 : term551 = term543.
Proof. exact (TRANS (@lem2419315) (@lem2419329)). Qed.
Lemma lem2419331 : term550 = term543.
Proof. exact (TRANS (@lem2419314) (@lem2419330)). Qed.
Lemma lem2419333 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2419334 : term543 = term182.
Proof. exact (@lem2419333 term182). Qed.
Lemma lem2419335 : term550 = term182.
Proof. exact (TRANS (@lem2419331) (@lem2419334)). Qed.
Lemma lem2419336 : term206 = term206.
Proof. exact (eq_refl term206). Qed.
Lemma lem2419337 : term541 = term563.
Proof. exact (MK_COMB (@lem2419336) (@lem2419335)). Qed.
Lemma lem2419338 : term563 = term182.
Proof. exact (@lem1982721 term182). Qed.
Lemma lem2419339 : term541 = term182.
Proof. exact (TRANS (@lem2419337) (@lem2419338)). Qed.
Lemma lem2419340 : term540 = term182.
Proof. exact (TRANS (@lem2419305) (@lem2419339)). Qed.
Lemma lem2419341 (x : int) : (term188 x) = term182.
Proof. exact (TRANS (@lem2419304 x) (@lem2419340)). Qed.
Lemma lem2419342 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2419343 (x : int) : (term583 x) = term539.
Proof. exact (MK_COMB (@lem2419342) (@lem2419341 x)). Qed.
Lemma lem2419344 (x : int) : (term584 x) = term565.
Proof. exact (MK_COMB (@lem2419343 x) (@lem2419293)). Qed.
Lemma lem2419345 : term565 = term566.
Proof. exact (@lem1982792 term182 term192). Qed.
Lemma lem2419347 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2419348 : term192 = term567.
Proof. exact (@lem2419347 term193). Qed.
Lemma lem2419350 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2419351 : term546 = term547.
Proof. exact (@lem2419350 term193). Qed.
Lemma lem2419352 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419353 : term548 = term549.
Proof. exact (MK_COMB (@lem2419352) (@lem2419351)). Qed.
Lemma lem2419354 : term568 = term569.
Proof. exact (MK_COMB (@lem2419353) (@lem2419348)). Qed.
Lemma lem2419355 : term569 = term570.
Proof. exact (@lem1981613 term546 term192 term192 term192). Qed.
Lemma lem2419357 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419358 : term555 = term556.
Proof. exact (@lem2419357 term193 term193). Qed.
Lemma lem2419359 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419360 : term558 = term193.
Proof. exact (EQ_MP (@lem2419359) (@lem940073)). Qed.
Lemma lem2419361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419362 : term556 = term192.
Proof. exact (MK_COMB (@lem2419361) (@lem2419360)). Qed.
Lemma lem2419363 : term555 = term192.
Proof. exact (TRANS (@lem2419358) (@lem2419362)). Qed.
Lemma lem2419365 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2419366 : term568 = term573.
Proof. exact (@lem2419365 term193 term193). Qed.
Lemma lem2419367 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419368 : term558 = term193.
Proof. exact (EQ_MP (@lem2419367) (@lem940073)). Qed.
Lemma lem2419369 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419370 : term556 = term192.
Proof. exact (MK_COMB (@lem2419369) (@lem2419368)). Qed.
Lemma lem2419371 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2419372 : term573 = term546.
Proof. exact (MK_COMB (@lem2419371) (@lem2419370)). Qed.
Lemma lem2419373 : term568 = term546.
Proof. exact (TRANS (@lem2419366) (@lem2419372)). Qed.
Lemma lem2419374 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2419375 : term574 = term575.
Proof. exact (MK_COMB (@lem2419374) (@lem2419373)). Qed.
Lemma lem2419376 : term570 = term547.
Proof. exact (MK_COMB (@lem2419375) (@lem2419363)). Qed.
Lemma lem2419377 : term569 = term547.
Proof. exact (TRANS (@lem2419355) (@lem2419376)). Qed.
Lemma lem2419378 : term568 = term547.
Proof. exact (TRANS (@lem2419354) (@lem2419377)). Qed.
Lemma lem2419380 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2419381 : term547 = term546.
Proof. exact (@lem2419380 term546). Qed.
Lemma lem2419382 : term568 = term546.
Proof. exact (TRANS (@lem2419378) (@lem2419381)). Qed.
Lemma lem2419383 : term206 = term206.
Proof. exact (eq_refl term206). Qed.
Lemma lem2419384 : term566 = term576.
Proof. exact (MK_COMB (@lem2419383) (@lem2419382)). Qed.
Lemma lem2419385 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2419386 : term566 = term546.
Proof. exact (TRANS (@lem2419384) (@lem2419385)). Qed.
Lemma lem2419387 : term565 = term546.
Proof. exact (TRANS (@lem2419345) (@lem2419386)). Qed.
Lemma lem2419388 (x : int) : (term584 x) = term546.
Proof. exact (TRANS (@lem2419344 x) (@lem2419387)). Qed.
Lemma lem2419389 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2419390 (x : int) : (term585 x) = term578.
Proof. exact (MK_COMB (@lem2419389) (@lem2419388 x)). Qed.
Lemma lem2419391 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2419392 (x : int) : (term582 x) = term579.
Proof. exact (MK_COMB (@lem2419390 x) (@lem2419391)). Qed.
Lemma lem2419393 (x : int) : (term210 x) = term579.
Proof. exact (TRANS (@lem2419286 x) (@lem2419392 x)). Qed.
Lemma lem2419394 : term367 = term580.
Proof. exact (fun_ext (fun x : int => @lem2419393 x)). Qed.
Lemma lem2419395 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419396 : term382 = term581.
Proof. exact (MK_COMB (@lem2419395) (@lem2419394)). Qed.
Lemma lem2419397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2419398 : term379 = term586.
Proof. exact (MK_COMB (@lem2419397) (@lem2419285)). Qed.
Lemma lem2419399 : term383 = term587.
Proof. exact (MK_COMB (@lem2419398) (@lem2419396)). Qed.
Lemma lem2419400 (y : int) (x : int) (z : int) : ((term218 y x z) = term182) = ((term588 y x z) = term182).
Proof. exact (@lem1988293 (term218 y x z) term182). Qed.
Lemma lem2419401 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2419419 (y : int) (x : int) (z : int) : (term218 y x z) = (term589 y x z).
Proof. exact (@lem1982792 (term168 x y) (term168 x z)). Qed.
Lemma lem2419426 (x : int) (z : int) : (term590 x z) = (term591 x z).
Proof. exact (@lem1982781 (real_of_int x) term546 (real_of_int z)). Qed.
Lemma lem2419427 (x : int) (y : int) : (term592 x y) = (term592 x y).
Proof. exact (eq_refl (term592 x y)). Qed.
Lemma lem2419428 (y : int) (x : int) (z : int) : (term589 y x z) = (term593 y x z).
Proof. exact (MK_COMB (@lem2419427 x y) (@lem2419426 x z)). Qed.
Lemma lem2419429 (x : int) (y : int) (z : int) : (term593 y x z) = (term594 x y z).
Proof. exact (@lem1982753 (real_of_int x) (term595 x) (real_of_int y) (term595 z)). Qed.
Lemma lem2419430 (x : int) : (term596 x) = (term597 x).
Proof. exact (@lem1982715 term546 (real_of_int x)). Qed.
Lemma lem2419432 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2419433 : term192 = term567.
Proof. exact (@lem2419432 term193). Qed.
Lemma lem2419435 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2419436 : term546 = term547.
Proof. exact (@lem2419435 term193). Qed.
Lemma lem2419437 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2419438 : term598 = term599.
Proof. exact (MK_COMB (@lem2419437) (@lem2419436)). Qed.
Lemma lem2419439 : term600 = term601.
Proof. exact (MK_COMB (@lem2419438) (@lem2419433)). Qed.
Lemma lem2419440 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2419442 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2419443 : term604 = term605.
Proof. exact (@lem2419442 (NUMERAL 0) term193). Qed.
Lemma lem2419444 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2419445 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2419446 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2419445 h1) (fun h1 : term605 = True => @lem2419444)). Qed.
Lemma lem2419447 : term605 = True.
Proof. exact (EQ_MP (@lem2419446) (@lem2419444)). Qed.
Lemma lem2419448 : term604 = True.
Proof. exact (TRANS (@lem2419443) (@lem2419447)). Qed.
Lemma lem2419449 : True = term604.
Proof. exact (SYM (@lem2419448)). Qed.
Lemma lem2419450 : term604.
Proof. exact (EQ_MP (@lem2419449) (@lem0)). Qed.
Lemma lem2419451 : term607.
Proof. exact (@lem2419440 (@lem2419450)). Qed.
Lemma lem2419453 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2419454 : term604 = term605.
Proof. exact (@lem2419453 (NUMERAL 0) term193). Qed.
Lemma lem2419455 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2419456 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2419457 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2419456 h1) (fun h1 : term605 = True => @lem2419455)). Qed.
Lemma lem2419458 : term605 = True.
Proof. exact (EQ_MP (@lem2419457) (@lem2419455)). Qed.
Lemma lem2419459 : term604 = True.
Proof. exact (TRANS (@lem2419454) (@lem2419458)). Qed.
Lemma lem2419460 : True = term604.
Proof. exact (SYM (@lem2419459)). Qed.
Lemma lem2419461 : term604.
Proof. exact (EQ_MP (@lem2419460) (@lem0)). Qed.
Lemma lem2419462 : term608.
Proof. exact (@lem2419451 (@lem2419461)). Qed.
Lemma lem2419464 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2419465 : term604 = term605.
Proof. exact (@lem2419464 (NUMERAL 0) term193). Qed.
Lemma lem2419466 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2419467 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2419468 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2419467 h1) (fun h1 : term605 = True => @lem2419466)). Qed.
Lemma lem2419469 : term605 = True.
Proof. exact (EQ_MP (@lem2419468) (@lem2419466)). Qed.
Lemma lem2419470 : term604 = True.
Proof. exact (TRANS (@lem2419465) (@lem2419469)). Qed.
Lemma lem2419471 : True = term604.
Proof. exact (SYM (@lem2419470)). Qed.
Lemma lem2419472 : term604.
Proof. exact (EQ_MP (@lem2419471) (@lem0)). Qed.
Lemma lem2419473 : term609.
Proof. exact (@lem2419462 (@lem2419472)). Qed.
Lemma lem2419475 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419476 : term555 = term556.
Proof. exact (@lem2419475 term193 term193). Qed.
Lemma lem2419477 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419478 : term558 = term193.
Proof. exact (EQ_MP (@lem2419477) (@lem940073)). Qed.
Lemma lem2419479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419480 : term556 = term192.
Proof. exact (MK_COMB (@lem2419479) (@lem2419478)). Qed.
Lemma lem2419481 : term555 = term192.
Proof. exact (TRANS (@lem2419476) (@lem2419480)). Qed.
Lemma lem2419483 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2419484 : term568 = term573.
Proof. exact (@lem2419483 term193 term193). Qed.
Lemma lem2419485 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419486 : term558 = term193.
Proof. exact (EQ_MP (@lem2419485) (@lem940073)). Qed.
Lemma lem2419487 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419488 : term556 = term192.
Proof. exact (MK_COMB (@lem2419487) (@lem2419486)). Qed.
Lemma lem2419489 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2419490 : term573 = term546.
Proof. exact (MK_COMB (@lem2419489) (@lem2419488)). Qed.
Lemma lem2419491 : term568 = term546.
Proof. exact (TRANS (@lem2419484) (@lem2419490)). Qed.
Lemma lem2419492 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2419493 : term610 = term598.
Proof. exact (MK_COMB (@lem2419492) (@lem2419491)). Qed.
Lemma lem2419494 : term611 = term600.
Proof. exact (MK_COMB (@lem2419493) (@lem2419481)). Qed.
Lemma lem2419496 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2419497 : term600 = term182.
Proof. exact (@lem2419496 term193). Qed.
Lemma lem2419498 : term611 = term182.
Proof. exact (TRANS (@lem2419494) (@lem2419497)). Qed.
Lemma lem2419499 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419500 : term613 = term184.
Proof. exact (MK_COMB (@lem2419499) (@lem2419498)). Qed.
Lemma lem2419501 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2419502 : term614 = term615.
Proof. exact (MK_COMB (@lem2419500) (@lem2419501)). Qed.
Lemma lem2419504 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2419505 : term615 = term182.
Proof. exact (@lem2419504 term193). Qed.
Lemma lem2419506 : term614 = term182.
Proof. exact (TRANS (@lem2419502) (@lem2419505)). Qed.
Lemma lem2419508 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419509 : term555 = term556.
Proof. exact (@lem2419508 term193 term193). Qed.
Lemma lem2419510 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419511 : term558 = term193.
Proof. exact (EQ_MP (@lem2419510) (@lem940073)). Qed.
Lemma lem2419512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419513 : term556 = term192.
Proof. exact (MK_COMB (@lem2419512) (@lem2419511)). Qed.
Lemma lem2419514 : term555 = term192.
Proof. exact (TRANS (@lem2419509) (@lem2419513)). Qed.
Lemma lem2419515 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2419516 : term617 = term615.
Proof. exact (MK_COMB (@lem2419515) (@lem2419514)). Qed.
Lemma lem2419518 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2419519 : term615 = term182.
Proof. exact (@lem2419518 term193). Qed.
Lemma lem2419520 : term617 = term182.
Proof. exact (TRANS (@lem2419516) (@lem2419519)). Qed.
Lemma lem2419521 : term182 = term617.
Proof. exact (SYM (@lem2419520)). Qed.
Lemma lem2419522 : term614 = term617.
Proof. exact (TRANS (@lem2419506) (@lem2419521)). Qed.
Lemma lem2419523 : term601 = term543.
Proof. exact (@lem2419473 (@lem2419522)). Qed.
Lemma lem2419524 : term600 = term543.
Proof. exact (TRANS (@lem2419439) (@lem2419523)). Qed.
Lemma lem2419526 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2419527 : term543 = term182.
Proof. exact (@lem2419526 term182). Qed.
Lemma lem2419528 : term600 = term182.
Proof. exact (TRANS (@lem2419524) (@lem2419527)). Qed.
Lemma lem2419529 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419530 : term618 = term184.
Proof. exact (MK_COMB (@lem2419529) (@lem2419528)). Qed.
Lemma lem2419531 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2419532 (x : int) : (term597 x) = (term185 x).
Proof. exact (MK_COMB (@lem2419530) (@lem2419531 x)). Qed.
Lemma lem2419533 (x : int) : (term596 x) = (term185 x).
Proof. exact (TRANS (@lem2419430 x) (@lem2419532 x)). Qed.
Lemma lem2419534 (x : int) : (term185 x) = term182.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2419535 (x : int) : (term596 x) = term182.
Proof. exact (TRANS (@lem2419533 x) (@lem2419534 x)). Qed.
Lemma lem2419536 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2419537 (x : int) : (term619 x) = term206.
Proof. exact (MK_COMB (@lem2419536) (@lem2419535 x)). Qed.
Lemma lem2419538 (y : int) (z : int) : (term620 y z) = (term620 y z).
Proof. exact (eq_refl (term620 y z)). Qed.
Lemma lem2419539 (x : int) (y : int) (z : int) : (term594 x y z) = (term621 y z).
Proof. exact (MK_COMB (@lem2419537 x) (@lem2419538 y z)). Qed.
Lemma lem2419540 (x : int) (y : int) (z : int) : (term593 y x z) = (term621 y z).
Proof. exact (TRANS (@lem2419429 x y z) (@lem2419539 x y z)). Qed.
Lemma lem2419541 (y : int) (z : int) : (term621 y z) = (term620 y z).
Proof. exact (@lem1982721 (term620 y z)). Qed.
Lemma lem2419542 (x : int) (y : int) (z : int) : (term593 y x z) = (term620 y z).
Proof. exact (TRANS (@lem2419540 x y z) (@lem2419541 y z)). Qed.
Lemma lem2419543 (x : int) (y : int) (z : int) : (term589 y x z) = (term620 y z).
Proof. exact (TRANS (@lem2419428 y x z) (@lem2419542 x y z)). Qed.
Lemma lem2419545 (x : int) (y : int) (z : int) : (term218 y x z) = (term620 y z).
Proof. exact (TRANS (@lem2419419 y x z) (@lem2419543 x y z)). Qed.
Lemma lem2419546 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2419547 (x : int) (y : int) (z : int) : (term622 y x z) = (term623 y z).
Proof. exact (MK_COMB (@lem2419546) (@lem2419545 x y z)). Qed.
Lemma lem2419548 (x : int) (y : int) (z : int) : (term588 y x z) = (term624 y z).
Proof. exact (MK_COMB (@lem2419547 x y z) (@lem2419401)). Qed.
Lemma lem2419549 (y : int) (z : int) : (term624 y z) = (term625 y z).
Proof. exact (@lem1982792 (term620 y z) term182). Qed.
Lemma lem2419551 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2419552 : term182 = term543.
Proof. exact (@lem2419551 (NUMERAL 0)). Qed.
Lemma lem2419554 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2419555 : term546 = term547.
Proof. exact (@lem2419554 term193). Qed.
Lemma lem2419556 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419557 : term548 = term549.
Proof. exact (MK_COMB (@lem2419556) (@lem2419555)). Qed.
Lemma lem2419558 : term550 = term551.
Proof. exact (MK_COMB (@lem2419557) (@lem2419552)). Qed.
Lemma lem2419559 : term551 = term552.
Proof. exact (@lem1981613 term546 term182 term192 term192). Qed.
Lemma lem2419561 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419562 : term555 = term556.
Proof. exact (@lem2419561 term193 term193). Qed.
Lemma lem2419563 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419564 : term558 = term193.
Proof. exact (EQ_MP (@lem2419563) (@lem940073)). Qed.
Lemma lem2419565 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419566 : term556 = term192.
Proof. exact (MK_COMB (@lem2419565) (@lem2419564)). Qed.
Lemma lem2419567 : term555 = term192.
Proof. exact (TRANS (@lem2419562) (@lem2419566)). Qed.
Lemma lem2419569 (x : nat) : (term559 x) = term182.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2419570 : term550 = term182.
Proof. exact (@lem2419569 term193). Qed.
Lemma lem2419571 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2419572 : term560 = term561.
Proof. exact (MK_COMB (@lem2419571) (@lem2419570)). Qed.
Lemma lem2419573 : term552 = term543.
Proof. exact (MK_COMB (@lem2419572) (@lem2419567)). Qed.
Lemma lem2419574 : term551 = term543.
Proof. exact (TRANS (@lem2419559) (@lem2419573)). Qed.
Lemma lem2419575 : term550 = term543.
Proof. exact (TRANS (@lem2419558) (@lem2419574)). Qed.
Lemma lem2419577 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2419578 : term543 = term182.
Proof. exact (@lem2419577 term182). Qed.
Lemma lem2419579 : term550 = term182.
Proof. exact (TRANS (@lem2419575) (@lem2419578)). Qed.
Lemma lem2419580 (y : int) (z : int) : (term626 y z) = (term626 y z).
Proof. exact (eq_refl (term626 y z)). Qed.
Lemma lem2419581 (y : int) (z : int) : (term625 y z) = (term627 y z).
Proof. exact (MK_COMB (@lem2419580 y z) (@lem2419579)). Qed.
Lemma lem2419582 (y : int) (z : int) : (term627 y z) = (term620 y z).
Proof. exact (@lem1982723 (term620 y z)). Qed.
Lemma lem2419583 (y : int) (z : int) : (term625 y z) = (term620 y z).
Proof. exact (TRANS (@lem2419581 y z) (@lem2419582 y z)). Qed.
Lemma lem2419584 (y : int) (z : int) : (term624 y z) = (term620 y z).
Proof. exact (TRANS (@lem2419549 y z) (@lem2419583 y z)). Qed.
Lemma lem2419585 (x : int) (y : int) (z : int) : (term588 y x z) = (term620 y z).
Proof. exact (TRANS (@lem2419548 x y z) (@lem2419584 y z)). Qed.
Lemma lem2419586 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2419587 (x : int) (y : int) (z : int) : (term628 y x z) = (term629 y z).
Proof. exact (MK_COMB (@lem2419586) (@lem2419585 x y z)). Qed.
Lemma lem2419588 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2419589 (x : int) (y : int) (z : int) : ((term588 y x z) = term182) = ((term620 y z) = term182).
Proof. exact (MK_COMB (@lem2419587 x y z) (@lem2419588)). Qed.
Lemma lem2419590 (x : int) (y : int) (z : int) : ((term218 y x z) = term182) = ((term620 y z) = term182).
Proof. exact (TRANS (@lem2419400 y x z) (@lem2419589 x y z)). Qed.
Lemma lem2419591 (y : int) (z : int) : (term233 y z) = (term630 y z).
Proof. exact (@lem1988287 term182 (term230 y z)). Qed.
Lemma lem2419592 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2419605 (y : int) (z : int) : (term173 y z) = (term620 y z).
Proof. exact (@lem1982792 (real_of_int y) (real_of_int z)). Qed.
Lemma lem2419606 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2419607 (y : int) (z : int) : (term229 y z) = (term626 y z).
Proof. exact (MK_COMB (@lem2419606) (@lem2419605 y z)). Qed.
Lemma lem2419608 (y : int) (z : int) : (term230 y z) = (term631 y z).
Proof. exact (MK_COMB (@lem2419607 y z) (@lem2419592)). Qed.
Lemma lem2419613 (y : int) (z : int) : (term631 y z) = (term632 y z).
Proof. exact (@lem1982755 (real_of_int y) (term595 z) term192). Qed.
Lemma lem2419614 (y : int) (z : int) : (term230 y z) = (term632 y z).
Proof. exact (TRANS (@lem2419608 y z) (@lem2419613 y z)). Qed.
Lemma lem2419617 : term539 = term539.
Proof. exact (eq_refl term539). Qed.
Lemma lem2419618 (y : int) (z : int) : (term633 y z) = (term634 y z).
Proof. exact (MK_COMB (@lem2419617) (@lem2419614 y z)). Qed.
Lemma lem2419619 (y : int) (z : int) : (term634 y z) = (term635 y z).
Proof. exact (@lem1982792 term182 (term632 y z)). Qed.
Lemma lem2419620 (y : int) (z : int) : (term636 y z) = (term637 y z).
Proof. exact (@lem1982781 (real_of_int y) term546 (term638 z)). Qed.
Lemma lem2419621 (z : int) : (term639 z) = (term640 z).
Proof. exact (@lem1982781 (term595 z) term546 term192). Qed.
Lemma lem2419623 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2419624 : term192 = term567.
Proof. exact (@lem2419623 term193). Qed.
Lemma lem2419626 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2419627 : term546 = term547.
Proof. exact (@lem2419626 term193). Qed.
Lemma lem2419628 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419629 : term548 = term549.
Proof. exact (MK_COMB (@lem2419628) (@lem2419627)). Qed.
Lemma lem2419630 : term568 = term569.
Proof. exact (MK_COMB (@lem2419629) (@lem2419624)). Qed.
Lemma lem2419631 : term569 = term570.
Proof. exact (@lem1981613 term546 term192 term192 term192). Qed.
Lemma lem2419633 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419634 : term555 = term556.
Proof. exact (@lem2419633 term193 term193). Qed.
Lemma lem2419635 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419636 : term558 = term193.
Proof. exact (EQ_MP (@lem2419635) (@lem940073)). Qed.
Lemma lem2419637 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419638 : term556 = term192.
Proof. exact (MK_COMB (@lem2419637) (@lem2419636)). Qed.
Lemma lem2419639 : term555 = term192.
Proof. exact (TRANS (@lem2419634) (@lem2419638)). Qed.
Lemma lem2419641 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2419642 : term568 = term573.
Proof. exact (@lem2419641 term193 term193). Qed.
Lemma lem2419643 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419644 : term558 = term193.
Proof. exact (EQ_MP (@lem2419643) (@lem940073)). Qed.
Lemma lem2419645 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419646 : term556 = term192.
Proof. exact (MK_COMB (@lem2419645) (@lem2419644)). Qed.
Lemma lem2419647 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2419648 : term573 = term546.
Proof. exact (MK_COMB (@lem2419647) (@lem2419646)). Qed.
Lemma lem2419649 : term568 = term546.
Proof. exact (TRANS (@lem2419642) (@lem2419648)). Qed.
Lemma lem2419650 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2419651 : term574 = term575.
Proof. exact (MK_COMB (@lem2419650) (@lem2419649)). Qed.
Lemma lem2419652 : term570 = term547.
Proof. exact (MK_COMB (@lem2419651) (@lem2419639)). Qed.
Lemma lem2419653 : term569 = term547.
Proof. exact (TRANS (@lem2419631) (@lem2419652)). Qed.
Lemma lem2419654 : term568 = term547.
Proof. exact (TRANS (@lem2419630) (@lem2419653)). Qed.
Lemma lem2419656 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2419657 : term547 = term546.
Proof. exact (@lem2419656 term546). Qed.
Lemma lem2419658 : term568 = term546.
Proof. exact (TRANS (@lem2419654) (@lem2419657)). Qed.
Lemma lem2419659 (z : int) : (term641 z) = (term642 z).
Proof. exact (@lem1982749 term546 term546 (real_of_int z)). Qed.
Lemma lem2419661 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2419662 : term546 = term547.
Proof. exact (@lem2419661 term193). Qed.
Lemma lem2419664 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2419665 : term546 = term547.
Proof. exact (@lem2419664 term193). Qed.
Lemma lem2419666 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419667 : term548 = term549.
Proof. exact (MK_COMB (@lem2419666) (@lem2419665)). Qed.
Lemma lem2419668 : term643 = term644.
Proof. exact (MK_COMB (@lem2419667) (@lem2419662)). Qed.
Lemma lem2419669 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2419671 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419672 : term555 = term556.
Proof. exact (@lem2419671 term193 term193). Qed.
Lemma lem2419673 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419674 : term558 = term193.
Proof. exact (EQ_MP (@lem2419673) (@lem940073)). Qed.
Lemma lem2419675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419676 : term556 = term192.
Proof. exact (MK_COMB (@lem2419675) (@lem2419674)). Qed.
Lemma lem2419677 : term555 = term192.
Proof. exact (TRANS (@lem2419672) (@lem2419676)). Qed.
Lemma lem2419679 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2419680 : term643 = term556.
Proof. exact (@lem2419679 term193 term193). Qed.
Lemma lem2419681 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419682 : term558 = term193.
Proof. exact (EQ_MP (@lem2419681) (@lem940073)). Qed.
Lemma lem2419683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419684 : term556 = term192.
Proof. exact (MK_COMB (@lem2419683) (@lem2419682)). Qed.
Lemma lem2419685 : term643 = term192.
Proof. exact (TRANS (@lem2419680) (@lem2419684)). Qed.
Lemma lem2419686 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2419687 : term647 = term648.
Proof. exact (MK_COMB (@lem2419686) (@lem2419685)). Qed.
Lemma lem2419688 : term645 = term567.
Proof. exact (MK_COMB (@lem2419687) (@lem2419677)). Qed.
Lemma lem2419689 : term644 = term567.
Proof. exact (TRANS (@lem2419669) (@lem2419688)). Qed.
Lemma lem2419690 : term643 = term567.
Proof. exact (TRANS (@lem2419668) (@lem2419689)). Qed.
Lemma lem2419692 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2419693 : term567 = term192.
Proof. exact (@lem2419692 term192). Qed.
Lemma lem2419694 : term643 = term192.
Proof. exact (TRANS (@lem2419690) (@lem2419693)). Qed.
Lemma lem2419695 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419696 : term649 = term650.
Proof. exact (MK_COMB (@lem2419695) (@lem2419694)). Qed.
Lemma lem2419697 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2419698 (z : int) : (term642 z) = (term651 z).
Proof. exact (MK_COMB (@lem2419696) (@lem2419697 z)). Qed.
Lemma lem2419699 (z : int) : (term641 z) = (term651 z).
Proof. exact (TRANS (@lem2419659 z) (@lem2419698 z)). Qed.
Lemma lem2419700 (z : int) : (term651 z) = (real_of_int z).
Proof. exact (@lem1982709 (real_of_int z)). Qed.
Lemma lem2419701 (z : int) : (term641 z) = (real_of_int z).
Proof. exact (TRANS (@lem2419699 z) (@lem2419700 z)). Qed.
Lemma lem2419702 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2419703 (z : int) : (term652 z) = (term653 z).
Proof. exact (MK_COMB (@lem2419702) (@lem2419701 z)). Qed.
Lemma lem2419704 (z : int) : (term640 z) = (term654 z).
Proof. exact (MK_COMB (@lem2419703 z) (@lem2419658)). Qed.
Lemma lem2419705 (z : int) : (term639 z) = (term654 z).
Proof. exact (TRANS (@lem2419621 z) (@lem2419704 z)). Qed.
Lemma lem2419708 (y : int) : (term655 y) = (term655 y).
Proof. exact (eq_refl (term655 y)). Qed.
Lemma lem2419709 (y : int) (z : int) : (term637 y z) = (term656 y z).
Proof. exact (MK_COMB (@lem2419708 y) (@lem2419705 z)). Qed.
Lemma lem2419710 (y : int) (z : int) : (term636 y z) = (term656 y z).
Proof. exact (TRANS (@lem2419620 y z) (@lem2419709 y z)). Qed.
Lemma lem2419711 : term206 = term206.
Proof. exact (eq_refl term206). Qed.
Lemma lem2419712 (y : int) (z : int) : (term635 y z) = (term657 y z).
Proof. exact (MK_COMB (@lem2419711) (@lem2419710 y z)). Qed.
Lemma lem2419713 (y : int) (z : int) : (term657 y z) = (term656 y z).
Proof. exact (@lem1982721 (term656 y z)). Qed.
Lemma lem2419714 (y : int) (z : int) : (term635 y z) = (term656 y z).
Proof. exact (TRANS (@lem2419712 y z) (@lem2419713 y z)). Qed.
Lemma lem2419715 (y : int) (z : int) : (term634 y z) = (term656 y z).
Proof. exact (TRANS (@lem2419619 y z) (@lem2419714 y z)). Qed.
Lemma lem2419716 (y : int) (z : int) : (term633 y z) = (term656 y z).
Proof. exact (TRANS (@lem2419618 y z) (@lem2419715 y z)). Qed.
Lemma lem2419717 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2419718 (y : int) (z : int) : (term658 y z) = (term659 y z).
Proof. exact (MK_COMB (@lem2419717) (@lem2419716 y z)). Qed.
Lemma lem2419719 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2419720 (y : int) (z : int) : (term630 y z) = (term660 y z).
Proof. exact (MK_COMB (@lem2419718 y z) (@lem2419719)). Qed.
Lemma lem2419721 (y : int) (z : int) : (term233 y z) = (term660 y z).
Proof. exact (TRANS (@lem2419591 y z) (@lem2419720 y z)). Qed.
Lemma lem2419722 (y : int) (z : int) : (term238 y z) = (term661 y z).
Proof. exact (@lem1988287 (term173 y z) term207). Qed.
Lemma lem2419729 : term207 = term192.
Proof. exact (@lem1982721 term192). Qed.
Lemma lem2419742 (y : int) (z : int) : (term173 y z) = (term620 y z).
Proof. exact (@lem1982792 (real_of_int y) (real_of_int z)). Qed.
Lemma lem2419743 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2419744 (y : int) (z : int) : (term662 y z) = (term623 y z).
Proof. exact (MK_COMB (@lem2419743) (@lem2419742 y z)). Qed.
Lemma lem2419745 (y : int) (z : int) : (term663 y z) = (term664 y z).
Proof. exact (MK_COMB (@lem2419744 y z) (@lem2419729)). Qed.
Lemma lem2419746 (y : int) (z : int) : (term664 y z) = (term665 y z).
Proof. exact (@lem1982792 (term620 y z) term192). Qed.
Lemma lem2419748 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2419749 : term192 = term567.
Proof. exact (@lem2419748 term193). Qed.
Lemma lem2419751 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2419752 : term546 = term547.
Proof. exact (@lem2419751 term193). Qed.
Lemma lem2419753 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419754 : term548 = term549.
Proof. exact (MK_COMB (@lem2419753) (@lem2419752)). Qed.
Lemma lem2419755 : term568 = term569.
Proof. exact (MK_COMB (@lem2419754) (@lem2419749)). Qed.
Lemma lem2419756 : term569 = term570.
Proof. exact (@lem1981613 term546 term192 term192 term192). Qed.
Lemma lem2419758 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419759 : term555 = term556.
Proof. exact (@lem2419758 term193 term193). Qed.
Lemma lem2419760 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419761 : term558 = term193.
Proof. exact (EQ_MP (@lem2419760) (@lem940073)). Qed.
Lemma lem2419762 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419763 : term556 = term192.
Proof. exact (MK_COMB (@lem2419762) (@lem2419761)). Qed.
Lemma lem2419764 : term555 = term192.
Proof. exact (TRANS (@lem2419759) (@lem2419763)). Qed.
Lemma lem2419766 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2419767 : term568 = term573.
Proof. exact (@lem2419766 term193 term193). Qed.
Lemma lem2419768 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419769 : term558 = term193.
Proof. exact (EQ_MP (@lem2419768) (@lem940073)). Qed.
Lemma lem2419770 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419771 : term556 = term192.
Proof. exact (MK_COMB (@lem2419770) (@lem2419769)). Qed.
Lemma lem2419772 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2419773 : term573 = term546.
Proof. exact (MK_COMB (@lem2419772) (@lem2419771)). Qed.
Lemma lem2419774 : term568 = term546.
Proof. exact (TRANS (@lem2419767) (@lem2419773)). Qed.
Lemma lem2419775 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2419776 : term574 = term575.
Proof. exact (MK_COMB (@lem2419775) (@lem2419774)). Qed.
Lemma lem2419777 : term570 = term547.
Proof. exact (MK_COMB (@lem2419776) (@lem2419764)). Qed.
Lemma lem2419778 : term569 = term547.
Proof. exact (TRANS (@lem2419756) (@lem2419777)). Qed.
Lemma lem2419779 : term568 = term547.
Proof. exact (TRANS (@lem2419755) (@lem2419778)). Qed.
Lemma lem2419781 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2419782 : term547 = term546.
Proof. exact (@lem2419781 term546). Qed.
Lemma lem2419783 : term568 = term546.
Proof. exact (TRANS (@lem2419779) (@lem2419782)). Qed.
Lemma lem2419784 (y : int) (z : int) : (term626 y z) = (term626 y z).
Proof. exact (eq_refl (term626 y z)). Qed.
Lemma lem2419785 (y : int) (z : int) : (term665 y z) = (term666 y z).
Proof. exact (MK_COMB (@lem2419784 y z) (@lem2419783)). Qed.
Lemma lem2419790 (y : int) (z : int) : (term666 y z) = (term667 y z).
Proof. exact (@lem1982755 (real_of_int y) (term595 z) term546). Qed.
Lemma lem2419791 (y : int) (z : int) : (term665 y z) = (term667 y z).
Proof. exact (TRANS (@lem2419785 y z) (@lem2419790 y z)). Qed.
Lemma lem2419792 (y : int) (z : int) : (term664 y z) = (term667 y z).
Proof. exact (TRANS (@lem2419746 y z) (@lem2419791 y z)). Qed.
Lemma lem2419793 (y : int) (z : int) : (term663 y z) = (term667 y z).
Proof. exact (TRANS (@lem2419745 y z) (@lem2419792 y z)). Qed.
Lemma lem2419794 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2419795 (y : int) (z : int) : (term668 y z) = (term669 y z).
Proof. exact (MK_COMB (@lem2419794) (@lem2419793 y z)). Qed.
Lemma lem2419796 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2419797 (y : int) (z : int) : (term661 y z) = (term670 y z).
Proof. exact (MK_COMB (@lem2419795 y z) (@lem2419796)). Qed.
Lemma lem2419798 (y : int) (z : int) : (term238 y z) = (term670 y z).
Proof. exact (TRANS (@lem2419722 y z) (@lem2419797 y z)). Qed.
Lemma lem2419799 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2419800 (y : int) (z : int) : (term235 y z) = (term671 y z).
Proof. exact (MK_COMB (@lem2419799) (@lem2419721 y z)). Qed.
Lemma lem2419801 (y : int) (z : int) : (term239 y z) = (term672 y z).
Proof. exact (MK_COMB (@lem2419800 y z) (@lem2419798 y z)). Qed.
Lemma lem2419802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2419803 (x : int) (y : int) (z : int) : (term241 y x z) = (term673 y z).
Proof. exact (MK_COMB (@lem2419802) (@lem2419590 x y z)). Qed.
Lemma lem2419804 (x : int) (y : int) (z : int) : (term243 x y z) = (term674 y z).
Proof. exact (MK_COMB (@lem2419803 x y z) (@lem2419801 y z)). Qed.
Lemma lem2419805 (x : int) (y : int) : (term387 x y) = (term675 y).
Proof. exact (fun_ext (fun z : int => @lem2419804 x y z)). Qed.
Lemma lem2419806 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419807 (x : int) (y : int) : (term398 x y) = (term676 y).
Proof. exact (MK_COMB (@lem2419806) (@lem2419805 x y)). Qed.
Lemma lem2419808 (x : int) : (term409 x) = term677.
Proof. exact (fun_ext (fun y : int => @lem2419807 x y)). Qed.
Lemma lem2419809 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419810 (x : int) : (term420 x) = term678.
Proof. exact (MK_COMB (@lem2419809) (@lem2419808 x)). Qed.
Lemma lem2419811 : term431 = term679.
Proof. exact (fun_ext (fun x : int => @lem2419810 x)). Qed.
Lemma lem2419812 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2419813 : term442 = term680.
Proof. exact (MK_COMB (@lem2419812) (@lem2419811)). Qed.
Lemma lem2419814 (y : int) (x : int) (z : int) : (term256 y x z) = (term681 y x z).
Proof. exact (@lem1988287 term182 (term253 y x z)). Qed.
Lemma lem2419815 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2419833 (y : int) (x : int) (z : int) : (term218 y x z) = (term589 y x z).
Proof. exact (@lem1982792 (term168 x y) (term168 x z)). Qed.
Lemma lem2419840 (x : int) (z : int) : (term590 x z) = (term591 x z).
Proof. exact (@lem1982781 (real_of_int x) term546 (real_of_int z)). Qed.
Lemma lem2419841 (x : int) (y : int) : (term592 x y) = (term592 x y).
Proof. exact (eq_refl (term592 x y)). Qed.
Lemma lem2419842 (y : int) (x : int) (z : int) : (term589 y x z) = (term593 y x z).
Proof. exact (MK_COMB (@lem2419841 x y) (@lem2419840 x z)). Qed.
Lemma lem2419843 (x : int) (y : int) (z : int) : (term593 y x z) = (term594 x y z).
Proof. exact (@lem1982753 (real_of_int x) (term595 x) (real_of_int y) (term595 z)). Qed.
Lemma lem2419844 (x : int) : (term596 x) = (term597 x).
Proof. exact (@lem1982715 term546 (real_of_int x)). Qed.
Lemma lem2419846 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2419847 : term192 = term567.
Proof. exact (@lem2419846 term193). Qed.
Lemma lem2419849 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2419850 : term546 = term547.
Proof. exact (@lem2419849 term193). Qed.
Lemma lem2419851 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2419852 : term598 = term599.
Proof. exact (MK_COMB (@lem2419851) (@lem2419850)). Qed.
Lemma lem2419853 : term600 = term601.
Proof. exact (MK_COMB (@lem2419852) (@lem2419847)). Qed.
Lemma lem2419854 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2419856 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2419857 : term604 = term605.
Proof. exact (@lem2419856 (NUMERAL 0) term193). Qed.
Lemma lem2419858 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2419859 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2419860 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2419859 h1) (fun h1 : term605 = True => @lem2419858)). Qed.
Lemma lem2419861 : term605 = True.
Proof. exact (EQ_MP (@lem2419860) (@lem2419858)). Qed.
Lemma lem2419862 : term604 = True.
Proof. exact (TRANS (@lem2419857) (@lem2419861)). Qed.
Lemma lem2419863 : True = term604.
Proof. exact (SYM (@lem2419862)). Qed.
Lemma lem2419864 : term604.
Proof. exact (EQ_MP (@lem2419863) (@lem0)). Qed.
Lemma lem2419865 : term607.
Proof. exact (@lem2419854 (@lem2419864)). Qed.
Lemma lem2419867 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2419868 : term604 = term605.
Proof. exact (@lem2419867 (NUMERAL 0) term193). Qed.
Lemma lem2419869 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2419870 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2419871 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2419870 h1) (fun h1 : term605 = True => @lem2419869)). Qed.
Lemma lem2419872 : term605 = True.
Proof. exact (EQ_MP (@lem2419871) (@lem2419869)). Qed.
Lemma lem2419873 : term604 = True.
Proof. exact (TRANS (@lem2419868) (@lem2419872)). Qed.
Lemma lem2419874 : True = term604.
Proof. exact (SYM (@lem2419873)). Qed.
Lemma lem2419875 : term604.
Proof. exact (EQ_MP (@lem2419874) (@lem0)). Qed.
Lemma lem2419876 : term608.
Proof. exact (@lem2419865 (@lem2419875)). Qed.
Lemma lem2419878 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2419879 : term604 = term605.
Proof. exact (@lem2419878 (NUMERAL 0) term193). Qed.
Lemma lem2419880 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2419881 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2419882 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2419881 h1) (fun h1 : term605 = True => @lem2419880)). Qed.
Lemma lem2419883 : term605 = True.
Proof. exact (EQ_MP (@lem2419882) (@lem2419880)). Qed.
Lemma lem2419884 : term604 = True.
Proof. exact (TRANS (@lem2419879) (@lem2419883)). Qed.
Lemma lem2419885 : True = term604.
Proof. exact (SYM (@lem2419884)). Qed.
Lemma lem2419886 : term604.
Proof. exact (EQ_MP (@lem2419885) (@lem0)). Qed.
Lemma lem2419887 : term609.
Proof. exact (@lem2419876 (@lem2419886)). Qed.
Lemma lem2419889 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419890 : term555 = term556.
Proof. exact (@lem2419889 term193 term193). Qed.
Lemma lem2419891 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419892 : term558 = term193.
Proof. exact (EQ_MP (@lem2419891) (@lem940073)). Qed.
Lemma lem2419893 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419894 : term556 = term192.
Proof. exact (MK_COMB (@lem2419893) (@lem2419892)). Qed.
Lemma lem2419895 : term555 = term192.
Proof. exact (TRANS (@lem2419890) (@lem2419894)). Qed.
Lemma lem2419897 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2419898 : term568 = term573.
Proof. exact (@lem2419897 term193 term193). Qed.
Lemma lem2419899 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419900 : term558 = term193.
Proof. exact (EQ_MP (@lem2419899) (@lem940073)). Qed.
Lemma lem2419901 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419902 : term556 = term192.
Proof. exact (MK_COMB (@lem2419901) (@lem2419900)). Qed.
Lemma lem2419903 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2419904 : term573 = term546.
Proof. exact (MK_COMB (@lem2419903) (@lem2419902)). Qed.
Lemma lem2419905 : term568 = term546.
Proof. exact (TRANS (@lem2419898) (@lem2419904)). Qed.
Lemma lem2419906 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2419907 : term610 = term598.
Proof. exact (MK_COMB (@lem2419906) (@lem2419905)). Qed.
Lemma lem2419908 : term611 = term600.
Proof. exact (MK_COMB (@lem2419907) (@lem2419895)). Qed.
Lemma lem2419910 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2419911 : term600 = term182.
Proof. exact (@lem2419910 term193). Qed.
Lemma lem2419912 : term611 = term182.
Proof. exact (TRANS (@lem2419908) (@lem2419911)). Qed.
Lemma lem2419913 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419914 : term613 = term184.
Proof. exact (MK_COMB (@lem2419913) (@lem2419912)). Qed.
Lemma lem2419915 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2419916 : term614 = term615.
Proof. exact (MK_COMB (@lem2419914) (@lem2419915)). Qed.
Lemma lem2419918 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2419919 : term615 = term182.
Proof. exact (@lem2419918 term193). Qed.
Lemma lem2419920 : term614 = term182.
Proof. exact (TRANS (@lem2419916) (@lem2419919)). Qed.
Lemma lem2419922 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419923 : term555 = term556.
Proof. exact (@lem2419922 term193 term193). Qed.
Lemma lem2419924 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419925 : term558 = term193.
Proof. exact (EQ_MP (@lem2419924) (@lem940073)). Qed.
Lemma lem2419926 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419927 : term556 = term192.
Proof. exact (MK_COMB (@lem2419926) (@lem2419925)). Qed.
Lemma lem2419928 : term555 = term192.
Proof. exact (TRANS (@lem2419923) (@lem2419927)). Qed.
Lemma lem2419929 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2419930 : term617 = term615.
Proof. exact (MK_COMB (@lem2419929) (@lem2419928)). Qed.
Lemma lem2419932 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2419933 : term615 = term182.
Proof. exact (@lem2419932 term193). Qed.
Lemma lem2419934 : term617 = term182.
Proof. exact (TRANS (@lem2419930) (@lem2419933)). Qed.
Lemma lem2419935 : term182 = term617.
Proof. exact (SYM (@lem2419934)). Qed.
Lemma lem2419936 : term614 = term617.
Proof. exact (TRANS (@lem2419920) (@lem2419935)). Qed.
Lemma lem2419937 : term601 = term543.
Proof. exact (@lem2419887 (@lem2419936)). Qed.
Lemma lem2419938 : term600 = term543.
Proof. exact (TRANS (@lem2419853) (@lem2419937)). Qed.
Lemma lem2419940 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2419941 : term543 = term182.
Proof. exact (@lem2419940 term182). Qed.
Lemma lem2419942 : term600 = term182.
Proof. exact (TRANS (@lem2419938) (@lem2419941)). Qed.
Lemma lem2419943 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419944 : term618 = term184.
Proof. exact (MK_COMB (@lem2419943) (@lem2419942)). Qed.
Lemma lem2419945 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2419946 (x : int) : (term597 x) = (term185 x).
Proof. exact (MK_COMB (@lem2419944) (@lem2419945 x)). Qed.
Lemma lem2419947 (x : int) : (term596 x) = (term185 x).
Proof. exact (TRANS (@lem2419844 x) (@lem2419946 x)). Qed.
Lemma lem2419948 (x : int) : (term185 x) = term182.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2419949 (x : int) : (term596 x) = term182.
Proof. exact (TRANS (@lem2419947 x) (@lem2419948 x)). Qed.
Lemma lem2419950 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2419951 (x : int) : (term619 x) = term206.
Proof. exact (MK_COMB (@lem2419950) (@lem2419949 x)). Qed.
Lemma lem2419952 (y : int) (z : int) : (term620 y z) = (term620 y z).
Proof. exact (eq_refl (term620 y z)). Qed.
Lemma lem2419953 (x : int) (y : int) (z : int) : (term594 x y z) = (term621 y z).
Proof. exact (MK_COMB (@lem2419951 x) (@lem2419952 y z)). Qed.
Lemma lem2419954 (x : int) (y : int) (z : int) : (term593 y x z) = (term621 y z).
Proof. exact (TRANS (@lem2419843 x y z) (@lem2419953 x y z)). Qed.
Lemma lem2419955 (y : int) (z : int) : (term621 y z) = (term620 y z).
Proof. exact (@lem1982721 (term620 y z)). Qed.
Lemma lem2419956 (x : int) (y : int) (z : int) : (term593 y x z) = (term620 y z).
Proof. exact (TRANS (@lem2419954 x y z) (@lem2419955 y z)). Qed.
Lemma lem2419957 (x : int) (y : int) (z : int) : (term589 y x z) = (term620 y z).
Proof. exact (TRANS (@lem2419842 y x z) (@lem2419956 x y z)). Qed.
Lemma lem2419959 (x : int) (y : int) (z : int) : (term218 y x z) = (term620 y z).
Proof. exact (TRANS (@lem2419833 y x z) (@lem2419957 x y z)). Qed.
Lemma lem2419960 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2419961 (x : int) (y : int) (z : int) : (term252 y x z) = (term626 y z).
Proof. exact (MK_COMB (@lem2419960) (@lem2419959 x y z)). Qed.
Lemma lem2419962 (x : int) (y : int) (z : int) : (term253 y x z) = (term631 y z).
Proof. exact (MK_COMB (@lem2419961 x y z) (@lem2419815)). Qed.
Lemma lem2419967 (y : int) (z : int) : (term631 y z) = (term632 y z).
Proof. exact (@lem1982755 (real_of_int y) (term595 z) term192). Qed.
Lemma lem2419968 (x : int) (y : int) (z : int) : (term253 y x z) = (term632 y z).
Proof. exact (TRANS (@lem2419962 x y z) (@lem2419967 y z)). Qed.
Lemma lem2419971 : term539 = term539.
Proof. exact (eq_refl term539). Qed.
Lemma lem2419972 (x : int) (y : int) (z : int) : (term682 y x z) = (term634 y z).
Proof. exact (MK_COMB (@lem2419971) (@lem2419968 x y z)). Qed.
Lemma lem2419973 (y : int) (z : int) : (term634 y z) = (term635 y z).
Proof. exact (@lem1982792 term182 (term632 y z)). Qed.
Lemma lem2419974 (y : int) (z : int) : (term636 y z) = (term637 y z).
Proof. exact (@lem1982781 (real_of_int y) term546 (term638 z)). Qed.
Lemma lem2419975 (z : int) : (term639 z) = (term640 z).
Proof. exact (@lem1982781 (term595 z) term546 term192). Qed.
Lemma lem2419977 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2419978 : term192 = term567.
Proof. exact (@lem2419977 term193). Qed.
Lemma lem2419980 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2419981 : term546 = term547.
Proof. exact (@lem2419980 term193). Qed.
Lemma lem2419982 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2419983 : term548 = term549.
Proof. exact (MK_COMB (@lem2419982) (@lem2419981)). Qed.
Lemma lem2419984 : term568 = term569.
Proof. exact (MK_COMB (@lem2419983) (@lem2419978)). Qed.
Lemma lem2419985 : term569 = term570.
Proof. exact (@lem1981613 term546 term192 term192 term192). Qed.
Lemma lem2419987 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2419988 : term555 = term556.
Proof. exact (@lem2419987 term193 term193). Qed.
Lemma lem2419989 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419990 : term558 = term193.
Proof. exact (EQ_MP (@lem2419989) (@lem940073)). Qed.
Lemma lem2419991 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2419992 : term556 = term192.
Proof. exact (MK_COMB (@lem2419991) (@lem2419990)). Qed.
Lemma lem2419993 : term555 = term192.
Proof. exact (TRANS (@lem2419988) (@lem2419992)). Qed.
Lemma lem2419995 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2419996 : term568 = term573.
Proof. exact (@lem2419995 term193 term193). Qed.
Lemma lem2419997 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2419998 : term558 = term193.
Proof. exact (EQ_MP (@lem2419997) (@lem940073)). Qed.
Lemma lem2419999 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420000 : term556 = term192.
Proof. exact (MK_COMB (@lem2419999) (@lem2419998)). Qed.
Lemma lem2420001 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2420002 : term573 = term546.
Proof. exact (MK_COMB (@lem2420001) (@lem2420000)). Qed.
Lemma lem2420003 : term568 = term546.
Proof. exact (TRANS (@lem2419996) (@lem2420002)). Qed.
Lemma lem2420004 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2420005 : term574 = term575.
Proof. exact (MK_COMB (@lem2420004) (@lem2420003)). Qed.
Lemma lem2420006 : term570 = term547.
Proof. exact (MK_COMB (@lem2420005) (@lem2419993)). Qed.
Lemma lem2420007 : term569 = term547.
Proof. exact (TRANS (@lem2419985) (@lem2420006)). Qed.
Lemma lem2420008 : term568 = term547.
Proof. exact (TRANS (@lem2419984) (@lem2420007)). Qed.
Lemma lem2420010 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2420011 : term547 = term546.
Proof. exact (@lem2420010 term546). Qed.
Lemma lem2420012 : term568 = term546.
Proof. exact (TRANS (@lem2420008) (@lem2420011)). Qed.
Lemma lem2420013 (z : int) : (term641 z) = (term642 z).
Proof. exact (@lem1982749 term546 term546 (real_of_int z)). Qed.
Lemma lem2420015 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420016 : term546 = term547.
Proof. exact (@lem2420015 term193). Qed.
Lemma lem2420018 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420019 : term546 = term547.
Proof. exact (@lem2420018 term193). Qed.
Lemma lem2420020 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420021 : term548 = term549.
Proof. exact (MK_COMB (@lem2420020) (@lem2420019)). Qed.
Lemma lem2420022 : term643 = term644.
Proof. exact (MK_COMB (@lem2420021) (@lem2420016)). Qed.
Lemma lem2420023 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2420025 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2420026 : term555 = term556.
Proof. exact (@lem2420025 term193 term193). Qed.
Lemma lem2420027 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420028 : term558 = term193.
Proof. exact (EQ_MP (@lem2420027) (@lem940073)). Qed.
Lemma lem2420029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420030 : term556 = term192.
Proof. exact (MK_COMB (@lem2420029) (@lem2420028)). Qed.
Lemma lem2420031 : term555 = term192.
Proof. exact (TRANS (@lem2420026) (@lem2420030)). Qed.
Lemma lem2420033 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2420034 : term643 = term556.
Proof. exact (@lem2420033 term193 term193). Qed.
Lemma lem2420035 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420036 : term558 = term193.
Proof. exact (EQ_MP (@lem2420035) (@lem940073)). Qed.
Lemma lem2420037 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420038 : term556 = term192.
Proof. exact (MK_COMB (@lem2420037) (@lem2420036)). Qed.
Lemma lem2420039 : term643 = term192.
Proof. exact (TRANS (@lem2420034) (@lem2420038)). Qed.
Lemma lem2420040 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2420041 : term647 = term648.
Proof. exact (MK_COMB (@lem2420040) (@lem2420039)). Qed.
Lemma lem2420042 : term645 = term567.
Proof. exact (MK_COMB (@lem2420041) (@lem2420031)). Qed.
Lemma lem2420043 : term644 = term567.
Proof. exact (TRANS (@lem2420023) (@lem2420042)). Qed.
Lemma lem2420044 : term643 = term567.
Proof. exact (TRANS (@lem2420022) (@lem2420043)). Qed.
Lemma lem2420046 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2420047 : term567 = term192.
Proof. exact (@lem2420046 term192). Qed.
Lemma lem2420048 : term643 = term192.
Proof. exact (TRANS (@lem2420044) (@lem2420047)). Qed.
Lemma lem2420049 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420050 : term649 = term650.
Proof. exact (MK_COMB (@lem2420049) (@lem2420048)). Qed.
Lemma lem2420051 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2420052 (z : int) : (term642 z) = (term651 z).
Proof. exact (MK_COMB (@lem2420050) (@lem2420051 z)). Qed.
Lemma lem2420053 (z : int) : (term641 z) = (term651 z).
Proof. exact (TRANS (@lem2420013 z) (@lem2420052 z)). Qed.
Lemma lem2420054 (z : int) : (term651 z) = (real_of_int z).
Proof. exact (@lem1982709 (real_of_int z)). Qed.
Lemma lem2420055 (z : int) : (term641 z) = (real_of_int z).
Proof. exact (TRANS (@lem2420053 z) (@lem2420054 z)). Qed.
Lemma lem2420056 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2420057 (z : int) : (term652 z) = (term653 z).
Proof. exact (MK_COMB (@lem2420056) (@lem2420055 z)). Qed.
Lemma lem2420058 (z : int) : (term640 z) = (term654 z).
Proof. exact (MK_COMB (@lem2420057 z) (@lem2420012)). Qed.
Lemma lem2420059 (z : int) : (term639 z) = (term654 z).
Proof. exact (TRANS (@lem2419975 z) (@lem2420058 z)). Qed.
Lemma lem2420062 (y : int) : (term655 y) = (term655 y).
Proof. exact (eq_refl (term655 y)). Qed.
Lemma lem2420063 (y : int) (z : int) : (term637 y z) = (term656 y z).
Proof. exact (MK_COMB (@lem2420062 y) (@lem2420059 z)). Qed.
Lemma lem2420064 (y : int) (z : int) : (term636 y z) = (term656 y z).
Proof. exact (TRANS (@lem2419974 y z) (@lem2420063 y z)). Qed.
Lemma lem2420065 : term206 = term206.
Proof. exact (eq_refl term206). Qed.
Lemma lem2420066 (y : int) (z : int) : (term635 y z) = (term657 y z).
Proof. exact (MK_COMB (@lem2420065) (@lem2420064 y z)). Qed.
Lemma lem2420067 (y : int) (z : int) : (term657 y z) = (term656 y z).
Proof. exact (@lem1982721 (term656 y z)). Qed.
Lemma lem2420068 (y : int) (z : int) : (term635 y z) = (term656 y z).
Proof. exact (TRANS (@lem2420066 y z) (@lem2420067 y z)). Qed.
Lemma lem2420069 (y : int) (z : int) : (term634 y z) = (term656 y z).
Proof. exact (TRANS (@lem2419973 y z) (@lem2420068 y z)). Qed.
Lemma lem2420070 (x : int) (y : int) (z : int) : (term682 y x z) = (term656 y z).
Proof. exact (TRANS (@lem2419972 x y z) (@lem2420069 y z)). Qed.
Lemma lem2420071 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2420072 (x : int) (y : int) (z : int) : (term683 y x z) = (term659 y z).
Proof. exact (MK_COMB (@lem2420071) (@lem2420070 x y z)). Qed.
Lemma lem2420073 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2420074 (x : int) (y : int) (z : int) : (term681 y x z) = (term660 y z).
Proof. exact (MK_COMB (@lem2420072 x y z) (@lem2420073)). Qed.
Lemma lem2420075 (x : int) (y : int) (z : int) : (term256 y x z) = (term660 y z).
Proof. exact (TRANS (@lem2419814 y x z) (@lem2420074 x y z)). Qed.
Lemma lem2420076 (y : int) (x : int) (z : int) : (term261 y x z) = (term684 y x z).
Proof. exact (@lem1988287 (term218 y x z) term207). Qed.
Lemma lem2420083 : term207 = term192.
Proof. exact (@lem1982721 term192). Qed.
Lemma lem2420101 (y : int) (x : int) (z : int) : (term218 y x z) = (term589 y x z).
Proof. exact (@lem1982792 (term168 x y) (term168 x z)). Qed.
Lemma lem2420108 (x : int) (z : int) : (term590 x z) = (term591 x z).
Proof. exact (@lem1982781 (real_of_int x) term546 (real_of_int z)). Qed.
Lemma lem2420109 (x : int) (y : int) : (term592 x y) = (term592 x y).
Proof. exact (eq_refl (term592 x y)). Qed.
Lemma lem2420110 (y : int) (x : int) (z : int) : (term589 y x z) = (term593 y x z).
Proof. exact (MK_COMB (@lem2420109 x y) (@lem2420108 x z)). Qed.
Lemma lem2420111 (x : int) (y : int) (z : int) : (term593 y x z) = (term594 x y z).
Proof. exact (@lem1982753 (real_of_int x) (term595 x) (real_of_int y) (term595 z)). Qed.
Lemma lem2420112 (x : int) : (term596 x) = (term597 x).
Proof. exact (@lem1982715 term546 (real_of_int x)). Qed.
Lemma lem2420114 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2420115 : term192 = term567.
Proof. exact (@lem2420114 term193). Qed.
Lemma lem2420117 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420118 : term546 = term547.
Proof. exact (@lem2420117 term193). Qed.
Lemma lem2420119 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2420120 : term598 = term599.
Proof. exact (MK_COMB (@lem2420119) (@lem2420118)). Qed.
Lemma lem2420121 : term600 = term601.
Proof. exact (MK_COMB (@lem2420120) (@lem2420115)). Qed.
Lemma lem2420122 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2420124 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2420125 : term604 = term605.
Proof. exact (@lem2420124 (NUMERAL 0) term193). Qed.
Lemma lem2420126 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2420127 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2420128 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2420127 h1) (fun h1 : term605 = True => @lem2420126)). Qed.
Lemma lem2420129 : term605 = True.
Proof. exact (EQ_MP (@lem2420128) (@lem2420126)). Qed.
Lemma lem2420130 : term604 = True.
Proof. exact (TRANS (@lem2420125) (@lem2420129)). Qed.
Lemma lem2420131 : True = term604.
Proof. exact (SYM (@lem2420130)). Qed.
Lemma lem2420132 : term604.
Proof. exact (EQ_MP (@lem2420131) (@lem0)). Qed.
Lemma lem2420133 : term607.
Proof. exact (@lem2420122 (@lem2420132)). Qed.
Lemma lem2420135 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2420136 : term604 = term605.
Proof. exact (@lem2420135 (NUMERAL 0) term193). Qed.
Lemma lem2420137 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2420138 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2420139 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2420138 h1) (fun h1 : term605 = True => @lem2420137)). Qed.
Lemma lem2420140 : term605 = True.
Proof. exact (EQ_MP (@lem2420139) (@lem2420137)). Qed.
Lemma lem2420141 : term604 = True.
Proof. exact (TRANS (@lem2420136) (@lem2420140)). Qed.
Lemma lem2420142 : True = term604.
Proof. exact (SYM (@lem2420141)). Qed.
Lemma lem2420143 : term604.
Proof. exact (EQ_MP (@lem2420142) (@lem0)). Qed.
Lemma lem2420144 : term608.
Proof. exact (@lem2420133 (@lem2420143)). Qed.
Lemma lem2420146 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2420147 : term604 = term605.
Proof. exact (@lem2420146 (NUMERAL 0) term193). Qed.
Lemma lem2420148 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2420149 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2420150 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2420149 h1) (fun h1 : term605 = True => @lem2420148)). Qed.
Lemma lem2420151 : term605 = True.
Proof. exact (EQ_MP (@lem2420150) (@lem2420148)). Qed.
Lemma lem2420152 : term604 = True.
Proof. exact (TRANS (@lem2420147) (@lem2420151)). Qed.
Lemma lem2420153 : True = term604.
Proof. exact (SYM (@lem2420152)). Qed.
Lemma lem2420154 : term604.
Proof. exact (EQ_MP (@lem2420153) (@lem0)). Qed.
Lemma lem2420155 : term609.
Proof. exact (@lem2420144 (@lem2420154)). Qed.
Lemma lem2420157 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2420158 : term555 = term556.
Proof. exact (@lem2420157 term193 term193). Qed.
Lemma lem2420159 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420160 : term558 = term193.
Proof. exact (EQ_MP (@lem2420159) (@lem940073)). Qed.
Lemma lem2420161 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420162 : term556 = term192.
Proof. exact (MK_COMB (@lem2420161) (@lem2420160)). Qed.
Lemma lem2420163 : term555 = term192.
Proof. exact (TRANS (@lem2420158) (@lem2420162)). Qed.
Lemma lem2420165 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2420166 : term568 = term573.
Proof. exact (@lem2420165 term193 term193). Qed.
Lemma lem2420167 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420168 : term558 = term193.
Proof. exact (EQ_MP (@lem2420167) (@lem940073)). Qed.
Lemma lem2420169 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420170 : term556 = term192.
Proof. exact (MK_COMB (@lem2420169) (@lem2420168)). Qed.
Lemma lem2420171 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2420172 : term573 = term546.
Proof. exact (MK_COMB (@lem2420171) (@lem2420170)). Qed.
Lemma lem2420173 : term568 = term546.
Proof. exact (TRANS (@lem2420166) (@lem2420172)). Qed.
Lemma lem2420174 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2420175 : term610 = term598.
Proof. exact (MK_COMB (@lem2420174) (@lem2420173)). Qed.
Lemma lem2420176 : term611 = term600.
Proof. exact (MK_COMB (@lem2420175) (@lem2420163)). Qed.
Lemma lem2420178 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2420179 : term600 = term182.
Proof. exact (@lem2420178 term193). Qed.
Lemma lem2420180 : term611 = term182.
Proof. exact (TRANS (@lem2420176) (@lem2420179)). Qed.
Lemma lem2420181 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420182 : term613 = term184.
Proof. exact (MK_COMB (@lem2420181) (@lem2420180)). Qed.
Lemma lem2420183 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2420184 : term614 = term615.
Proof. exact (MK_COMB (@lem2420182) (@lem2420183)). Qed.
Lemma lem2420186 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2420187 : term615 = term182.
Proof. exact (@lem2420186 term193). Qed.
Lemma lem2420188 : term614 = term182.
Proof. exact (TRANS (@lem2420184) (@lem2420187)). Qed.
Lemma lem2420190 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2420191 : term555 = term556.
Proof. exact (@lem2420190 term193 term193). Qed.
Lemma lem2420192 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420193 : term558 = term193.
Proof. exact (EQ_MP (@lem2420192) (@lem940073)). Qed.
Lemma lem2420194 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420195 : term556 = term192.
Proof. exact (MK_COMB (@lem2420194) (@lem2420193)). Qed.
Lemma lem2420196 : term555 = term192.
Proof. exact (TRANS (@lem2420191) (@lem2420195)). Qed.
Lemma lem2420197 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2420198 : term617 = term615.
Proof. exact (MK_COMB (@lem2420197) (@lem2420196)). Qed.
Lemma lem2420200 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2420201 : term615 = term182.
Proof. exact (@lem2420200 term193). Qed.
Lemma lem2420202 : term617 = term182.
Proof. exact (TRANS (@lem2420198) (@lem2420201)). Qed.
Lemma lem2420203 : term182 = term617.
Proof. exact (SYM (@lem2420202)). Qed.
Lemma lem2420204 : term614 = term617.
Proof. exact (TRANS (@lem2420188) (@lem2420203)). Qed.
Lemma lem2420205 : term601 = term543.
Proof. exact (@lem2420155 (@lem2420204)). Qed.
Lemma lem2420206 : term600 = term543.
Proof. exact (TRANS (@lem2420121) (@lem2420205)). Qed.
Lemma lem2420208 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2420209 : term543 = term182.
Proof. exact (@lem2420208 term182). Qed.
Lemma lem2420210 : term600 = term182.
Proof. exact (TRANS (@lem2420206) (@lem2420209)). Qed.
Lemma lem2420211 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420212 : term618 = term184.
Proof. exact (MK_COMB (@lem2420211) (@lem2420210)). Qed.
Lemma lem2420213 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2420214 (x : int) : (term597 x) = (term185 x).
Proof. exact (MK_COMB (@lem2420212) (@lem2420213 x)). Qed.
Lemma lem2420215 (x : int) : (term596 x) = (term185 x).
Proof. exact (TRANS (@lem2420112 x) (@lem2420214 x)). Qed.
Lemma lem2420216 (x : int) : (term185 x) = term182.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2420217 (x : int) : (term596 x) = term182.
Proof. exact (TRANS (@lem2420215 x) (@lem2420216 x)). Qed.
Lemma lem2420218 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2420219 (x : int) : (term619 x) = term206.
Proof. exact (MK_COMB (@lem2420218) (@lem2420217 x)). Qed.
Lemma lem2420220 (y : int) (z : int) : (term620 y z) = (term620 y z).
Proof. exact (eq_refl (term620 y z)). Qed.
Lemma lem2420221 (x : int) (y : int) (z : int) : (term594 x y z) = (term621 y z).
Proof. exact (MK_COMB (@lem2420219 x) (@lem2420220 y z)). Qed.
Lemma lem2420222 (x : int) (y : int) (z : int) : (term593 y x z) = (term621 y z).
Proof. exact (TRANS (@lem2420111 x y z) (@lem2420221 x y z)). Qed.
Lemma lem2420223 (y : int) (z : int) : (term621 y z) = (term620 y z).
Proof. exact (@lem1982721 (term620 y z)). Qed.
Lemma lem2420224 (x : int) (y : int) (z : int) : (term593 y x z) = (term620 y z).
Proof. exact (TRANS (@lem2420222 x y z) (@lem2420223 y z)). Qed.
Lemma lem2420225 (x : int) (y : int) (z : int) : (term589 y x z) = (term620 y z).
Proof. exact (TRANS (@lem2420110 y x z) (@lem2420224 x y z)). Qed.
Lemma lem2420227 (x : int) (y : int) (z : int) : (term218 y x z) = (term620 y z).
Proof. exact (TRANS (@lem2420101 y x z) (@lem2420225 x y z)). Qed.
Lemma lem2420228 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2420229 (x : int) (y : int) (z : int) : (term622 y x z) = (term623 y z).
Proof. exact (MK_COMB (@lem2420228) (@lem2420227 x y z)). Qed.
Lemma lem2420230 (x : int) (y : int) (z : int) : (term685 y x z) = (term664 y z).
Proof. exact (MK_COMB (@lem2420229 x y z) (@lem2420083)). Qed.
Lemma lem2420231 (y : int) (z : int) : (term664 y z) = (term665 y z).
Proof. exact (@lem1982792 (term620 y z) term192). Qed.
Lemma lem2420233 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2420234 : term192 = term567.
Proof. exact (@lem2420233 term193). Qed.
Lemma lem2420236 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420237 : term546 = term547.
Proof. exact (@lem2420236 term193). Qed.
Lemma lem2420238 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420239 : term548 = term549.
Proof. exact (MK_COMB (@lem2420238) (@lem2420237)). Qed.
Lemma lem2420240 : term568 = term569.
Proof. exact (MK_COMB (@lem2420239) (@lem2420234)). Qed.
Lemma lem2420241 : term569 = term570.
Proof. exact (@lem1981613 term546 term192 term192 term192). Qed.
Lemma lem2420243 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2420244 : term555 = term556.
Proof. exact (@lem2420243 term193 term193). Qed.
Lemma lem2420245 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420246 : term558 = term193.
Proof. exact (EQ_MP (@lem2420245) (@lem940073)). Qed.
Lemma lem2420247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420248 : term556 = term192.
Proof. exact (MK_COMB (@lem2420247) (@lem2420246)). Qed.
Lemma lem2420249 : term555 = term192.
Proof. exact (TRANS (@lem2420244) (@lem2420248)). Qed.
Lemma lem2420251 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2420252 : term568 = term573.
Proof. exact (@lem2420251 term193 term193). Qed.
Lemma lem2420253 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420254 : term558 = term193.
Proof. exact (EQ_MP (@lem2420253) (@lem940073)). Qed.
Lemma lem2420255 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420256 : term556 = term192.
Proof. exact (MK_COMB (@lem2420255) (@lem2420254)). Qed.
Lemma lem2420257 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2420258 : term573 = term546.
Proof. exact (MK_COMB (@lem2420257) (@lem2420256)). Qed.
Lemma lem2420259 : term568 = term546.
Proof. exact (TRANS (@lem2420252) (@lem2420258)). Qed.
Lemma lem2420260 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2420261 : term574 = term575.
Proof. exact (MK_COMB (@lem2420260) (@lem2420259)). Qed.
Lemma lem2420262 : term570 = term547.
Proof. exact (MK_COMB (@lem2420261) (@lem2420249)). Qed.
Lemma lem2420263 : term569 = term547.
Proof. exact (TRANS (@lem2420241) (@lem2420262)). Qed.
Lemma lem2420264 : term568 = term547.
Proof. exact (TRANS (@lem2420240) (@lem2420263)). Qed.
Lemma lem2420266 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2420267 : term547 = term546.
Proof. exact (@lem2420266 term546). Qed.
Lemma lem2420268 : term568 = term546.
Proof. exact (TRANS (@lem2420264) (@lem2420267)). Qed.
Lemma lem2420269 (y : int) (z : int) : (term626 y z) = (term626 y z).
Proof. exact (eq_refl (term626 y z)). Qed.
Lemma lem2420270 (y : int) (z : int) : (term665 y z) = (term666 y z).
Proof. exact (MK_COMB (@lem2420269 y z) (@lem2420268)). Qed.
Lemma lem2420275 (y : int) (z : int) : (term666 y z) = (term667 y z).
Proof. exact (@lem1982755 (real_of_int y) (term595 z) term546). Qed.
Lemma lem2420276 (y : int) (z : int) : (term665 y z) = (term667 y z).
Proof. exact (TRANS (@lem2420270 y z) (@lem2420275 y z)). Qed.
Lemma lem2420277 (y : int) (z : int) : (term664 y z) = (term667 y z).
Proof. exact (TRANS (@lem2420231 y z) (@lem2420276 y z)). Qed.
Lemma lem2420278 (x : int) (y : int) (z : int) : (term685 y x z) = (term667 y z).
Proof. exact (TRANS (@lem2420230 x y z) (@lem2420277 y z)). Qed.
Lemma lem2420279 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2420280 (x : int) (y : int) (z : int) : (term686 y x z) = (term669 y z).
Proof. exact (MK_COMB (@lem2420279) (@lem2420278 x y z)). Qed.
Lemma lem2420281 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2420282 (x : int) (y : int) (z : int) : (term684 y x z) = (term670 y z).
Proof. exact (MK_COMB (@lem2420280 x y z) (@lem2420281)). Qed.
Lemma lem2420283 (x : int) (y : int) (z : int) : (term261 y x z) = (term670 y z).
Proof. exact (TRANS (@lem2420076 y x z) (@lem2420282 x y z)). Qed.
Lemma lem2420284 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2420285 (x : int) (y : int) (z : int) : (term258 y x z) = (term671 y z).
Proof. exact (MK_COMB (@lem2420284) (@lem2420075 x y z)). Qed.
Lemma lem2420286 (x : int) (y : int) (z : int) : (term262 y x z) = (term672 y z).
Proof. exact (MK_COMB (@lem2420285 x y z) (@lem2420283 x y z)). Qed.
Lemma lem2420287 (y : int) (z : int) : ((term173 y z) = term182) = ((term687 y z) = term182).
Proof. exact (@lem1988293 (term173 y z) term182). Qed.
Lemma lem2420288 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2420301 (y : int) (z : int) : (term173 y z) = (term620 y z).
Proof. exact (@lem1982792 (real_of_int y) (real_of_int z)). Qed.
Lemma lem2420302 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2420303 (y : int) (z : int) : (term662 y z) = (term623 y z).
Proof. exact (MK_COMB (@lem2420302) (@lem2420301 y z)). Qed.
Lemma lem2420304 (y : int) (z : int) : (term687 y z) = (term624 y z).
Proof. exact (MK_COMB (@lem2420303 y z) (@lem2420288)). Qed.
Lemma lem2420305 (y : int) (z : int) : (term624 y z) = (term625 y z).
Proof. exact (@lem1982792 (term620 y z) term182). Qed.
Lemma lem2420307 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2420308 : term182 = term543.
Proof. exact (@lem2420307 (NUMERAL 0)). Qed.
Lemma lem2420310 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420311 : term546 = term547.
Proof. exact (@lem2420310 term193). Qed.
Lemma lem2420312 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420313 : term548 = term549.
Proof. exact (MK_COMB (@lem2420312) (@lem2420311)). Qed.
Lemma lem2420314 : term550 = term551.
Proof. exact (MK_COMB (@lem2420313) (@lem2420308)). Qed.
Lemma lem2420315 : term551 = term552.
Proof. exact (@lem1981613 term546 term182 term192 term192). Qed.
Lemma lem2420317 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2420318 : term555 = term556.
Proof. exact (@lem2420317 term193 term193). Qed.
Lemma lem2420319 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420320 : term558 = term193.
Proof. exact (EQ_MP (@lem2420319) (@lem940073)). Qed.
Lemma lem2420321 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420322 : term556 = term192.
Proof. exact (MK_COMB (@lem2420321) (@lem2420320)). Qed.
Lemma lem2420323 : term555 = term192.
Proof. exact (TRANS (@lem2420318) (@lem2420322)). Qed.
Lemma lem2420325 (x : nat) : (term559 x) = term182.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2420326 : term550 = term182.
Proof. exact (@lem2420325 term193). Qed.
Lemma lem2420327 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2420328 : term560 = term561.
Proof. exact (MK_COMB (@lem2420327) (@lem2420326)). Qed.
Lemma lem2420329 : term552 = term543.
Proof. exact (MK_COMB (@lem2420328) (@lem2420323)). Qed.
Lemma lem2420330 : term551 = term543.
Proof. exact (TRANS (@lem2420315) (@lem2420329)). Qed.
Lemma lem2420331 : term550 = term543.
Proof. exact (TRANS (@lem2420314) (@lem2420330)). Qed.
Lemma lem2420333 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2420334 : term543 = term182.
Proof. exact (@lem2420333 term182). Qed.
Lemma lem2420335 : term550 = term182.
Proof. exact (TRANS (@lem2420331) (@lem2420334)). Qed.
Lemma lem2420336 (y : int) (z : int) : (term626 y z) = (term626 y z).
Proof. exact (eq_refl (term626 y z)). Qed.
Lemma lem2420337 (y : int) (z : int) : (term625 y z) = (term627 y z).
Proof. exact (MK_COMB (@lem2420336 y z) (@lem2420335)). Qed.
Lemma lem2420338 (y : int) (z : int) : (term627 y z) = (term620 y z).
Proof. exact (@lem1982723 (term620 y z)). Qed.
Lemma lem2420339 (y : int) (z : int) : (term625 y z) = (term620 y z).
Proof. exact (TRANS (@lem2420337 y z) (@lem2420338 y z)). Qed.
Lemma lem2420340 (y : int) (z : int) : (term624 y z) = (term620 y z).
Proof. exact (TRANS (@lem2420305 y z) (@lem2420339 y z)). Qed.
Lemma lem2420341 (y : int) (z : int) : (term687 y z) = (term620 y z).
Proof. exact (TRANS (@lem2420304 y z) (@lem2420340 y z)). Qed.
Lemma lem2420342 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2420343 (y : int) (z : int) : (term688 y z) = (term629 y z).
Proof. exact (MK_COMB (@lem2420342) (@lem2420341 y z)). Qed.
Lemma lem2420344 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2420345 (y : int) (z : int) : ((term687 y z) = term182) = ((term620 y z) = term182).
Proof. exact (MK_COMB (@lem2420343 y z) (@lem2420344)). Qed.
Lemma lem2420346 (y : int) (z : int) : ((term173 y z) = term182) = ((term620 y z) = term182).
Proof. exact (TRANS (@lem2420287 y z) (@lem2420345 y z)). Qed.
Lemma lem2420347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2420348 (x : int) (y : int) (z : int) : (term266 y x z) = (term689 y z).
Proof. exact (MK_COMB (@lem2420347) (@lem2420286 x y z)). Qed.
Lemma lem2420349 (x : int) (y : int) (z : int) : (term268 x y z) = (term690 y z).
Proof. exact (MK_COMB (@lem2420348 x y z) (@lem2420346 y z)). Qed.
Lemma lem2420350 (x : int) (y : int) : (term388 x y) = (term691 y).
Proof. exact (fun_ext (fun z : int => @lem2420349 x y z)). Qed.
Lemma lem2420351 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2420352 (x : int) (y : int) : (term403 x y) = (term692 y).
Proof. exact (MK_COMB (@lem2420351) (@lem2420350 x y)). Qed.
Lemma lem2420353 (x : int) : (term410 x) = term693.
Proof. exact (fun_ext (fun y : int => @lem2420352 x y)). Qed.
Lemma lem2420354 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2420355 (x : int) : (term425 x) = term694.
Proof. exact (MK_COMB (@lem2420354) (@lem2420353 x)). Qed.
Lemma lem2420356 : term432 = term695.
Proof. exact (fun_ext (fun x : int => @lem2420355 x)). Qed.
Lemma lem2420357 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2420358 : term447 = term696.
Proof. exact (MK_COMB (@lem2420357) (@lem2420356)). Qed.
Lemma lem2420359 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2420360 : term444 = term697.
Proof. exact (MK_COMB (@lem2420359) (@lem2419813)). Qed.
Lemma lem2420361 : term448 = term698.
Proof. exact (MK_COMB (@lem2420360) (@lem2420358)). Qed.
Lemma lem2420362 (w : int) (z : int) (x : int) (y : int) : ((term287 w z x y) = term182) = ((term699 w z x y) = term182).
Proof. exact (@lem1988293 (term287 w z x y) term182). Qed.
Lemma lem2420363 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2420405 (w : int) (z : int) (x : int) (y : int) : (term287 w z x y) = (term700 w z x y).
Proof. exact (@lem1982792 (term284 w y x z) (term284 w z x y)). Qed.
Lemma lem2420412 (w : int) (z : int) (x : int) (y : int) : (term701 w z x y) = (term702 w z x y).
Proof. exact (@lem1982781 (term177 w z) term546 (term177 x y)). Qed.
Lemma lem2420413 (w : int) (y : int) (x : int) (z : int) : (term703 w y x z) = (term703 w y x z).
Proof. exact (eq_refl (term703 w y x z)). Qed.
Lemma lem2420414 (w : int) (z : int) (x : int) (y : int) : (term700 w z x y) = (term704 w z x y).
Proof. exact (MK_COMB (@lem2420413 w y x z) (@lem2420412 w z x y)). Qed.
Lemma lem2420415 (w : int) (z : int) (x : int) (y : int) : (term704 w z x y) = (term705 w z x y).
Proof. exact (@lem1982755 (term177 w y) (term177 x z) (term702 w z x y)). Qed.
Lemma lem2420416 (w : int) (z : int) (x : int) (y : int) : (term706 w z x y) = (term707 w z x y).
Proof. exact (@lem1982757 (term708 w z) (term177 x z) (term708 x y)). Qed.
Lemma lem2420417 (y : int) (x : int) (z : int) : (term709 z x y) = (term710 y x z).
Proof. exact (@lem1982761 (term708 x y) (term177 x z)). Qed.
Lemma lem2420418 (w : int) (z : int) : (term711 w z) = (term711 w z).
Proof. exact (eq_refl (term711 w z)). Qed.
Lemma lem2420419 (w : int) (y : int) (x : int) (z : int) : (term707 w z x y) = (term712 w y x z).
Proof. exact (MK_COMB (@lem2420418 w z) (@lem2420417 y x z)). Qed.
Lemma lem2420420 (w : int) (y : int) (x : int) (z : int) : (term706 w z x y) = (term712 w y x z).
Proof. exact (TRANS (@lem2420416 w z x y) (@lem2420419 w y x z)). Qed.
Lemma lem2420421 (w : int) (y : int) : (term283 w y) = (term283 w y).
Proof. exact (eq_refl (term283 w y)). Qed.
Lemma lem2420422 (w : int) (y : int) (x : int) (z : int) : (term705 w z x y) = (term713 w y x z).
Proof. exact (MK_COMB (@lem2420421 w y) (@lem2420420 w y x z)). Qed.
Lemma lem2420423 (w : int) (y : int) (x : int) (z : int) : (term704 w z x y) = (term713 w y x z).
Proof. exact (TRANS (@lem2420415 w z x y) (@lem2420422 w y x z)). Qed.
Lemma lem2420424 (w : int) (y : int) (x : int) (z : int) : (term700 w z x y) = (term713 w y x z).
Proof. exact (TRANS (@lem2420414 w z x y) (@lem2420423 w y x z)). Qed.
Lemma lem2420426 (w : int) (y : int) (x : int) (z : int) : (term287 w z x y) = (term713 w y x z).
Proof. exact (TRANS (@lem2420405 w z x y) (@lem2420424 w y x z)). Qed.
Lemma lem2420427 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2420428 (w : int) (y : int) (x : int) (z : int) : (term714 w z x y) = (term715 w y x z).
Proof. exact (MK_COMB (@lem2420427) (@lem2420426 w y x z)). Qed.
Lemma lem2420429 (w : int) (y : int) (x : int) (z : int) : (term699 w z x y) = (term716 w y x z).
Proof. exact (MK_COMB (@lem2420428 w y x z) (@lem2420363)). Qed.
Lemma lem2420430 (w : int) (y : int) (x : int) (z : int) : (term716 w y x z) = (term717 w y x z).
Proof. exact (@lem1982792 (term713 w y x z) term182). Qed.
Lemma lem2420432 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2420433 : term182 = term543.
Proof. exact (@lem2420432 (NUMERAL 0)). Qed.
Lemma lem2420435 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420436 : term546 = term547.
Proof. exact (@lem2420435 term193). Qed.
Lemma lem2420437 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420438 : term548 = term549.
Proof. exact (MK_COMB (@lem2420437) (@lem2420436)). Qed.
Lemma lem2420439 : term550 = term551.
Proof. exact (MK_COMB (@lem2420438) (@lem2420433)). Qed.
Lemma lem2420440 : term551 = term552.
Proof. exact (@lem1981613 term546 term182 term192 term192). Qed.
Lemma lem2420442 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2420443 : term555 = term556.
Proof. exact (@lem2420442 term193 term193). Qed.
Lemma lem2420444 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420445 : term558 = term193.
Proof. exact (EQ_MP (@lem2420444) (@lem940073)). Qed.
Lemma lem2420446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420447 : term556 = term192.
Proof. exact (MK_COMB (@lem2420446) (@lem2420445)). Qed.
Lemma lem2420448 : term555 = term192.
Proof. exact (TRANS (@lem2420443) (@lem2420447)). Qed.
Lemma lem2420450 (x : nat) : (term559 x) = term182.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2420451 : term550 = term182.
Proof. exact (@lem2420450 term193). Qed.
Lemma lem2420452 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2420453 : term560 = term561.
Proof. exact (MK_COMB (@lem2420452) (@lem2420451)). Qed.
Lemma lem2420454 : term552 = term543.
Proof. exact (MK_COMB (@lem2420453) (@lem2420448)). Qed.
Lemma lem2420455 : term551 = term543.
Proof. exact (TRANS (@lem2420440) (@lem2420454)). Qed.
Lemma lem2420456 : term550 = term543.
Proof. exact (TRANS (@lem2420439) (@lem2420455)). Qed.
Lemma lem2420458 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2420459 : term543 = term182.
Proof. exact (@lem2420458 term182). Qed.
Lemma lem2420460 : term550 = term182.
Proof. exact (TRANS (@lem2420456) (@lem2420459)). Qed.
Lemma lem2420461 (w : int) (y : int) (x : int) (z : int) : (term718 w y x z) = (term718 w y x z).
Proof. exact (eq_refl (term718 w y x z)). Qed.
Lemma lem2420462 (w : int) (y : int) (x : int) (z : int) : (term717 w y x z) = (term719 w y x z).
Proof. exact (MK_COMB (@lem2420461 w y x z) (@lem2420460)). Qed.
Lemma lem2420463 (w : int) (y : int) (x : int) (z : int) : (term719 w y x z) = (term713 w y x z).
Proof. exact (@lem1982723 (term713 w y x z)). Qed.
Lemma lem2420464 (w : int) (y : int) (x : int) (z : int) : (term717 w y x z) = (term713 w y x z).
Proof. exact (TRANS (@lem2420462 w y x z) (@lem2420463 w y x z)). Qed.
Lemma lem2420465 (w : int) (y : int) (x : int) (z : int) : (term716 w y x z) = (term713 w y x z).
Proof. exact (TRANS (@lem2420430 w y x z) (@lem2420464 w y x z)). Qed.
Lemma lem2420466 (w : int) (y : int) (x : int) (z : int) : (term699 w z x y) = (term713 w y x z).
Proof. exact (TRANS (@lem2420429 w y x z) (@lem2420465 w y x z)). Qed.
Lemma lem2420467 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2420468 (w : int) (y : int) (x : int) (z : int) : (term720 w z x y) = (term721 w y x z).
Proof. exact (MK_COMB (@lem2420467) (@lem2420466 w y x z)). Qed.
Lemma lem2420469 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2420470 (w : int) (y : int) (x : int) (z : int) : ((term699 w z x y) = term182) = ((term713 w y x z) = term182).
Proof. exact (MK_COMB (@lem2420468 w y x z) (@lem2420469)). Qed.
Lemma lem2420471 (w : int) (y : int) (x : int) (z : int) : ((term287 w z x y) = term182) = ((term713 w y x z) = term182).
Proof. exact (TRANS (@lem2420362 w z x y) (@lem2420470 w y x z)). Qed.
Lemma lem2420472 (w : int) (x : int) (y : int) (z : int) : (term307 w x y z) = (term722 w x y z).
Proof. exact (@lem1988287 term182 (term304 w x y z)). Qed.
Lemma lem2420473 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2420486 (y : int) (z : int) : (term173 y z) = (term620 y z).
Proof. exact (@lem1982792 (real_of_int y) (real_of_int z)). Qed.
Lemma lem2420499 (w : int) (x : int) : (term173 w x) = (term620 w x).
Proof. exact (@lem1982792 (real_of_int w) (real_of_int x)). Qed.
Lemma lem2420500 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420501 (w : int) (x : int) : (term300 w x) = (term723 w x).
Proof. exact (MK_COMB (@lem2420500) (@lem2420499 w x)). Qed.
Lemma lem2420502 (w : int) (x : int) (y : int) (z : int) : (term301 w x y z) = (term724 w x y z).
Proof. exact (MK_COMB (@lem2420501 w x) (@lem2420486 y z)). Qed.
Lemma lem2420503 (w : int) (x : int) (y : int) (z : int) : (term724 w x y z) = (term725 w x y z).
Proof. exact (@lem1982727 (real_of_int w) (term595 x) (term620 y z)). Qed.
Lemma lem2420504 (y : int) (w : int) (z : int) : (term726 w y z) = (term727 y w z).
Proof. exact (@lem1982781 (real_of_int y) (real_of_int w) (term595 z)). Qed.
Lemma lem2420509 (w : int) (z : int) : (term728 w z) = (term708 w z).
Proof. exact (@lem1982751 term546 (real_of_int w) (real_of_int z)). Qed.
Lemma lem2420512 (w : int) (y : int) : (term283 w y) = (term283 w y).
Proof. exact (eq_refl (term283 w y)). Qed.
Lemma lem2420513 (y : int) (w : int) (z : int) : (term727 y w z) = (term709 y w z).
Proof. exact (MK_COMB (@lem2420512 w y) (@lem2420509 w z)). Qed.
Lemma lem2420514 (y : int) (w : int) (z : int) : (term726 w y z) = (term709 y w z).
Proof. exact (TRANS (@lem2420504 y w z) (@lem2420513 y w z)). Qed.
Lemma lem2420515 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2420516 (y : int) (w : int) (z : int) : (term729 w y z) = (term730 y w z).
Proof. exact (MK_COMB (@lem2420515) (@lem2420514 y w z)). Qed.
Lemma lem2420517 (y : int) (x : int) (z : int) : (term731 x y z) = (term732 y x z).
Proof. exact (@lem1982781 (real_of_int y) (term595 x) (term595 z)). Qed.
Lemma lem2420518 (x : int) (z : int) : (term733 x z) = (term734 x z).
Proof. exact (@lem1982737 term546 term546 (real_of_int x) (real_of_int z)). Qed.
Lemma lem2420520 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420521 : term546 = term547.
Proof. exact (@lem2420520 term193). Qed.
Lemma lem2420523 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420524 : term546 = term547.
Proof. exact (@lem2420523 term193). Qed.
Lemma lem2420525 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420526 : term548 = term549.
Proof. exact (MK_COMB (@lem2420525) (@lem2420524)). Qed.
Lemma lem2420527 : term643 = term644.
Proof. exact (MK_COMB (@lem2420526) (@lem2420521)). Qed.
Lemma lem2420528 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2420530 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2420531 : term555 = term556.
Proof. exact (@lem2420530 term193 term193). Qed.
Lemma lem2420532 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420533 : term558 = term193.
Proof. exact (EQ_MP (@lem2420532) (@lem940073)). Qed.
Lemma lem2420534 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420535 : term556 = term192.
Proof. exact (MK_COMB (@lem2420534) (@lem2420533)). Qed.
Lemma lem2420536 : term555 = term192.
Proof. exact (TRANS (@lem2420531) (@lem2420535)). Qed.
Lemma lem2420538 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2420539 : term643 = term556.
Proof. exact (@lem2420538 term193 term193). Qed.
Lemma lem2420540 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420541 : term558 = term193.
Proof. exact (EQ_MP (@lem2420540) (@lem940073)). Qed.
Lemma lem2420542 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420543 : term556 = term192.
Proof. exact (MK_COMB (@lem2420542) (@lem2420541)). Qed.
Lemma lem2420544 : term643 = term192.
Proof. exact (TRANS (@lem2420539) (@lem2420543)). Qed.
Lemma lem2420545 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2420546 : term647 = term648.
Proof. exact (MK_COMB (@lem2420545) (@lem2420544)). Qed.
Lemma lem2420547 : term645 = term567.
Proof. exact (MK_COMB (@lem2420546) (@lem2420536)). Qed.
Lemma lem2420548 : term644 = term567.
Proof. exact (TRANS (@lem2420528) (@lem2420547)). Qed.
Lemma lem2420549 : term643 = term567.
Proof. exact (TRANS (@lem2420527) (@lem2420548)). Qed.
Lemma lem2420551 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2420552 : term567 = term192.
Proof. exact (@lem2420551 term192). Qed.
Lemma lem2420553 : term643 = term192.
Proof. exact (TRANS (@lem2420549) (@lem2420552)). Qed.
Lemma lem2420554 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420555 : term649 = term650.
Proof. exact (MK_COMB (@lem2420554) (@lem2420553)). Qed.
Lemma lem2420556 (x : int) (z : int) : (term177 x z) = (term177 x z).
Proof. exact (eq_refl (term177 x z)). Qed.
Lemma lem2420557 (x : int) (z : int) : (term734 x z) = (term735 x z).
Proof. exact (MK_COMB (@lem2420555) (@lem2420556 x z)). Qed.
Lemma lem2420562 (x : int) (z : int) : (term733 x z) = (term735 x z).
Proof. exact (TRANS (@lem2420518 x z) (@lem2420557 x z)). Qed.
Lemma lem2420563 (x : int) (z : int) : (term735 x z) = (term177 x z).
Proof. exact (@lem1982709 (term177 x z)). Qed.
Lemma lem2420564 (x : int) (z : int) : (term733 x z) = (term177 x z).
Proof. exact (TRANS (@lem2420562 x z) (@lem2420563 x z)). Qed.
Lemma lem2420569 (x : int) (y : int) : (term736 x y) = (term708 x y).
Proof. exact (@lem1982745 term546 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2420570 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2420571 (x : int) (y : int) : (term737 x y) = (term711 x y).
Proof. exact (MK_COMB (@lem2420570) (@lem2420569 x y)). Qed.
Lemma lem2420572 (y : int) (x : int) (z : int) : (term732 y x z) = (term710 y x z).
Proof. exact (MK_COMB (@lem2420571 x y) (@lem2420564 x z)). Qed.
Lemma lem2420573 (y : int) (x : int) (z : int) : (term731 x y z) = (term710 y x z).
Proof. exact (TRANS (@lem2420517 y x z) (@lem2420572 y x z)). Qed.
Lemma lem2420574 (w : int) (y : int) (x : int) (z : int) : (term725 w x y z) = (term738 w y x z).
Proof. exact (MK_COMB (@lem2420516 y w z) (@lem2420573 y x z)). Qed.
Lemma lem2420575 (w : int) (y : int) (x : int) (z : int) : (term724 w x y z) = (term738 w y x z).
Proof. exact (TRANS (@lem2420503 w x y z) (@lem2420574 w y x z)). Qed.
Lemma lem2420580 (w : int) (y : int) (x : int) (z : int) : (term738 w y x z) = (term713 w y x z).
Proof. exact (@lem1982755 (term177 w y) (term708 w z) (term710 y x z)). Qed.
Lemma lem2420581 (w : int) (y : int) (x : int) (z : int) : (term724 w x y z) = (term713 w y x z).
Proof. exact (TRANS (@lem2420575 w y x z) (@lem2420580 w y x z)). Qed.
Lemma lem2420582 (w : int) (y : int) (x : int) (z : int) : (term301 w x y z) = (term713 w y x z).
Proof. exact (TRANS (@lem2420502 w x y z) (@lem2420581 w y x z)). Qed.
Lemma lem2420583 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2420584 (w : int) (y : int) (x : int) (z : int) : (term303 w x y z) = (term718 w y x z).
Proof. exact (MK_COMB (@lem2420583) (@lem2420582 w y x z)). Qed.
Lemma lem2420585 (w : int) (y : int) (x : int) (z : int) : (term304 w x y z) = (term739 w y x z).
Proof. exact (MK_COMB (@lem2420584 w y x z) (@lem2420473)). Qed.
Lemma lem2420586 (w : int) (y : int) (x : int) (z : int) : (term739 w y x z) = (term740 w y x z).
Proof. exact (@lem1982755 (term177 w y) (term712 w y x z) term192). Qed.
Lemma lem2420587 (w : int) (y : int) (x : int) (z : int) : (term741 w y x z) = (term742 w y x z).
Proof. exact (@lem1982755 (term708 w z) (term710 y x z) term192). Qed.
Lemma lem2420592 (y : int) (x : int) (z : int) : (term743 y x z) = (term744 y x z).
Proof. exact (@lem1982755 (term708 x y) (term177 x z) term192). Qed.
Lemma lem2420593 (w : int) (z : int) : (term711 w z) = (term711 w z).
Proof. exact (eq_refl (term711 w z)). Qed.
Lemma lem2420594 (w : int) (y : int) (x : int) (z : int) : (term742 w y x z) = (term745 w y x z).
Proof. exact (MK_COMB (@lem2420593 w z) (@lem2420592 y x z)). Qed.
Lemma lem2420595 (w : int) (y : int) (x : int) (z : int) : (term741 w y x z) = (term745 w y x z).
Proof. exact (TRANS (@lem2420587 w y x z) (@lem2420594 w y x z)). Qed.
Lemma lem2420596 (w : int) (y : int) : (term283 w y) = (term283 w y).
Proof. exact (eq_refl (term283 w y)). Qed.
Lemma lem2420597 (w : int) (y : int) (x : int) (z : int) : (term740 w y x z) = (term746 w y x z).
Proof. exact (MK_COMB (@lem2420596 w y) (@lem2420595 w y x z)). Qed.
Lemma lem2420598 (w : int) (y : int) (x : int) (z : int) : (term739 w y x z) = (term746 w y x z).
Proof. exact (TRANS (@lem2420586 w y x z) (@lem2420597 w y x z)). Qed.
Lemma lem2420599 (w : int) (y : int) (x : int) (z : int) : (term304 w x y z) = (term746 w y x z).
Proof. exact (TRANS (@lem2420585 w y x z) (@lem2420598 w y x z)). Qed.
Lemma lem2420602 : term539 = term539.
Proof. exact (eq_refl term539). Qed.
Lemma lem2420603 (w : int) (y : int) (x : int) (z : int) : (term747 w x y z) = (term748 w y x z).
Proof. exact (MK_COMB (@lem2420602) (@lem2420599 w y x z)). Qed.
Lemma lem2420604 (w : int) (y : int) (x : int) (z : int) : (term748 w y x z) = (term749 w y x z).
Proof. exact (@lem1982792 term182 (term746 w y x z)). Qed.
Lemma lem2420605 (w : int) (y : int) (x : int) (z : int) : (term750 w y x z) = (term751 w y x z).
Proof. exact (@lem1982781 (term177 w y) term546 (term745 w y x z)). Qed.
Lemma lem2420606 (w : int) (y : int) (x : int) (z : int) : (term752 w y x z) = (term753 w y x z).
Proof. exact (@lem1982781 (term708 w z) term546 (term744 y x z)). Qed.
Lemma lem2420607 (y : int) (x : int) (z : int) : (term754 y x z) = (term755 y x z).
Proof. exact (@lem1982781 (term708 x y) term546 (term756 x z)). Qed.
Lemma lem2420608 (x : int) (z : int) : (term757 x z) = (term758 x z).
Proof. exact (@lem1982781 (term177 x z) term546 term192). Qed.
Lemma lem2420610 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2420611 : term192 = term567.
Proof. exact (@lem2420610 term193). Qed.
Lemma lem2420613 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420614 : term546 = term547.
Proof. exact (@lem2420613 term193). Qed.
Lemma lem2420615 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420616 : term548 = term549.
Proof. exact (MK_COMB (@lem2420615) (@lem2420614)). Qed.
Lemma lem2420617 : term568 = term569.
Proof. exact (MK_COMB (@lem2420616) (@lem2420611)). Qed.
Lemma lem2420618 : term569 = term570.
Proof. exact (@lem1981613 term546 term192 term192 term192). Qed.
Lemma lem2420620 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2420621 : term555 = term556.
Proof. exact (@lem2420620 term193 term193). Qed.
Lemma lem2420622 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420623 : term558 = term193.
Proof. exact (EQ_MP (@lem2420622) (@lem940073)). Qed.
Lemma lem2420624 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420625 : term556 = term192.
Proof. exact (MK_COMB (@lem2420624) (@lem2420623)). Qed.
Lemma lem2420626 : term555 = term192.
Proof. exact (TRANS (@lem2420621) (@lem2420625)). Qed.
Lemma lem2420628 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2420629 : term568 = term573.
Proof. exact (@lem2420628 term193 term193). Qed.
Lemma lem2420630 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420631 : term558 = term193.
Proof. exact (EQ_MP (@lem2420630) (@lem940073)). Qed.
Lemma lem2420632 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420633 : term556 = term192.
Proof. exact (MK_COMB (@lem2420632) (@lem2420631)). Qed.
Lemma lem2420634 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2420635 : term573 = term546.
Proof. exact (MK_COMB (@lem2420634) (@lem2420633)). Qed.
Lemma lem2420636 : term568 = term546.
Proof. exact (TRANS (@lem2420629) (@lem2420635)). Qed.
Lemma lem2420637 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2420638 : term574 = term575.
Proof. exact (MK_COMB (@lem2420637) (@lem2420636)). Qed.
Lemma lem2420639 : term570 = term547.
Proof. exact (MK_COMB (@lem2420638) (@lem2420626)). Qed.
Lemma lem2420640 : term569 = term547.
Proof. exact (TRANS (@lem2420618) (@lem2420639)). Qed.
Lemma lem2420641 : term568 = term547.
Proof. exact (TRANS (@lem2420617) (@lem2420640)). Qed.
Lemma lem2420643 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2420644 : term547 = term546.
Proof. exact (@lem2420643 term546). Qed.
Lemma lem2420645 : term568 = term546.
Proof. exact (TRANS (@lem2420641) (@lem2420644)). Qed.
Lemma lem2420648 (x : int) (z : int) : (term711 x z) = (term711 x z).
Proof. exact (eq_refl (term711 x z)). Qed.
Lemma lem2420649 (x : int) (z : int) : (term758 x z) = (term759 x z).
Proof. exact (MK_COMB (@lem2420648 x z) (@lem2420645)). Qed.
Lemma lem2420650 (x : int) (z : int) : (term757 x z) = (term759 x z).
Proof. exact (TRANS (@lem2420608 x z) (@lem2420649 x z)). Qed.
Lemma lem2420651 (x : int) (y : int) : (term760 x y) = (term734 x y).
Proof. exact (@lem1982749 term546 term546 (term177 x y)). Qed.
Lemma lem2420653 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420654 : term546 = term547.
Proof. exact (@lem2420653 term193). Qed.
Lemma lem2420656 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420657 : term546 = term547.
Proof. exact (@lem2420656 term193). Qed.
Lemma lem2420658 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420659 : term548 = term549.
Proof. exact (MK_COMB (@lem2420658) (@lem2420657)). Qed.
Lemma lem2420660 : term643 = term644.
Proof. exact (MK_COMB (@lem2420659) (@lem2420654)). Qed.
Lemma lem2420661 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2420663 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2420664 : term555 = term556.
Proof. exact (@lem2420663 term193 term193). Qed.
Lemma lem2420665 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420666 : term558 = term193.
Proof. exact (EQ_MP (@lem2420665) (@lem940073)). Qed.
Lemma lem2420667 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420668 : term556 = term192.
Proof. exact (MK_COMB (@lem2420667) (@lem2420666)). Qed.
Lemma lem2420669 : term555 = term192.
Proof. exact (TRANS (@lem2420664) (@lem2420668)). Qed.
Lemma lem2420671 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2420672 : term643 = term556.
Proof. exact (@lem2420671 term193 term193). Qed.
Lemma lem2420673 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420674 : term558 = term193.
Proof. exact (EQ_MP (@lem2420673) (@lem940073)). Qed.
Lemma lem2420675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420676 : term556 = term192.
Proof. exact (MK_COMB (@lem2420675) (@lem2420674)). Qed.
Lemma lem2420677 : term643 = term192.
Proof. exact (TRANS (@lem2420672) (@lem2420676)). Qed.
Lemma lem2420678 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2420679 : term647 = term648.
Proof. exact (MK_COMB (@lem2420678) (@lem2420677)). Qed.
Lemma lem2420680 : term645 = term567.
Proof. exact (MK_COMB (@lem2420679) (@lem2420669)). Qed.
Lemma lem2420681 : term644 = term567.
Proof. exact (TRANS (@lem2420661) (@lem2420680)). Qed.
Lemma lem2420682 : term643 = term567.
Proof. exact (TRANS (@lem2420660) (@lem2420681)). Qed.
Lemma lem2420684 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2420685 : term567 = term192.
Proof. exact (@lem2420684 term192). Qed.
Lemma lem2420686 : term643 = term192.
Proof. exact (TRANS (@lem2420682) (@lem2420685)). Qed.
Lemma lem2420687 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420688 : term649 = term650.
Proof. exact (MK_COMB (@lem2420687) (@lem2420686)). Qed.
Lemma lem2420689 (x : int) (y : int) : (term177 x y) = (term177 x y).
Proof. exact (eq_refl (term177 x y)). Qed.
Lemma lem2420690 (x : int) (y : int) : (term734 x y) = (term735 x y).
Proof. exact (MK_COMB (@lem2420688) (@lem2420689 x y)). Qed.
Lemma lem2420691 (x : int) (y : int) : (term760 x y) = (term735 x y).
Proof. exact (TRANS (@lem2420651 x y) (@lem2420690 x y)). Qed.
Lemma lem2420692 (x : int) (y : int) : (term735 x y) = (term177 x y).
Proof. exact (@lem1982709 (term177 x y)). Qed.
Lemma lem2420693 (x : int) (y : int) : (term760 x y) = (term177 x y).
Proof. exact (TRANS (@lem2420691 x y) (@lem2420692 x y)). Qed.
Lemma lem2420694 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2420695 (x : int) (y : int) : (term761 x y) = (term283 x y).
Proof. exact (MK_COMB (@lem2420694) (@lem2420693 x y)). Qed.
Lemma lem2420696 (y : int) (x : int) (z : int) : (term755 y x z) = (term762 y x z).
Proof. exact (MK_COMB (@lem2420695 x y) (@lem2420650 x z)). Qed.
Lemma lem2420697 (y : int) (x : int) (z : int) : (term754 y x z) = (term762 y x z).
Proof. exact (TRANS (@lem2420607 y x z) (@lem2420696 y x z)). Qed.
Lemma lem2420698 (w : int) (z : int) : (term760 w z) = (term734 w z).
Proof. exact (@lem1982749 term546 term546 (term177 w z)). Qed.
Lemma lem2420700 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420701 : term546 = term547.
Proof. exact (@lem2420700 term193). Qed.
Lemma lem2420703 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420704 : term546 = term547.
Proof. exact (@lem2420703 term193). Qed.
Lemma lem2420705 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420706 : term548 = term549.
Proof. exact (MK_COMB (@lem2420705) (@lem2420704)). Qed.
Lemma lem2420707 : term643 = term644.
Proof. exact (MK_COMB (@lem2420706) (@lem2420701)). Qed.
Lemma lem2420708 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2420710 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2420711 : term555 = term556.
Proof. exact (@lem2420710 term193 term193). Qed.
Lemma lem2420712 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420713 : term558 = term193.
Proof. exact (EQ_MP (@lem2420712) (@lem940073)). Qed.
Lemma lem2420714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420715 : term556 = term192.
Proof. exact (MK_COMB (@lem2420714) (@lem2420713)). Qed.
Lemma lem2420716 : term555 = term192.
Proof. exact (TRANS (@lem2420711) (@lem2420715)). Qed.
Lemma lem2420718 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2420719 : term643 = term556.
Proof. exact (@lem2420718 term193 term193). Qed.
Lemma lem2420720 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420721 : term558 = term193.
Proof. exact (EQ_MP (@lem2420720) (@lem940073)). Qed.
Lemma lem2420722 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420723 : term556 = term192.
Proof. exact (MK_COMB (@lem2420722) (@lem2420721)). Qed.
Lemma lem2420724 : term643 = term192.
Proof. exact (TRANS (@lem2420719) (@lem2420723)). Qed.
Lemma lem2420725 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2420726 : term647 = term648.
Proof. exact (MK_COMB (@lem2420725) (@lem2420724)). Qed.
Lemma lem2420727 : term645 = term567.
Proof. exact (MK_COMB (@lem2420726) (@lem2420716)). Qed.
Lemma lem2420728 : term644 = term567.
Proof. exact (TRANS (@lem2420708) (@lem2420727)). Qed.
Lemma lem2420729 : term643 = term567.
Proof. exact (TRANS (@lem2420707) (@lem2420728)). Qed.
Lemma lem2420731 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2420732 : term567 = term192.
Proof. exact (@lem2420731 term192). Qed.
Lemma lem2420733 : term643 = term192.
Proof. exact (TRANS (@lem2420729) (@lem2420732)). Qed.
Lemma lem2420734 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420735 : term649 = term650.
Proof. exact (MK_COMB (@lem2420734) (@lem2420733)). Qed.
Lemma lem2420736 (w : int) (z : int) : (term177 w z) = (term177 w z).
Proof. exact (eq_refl (term177 w z)). Qed.
Lemma lem2420737 (w : int) (z : int) : (term734 w z) = (term735 w z).
Proof. exact (MK_COMB (@lem2420735) (@lem2420736 w z)). Qed.
Lemma lem2420738 (w : int) (z : int) : (term760 w z) = (term735 w z).
Proof. exact (TRANS (@lem2420698 w z) (@lem2420737 w z)). Qed.
Lemma lem2420739 (w : int) (z : int) : (term735 w z) = (term177 w z).
Proof. exact (@lem1982709 (term177 w z)). Qed.
Lemma lem2420740 (w : int) (z : int) : (term760 w z) = (term177 w z).
Proof. exact (TRANS (@lem2420738 w z) (@lem2420739 w z)). Qed.
Lemma lem2420741 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2420742 (w : int) (z : int) : (term761 w z) = (term283 w z).
Proof. exact (MK_COMB (@lem2420741) (@lem2420740 w z)). Qed.
Lemma lem2420743 (w : int) (y : int) (x : int) (z : int) : (term753 w y x z) = (term763 w y x z).
Proof. exact (MK_COMB (@lem2420742 w z) (@lem2420697 y x z)). Qed.
Lemma lem2420744 (w : int) (y : int) (x : int) (z : int) : (term752 w y x z) = (term763 w y x z).
Proof. exact (TRANS (@lem2420606 w y x z) (@lem2420743 w y x z)). Qed.
Lemma lem2420747 (w : int) (y : int) : (term711 w y) = (term711 w y).
Proof. exact (eq_refl (term711 w y)). Qed.
Lemma lem2420748 (w : int) (y : int) (x : int) (z : int) : (term751 w y x z) = (term764 w y x z).
Proof. exact (MK_COMB (@lem2420747 w y) (@lem2420744 w y x z)). Qed.
Lemma lem2420749 (w : int) (y : int) (x : int) (z : int) : (term750 w y x z) = (term764 w y x z).
Proof. exact (TRANS (@lem2420605 w y x z) (@lem2420748 w y x z)). Qed.
Lemma lem2420750 : term206 = term206.
Proof. exact (eq_refl term206). Qed.
Lemma lem2420751 (w : int) (y : int) (x : int) (z : int) : (term749 w y x z) = (term765 w y x z).
Proof. exact (MK_COMB (@lem2420750) (@lem2420749 w y x z)). Qed.
Lemma lem2420752 (w : int) (y : int) (x : int) (z : int) : (term765 w y x z) = (term764 w y x z).
Proof. exact (@lem1982721 (term764 w y x z)). Qed.
Lemma lem2420753 (w : int) (y : int) (x : int) (z : int) : (term749 w y x z) = (term764 w y x z).
Proof. exact (TRANS (@lem2420751 w y x z) (@lem2420752 w y x z)). Qed.
Lemma lem2420754 (w : int) (y : int) (x : int) (z : int) : (term748 w y x z) = (term764 w y x z).
Proof. exact (TRANS (@lem2420604 w y x z) (@lem2420753 w y x z)). Qed.
Lemma lem2420755 (w : int) (y : int) (x : int) (z : int) : (term747 w x y z) = (term764 w y x z).
Proof. exact (TRANS (@lem2420603 w y x z) (@lem2420754 w y x z)). Qed.
Lemma lem2420756 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2420757 (w : int) (y : int) (x : int) (z : int) : (term766 w x y z) = (term767 w y x z).
Proof. exact (MK_COMB (@lem2420756) (@lem2420755 w y x z)). Qed.
Lemma lem2420758 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2420759 (w : int) (y : int) (x : int) (z : int) : (term722 w x y z) = (term768 w y x z).
Proof. exact (MK_COMB (@lem2420757 w y x z) (@lem2420758)). Qed.
Lemma lem2420760 (w : int) (y : int) (x : int) (z : int) : (term307 w x y z) = (term768 w y x z).
Proof. exact (TRANS (@lem2420472 w x y z) (@lem2420759 w y x z)). Qed.
Lemma lem2420761 (w : int) (x : int) (y : int) (z : int) : (term312 w x y z) = (term769 w x y z).
Proof. exact (@lem1988287 (term301 w x y z) term207). Qed.
Lemma lem2420768 : term207 = term192.
Proof. exact (@lem1982721 term192). Qed.
Lemma lem2420781 (y : int) (z : int) : (term173 y z) = (term620 y z).
Proof. exact (@lem1982792 (real_of_int y) (real_of_int z)). Qed.
Lemma lem2420794 (w : int) (x : int) : (term173 w x) = (term620 w x).
Proof. exact (@lem1982792 (real_of_int w) (real_of_int x)). Qed.
Lemma lem2420795 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420796 (w : int) (x : int) : (term300 w x) = (term723 w x).
Proof. exact (MK_COMB (@lem2420795) (@lem2420794 w x)). Qed.
Lemma lem2420797 (w : int) (x : int) (y : int) (z : int) : (term301 w x y z) = (term724 w x y z).
Proof. exact (MK_COMB (@lem2420796 w x) (@lem2420781 y z)). Qed.
Lemma lem2420798 (w : int) (x : int) (y : int) (z : int) : (term724 w x y z) = (term725 w x y z).
Proof. exact (@lem1982727 (real_of_int w) (term595 x) (term620 y z)). Qed.
Lemma lem2420799 (y : int) (w : int) (z : int) : (term726 w y z) = (term727 y w z).
Proof. exact (@lem1982781 (real_of_int y) (real_of_int w) (term595 z)). Qed.
Lemma lem2420804 (w : int) (z : int) : (term728 w z) = (term708 w z).
Proof. exact (@lem1982751 term546 (real_of_int w) (real_of_int z)). Qed.
Lemma lem2420807 (w : int) (y : int) : (term283 w y) = (term283 w y).
Proof. exact (eq_refl (term283 w y)). Qed.
Lemma lem2420808 (y : int) (w : int) (z : int) : (term727 y w z) = (term709 y w z).
Proof. exact (MK_COMB (@lem2420807 w y) (@lem2420804 w z)). Qed.
Lemma lem2420809 (y : int) (w : int) (z : int) : (term726 w y z) = (term709 y w z).
Proof. exact (TRANS (@lem2420799 y w z) (@lem2420808 y w z)). Qed.
Lemma lem2420810 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2420811 (y : int) (w : int) (z : int) : (term729 w y z) = (term730 y w z).
Proof. exact (MK_COMB (@lem2420810) (@lem2420809 y w z)). Qed.
Lemma lem2420812 (y : int) (x : int) (z : int) : (term731 x y z) = (term732 y x z).
Proof. exact (@lem1982781 (real_of_int y) (term595 x) (term595 z)). Qed.
Lemma lem2420813 (x : int) (z : int) : (term733 x z) = (term734 x z).
Proof. exact (@lem1982737 term546 term546 (real_of_int x) (real_of_int z)). Qed.
Lemma lem2420815 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420816 : term546 = term547.
Proof. exact (@lem2420815 term193). Qed.
Lemma lem2420818 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420819 : term546 = term547.
Proof. exact (@lem2420818 term193). Qed.
Lemma lem2420820 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420821 : term548 = term549.
Proof. exact (MK_COMB (@lem2420820) (@lem2420819)). Qed.
Lemma lem2420822 : term643 = term644.
Proof. exact (MK_COMB (@lem2420821) (@lem2420816)). Qed.
Lemma lem2420823 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2420825 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2420826 : term555 = term556.
Proof. exact (@lem2420825 term193 term193). Qed.
Lemma lem2420827 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420828 : term558 = term193.
Proof. exact (EQ_MP (@lem2420827) (@lem940073)). Qed.
Lemma lem2420829 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420830 : term556 = term192.
Proof. exact (MK_COMB (@lem2420829) (@lem2420828)). Qed.
Lemma lem2420831 : term555 = term192.
Proof. exact (TRANS (@lem2420826) (@lem2420830)). Qed.
Lemma lem2420833 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2420834 : term643 = term556.
Proof. exact (@lem2420833 term193 term193). Qed.
Lemma lem2420835 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420836 : term558 = term193.
Proof. exact (EQ_MP (@lem2420835) (@lem940073)). Qed.
Lemma lem2420837 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420838 : term556 = term192.
Proof. exact (MK_COMB (@lem2420837) (@lem2420836)). Qed.
Lemma lem2420839 : term643 = term192.
Proof. exact (TRANS (@lem2420834) (@lem2420838)). Qed.
Lemma lem2420840 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2420841 : term647 = term648.
Proof. exact (MK_COMB (@lem2420840) (@lem2420839)). Qed.
Lemma lem2420842 : term645 = term567.
Proof. exact (MK_COMB (@lem2420841) (@lem2420831)). Qed.
Lemma lem2420843 : term644 = term567.
Proof. exact (TRANS (@lem2420823) (@lem2420842)). Qed.
Lemma lem2420844 : term643 = term567.
Proof. exact (TRANS (@lem2420822) (@lem2420843)). Qed.
Lemma lem2420846 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2420847 : term567 = term192.
Proof. exact (@lem2420846 term192). Qed.
Lemma lem2420848 : term643 = term192.
Proof. exact (TRANS (@lem2420844) (@lem2420847)). Qed.
Lemma lem2420849 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420850 : term649 = term650.
Proof. exact (MK_COMB (@lem2420849) (@lem2420848)). Qed.
Lemma lem2420851 (x : int) (z : int) : (term177 x z) = (term177 x z).
Proof. exact (eq_refl (term177 x z)). Qed.
Lemma lem2420852 (x : int) (z : int) : (term734 x z) = (term735 x z).
Proof. exact (MK_COMB (@lem2420850) (@lem2420851 x z)). Qed.
Lemma lem2420857 (x : int) (z : int) : (term733 x z) = (term735 x z).
Proof. exact (TRANS (@lem2420813 x z) (@lem2420852 x z)). Qed.
Lemma lem2420858 (x : int) (z : int) : (term735 x z) = (term177 x z).
Proof. exact (@lem1982709 (term177 x z)). Qed.
Lemma lem2420859 (x : int) (z : int) : (term733 x z) = (term177 x z).
Proof. exact (TRANS (@lem2420857 x z) (@lem2420858 x z)). Qed.
Lemma lem2420864 (x : int) (y : int) : (term736 x y) = (term708 x y).
Proof. exact (@lem1982745 term546 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2420865 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2420866 (x : int) (y : int) : (term737 x y) = (term711 x y).
Proof. exact (MK_COMB (@lem2420865) (@lem2420864 x y)). Qed.
Lemma lem2420867 (y : int) (x : int) (z : int) : (term732 y x z) = (term710 y x z).
Proof. exact (MK_COMB (@lem2420866 x y) (@lem2420859 x z)). Qed.
Lemma lem2420868 (y : int) (x : int) (z : int) : (term731 x y z) = (term710 y x z).
Proof. exact (TRANS (@lem2420812 y x z) (@lem2420867 y x z)). Qed.
Lemma lem2420869 (w : int) (y : int) (x : int) (z : int) : (term725 w x y z) = (term738 w y x z).
Proof. exact (MK_COMB (@lem2420811 y w z) (@lem2420868 y x z)). Qed.
Lemma lem2420870 (w : int) (y : int) (x : int) (z : int) : (term724 w x y z) = (term738 w y x z).
Proof. exact (TRANS (@lem2420798 w x y z) (@lem2420869 w y x z)). Qed.
Lemma lem2420875 (w : int) (y : int) (x : int) (z : int) : (term738 w y x z) = (term713 w y x z).
Proof. exact (@lem1982755 (term177 w y) (term708 w z) (term710 y x z)). Qed.
Lemma lem2420876 (w : int) (y : int) (x : int) (z : int) : (term724 w x y z) = (term713 w y x z).
Proof. exact (TRANS (@lem2420870 w y x z) (@lem2420875 w y x z)). Qed.
Lemma lem2420877 (w : int) (y : int) (x : int) (z : int) : (term301 w x y z) = (term713 w y x z).
Proof. exact (TRANS (@lem2420797 w x y z) (@lem2420876 w y x z)). Qed.
Lemma lem2420878 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2420879 (w : int) (y : int) (x : int) (z : int) : (term770 w x y z) = (term715 w y x z).
Proof. exact (MK_COMB (@lem2420878) (@lem2420877 w y x z)). Qed.
Lemma lem2420880 (w : int) (y : int) (x : int) (z : int) : (term771 w x y z) = (term772 w y x z).
Proof. exact (MK_COMB (@lem2420879 w y x z) (@lem2420768)). Qed.
Lemma lem2420881 (w : int) (y : int) (x : int) (z : int) : (term772 w y x z) = (term773 w y x z).
Proof. exact (@lem1982792 (term713 w y x z) term192). Qed.
Lemma lem2420883 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2420884 : term192 = term567.
Proof. exact (@lem2420883 term193). Qed.
Lemma lem2420886 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2420887 : term546 = term547.
Proof. exact (@lem2420886 term193). Qed.
Lemma lem2420888 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2420889 : term548 = term549.
Proof. exact (MK_COMB (@lem2420888) (@lem2420887)). Qed.
Lemma lem2420890 : term568 = term569.
Proof. exact (MK_COMB (@lem2420889) (@lem2420884)). Qed.
Lemma lem2420891 : term569 = term570.
Proof. exact (@lem1981613 term546 term192 term192 term192). Qed.
Lemma lem2420893 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2420894 : term555 = term556.
Proof. exact (@lem2420893 term193 term193). Qed.
Lemma lem2420895 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420896 : term558 = term193.
Proof. exact (EQ_MP (@lem2420895) (@lem940073)). Qed.
Lemma lem2420897 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420898 : term556 = term192.
Proof. exact (MK_COMB (@lem2420897) (@lem2420896)). Qed.
Lemma lem2420899 : term555 = term192.
Proof. exact (TRANS (@lem2420894) (@lem2420898)). Qed.
Lemma lem2420901 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2420902 : term568 = term573.
Proof. exact (@lem2420901 term193 term193). Qed.
Lemma lem2420903 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2420904 : term558 = term193.
Proof. exact (EQ_MP (@lem2420903) (@lem940073)). Qed.
Lemma lem2420905 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2420906 : term556 = term192.
Proof. exact (MK_COMB (@lem2420905) (@lem2420904)). Qed.
Lemma lem2420907 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2420908 : term573 = term546.
Proof. exact (MK_COMB (@lem2420907) (@lem2420906)). Qed.
Lemma lem2420909 : term568 = term546.
Proof. exact (TRANS (@lem2420902) (@lem2420908)). Qed.
Lemma lem2420910 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2420911 : term574 = term575.
Proof. exact (MK_COMB (@lem2420910) (@lem2420909)). Qed.
Lemma lem2420912 : term570 = term547.
Proof. exact (MK_COMB (@lem2420911) (@lem2420899)). Qed.
Lemma lem2420913 : term569 = term547.
Proof. exact (TRANS (@lem2420891) (@lem2420912)). Qed.
Lemma lem2420914 : term568 = term547.
Proof. exact (TRANS (@lem2420890) (@lem2420913)). Qed.
Lemma lem2420916 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2420917 : term547 = term546.
Proof. exact (@lem2420916 term546). Qed.
Lemma lem2420918 : term568 = term546.
Proof. exact (TRANS (@lem2420914) (@lem2420917)). Qed.
Lemma lem2420919 (w : int) (y : int) (x : int) (z : int) : (term718 w y x z) = (term718 w y x z).
Proof. exact (eq_refl (term718 w y x z)). Qed.
Lemma lem2420920 (w : int) (y : int) (x : int) (z : int) : (term773 w y x z) = (term774 w y x z).
Proof. exact (MK_COMB (@lem2420919 w y x z) (@lem2420918)). Qed.
Lemma lem2420921 (w : int) (y : int) (x : int) (z : int) : (term774 w y x z) = (term775 w y x z).
Proof. exact (@lem1982755 (term177 w y) (term712 w y x z) term546). Qed.
Lemma lem2420922 (w : int) (y : int) (x : int) (z : int) : (term776 w y x z) = (term777 w y x z).
Proof. exact (@lem1982755 (term708 w z) (term710 y x z) term546). Qed.
Lemma lem2420927 (y : int) (x : int) (z : int) : (term778 y x z) = (term779 y x z).
Proof. exact (@lem1982755 (term708 x y) (term177 x z) term546). Qed.
Lemma lem2420928 (w : int) (z : int) : (term711 w z) = (term711 w z).
Proof. exact (eq_refl (term711 w z)). Qed.
Lemma lem2420929 (w : int) (y : int) (x : int) (z : int) : (term777 w y x z) = (term780 w y x z).
Proof. exact (MK_COMB (@lem2420928 w z) (@lem2420927 y x z)). Qed.
Lemma lem2420930 (w : int) (y : int) (x : int) (z : int) : (term776 w y x z) = (term780 w y x z).
Proof. exact (TRANS (@lem2420922 w y x z) (@lem2420929 w y x z)). Qed.
Lemma lem2420931 (w : int) (y : int) : (term283 w y) = (term283 w y).
Proof. exact (eq_refl (term283 w y)). Qed.
Lemma lem2420932 (w : int) (y : int) (x : int) (z : int) : (term775 w y x z) = (term781 w y x z).
Proof. exact (MK_COMB (@lem2420931 w y) (@lem2420930 w y x z)). Qed.
Lemma lem2420933 (w : int) (y : int) (x : int) (z : int) : (term774 w y x z) = (term781 w y x z).
Proof. exact (TRANS (@lem2420921 w y x z) (@lem2420932 w y x z)). Qed.
Lemma lem2420934 (w : int) (y : int) (x : int) (z : int) : (term773 w y x z) = (term781 w y x z).
Proof. exact (TRANS (@lem2420920 w y x z) (@lem2420933 w y x z)). Qed.
Lemma lem2420935 (w : int) (y : int) (x : int) (z : int) : (term772 w y x z) = (term781 w y x z).
Proof. exact (TRANS (@lem2420881 w y x z) (@lem2420934 w y x z)). Qed.
Lemma lem2420936 (w : int) (y : int) (x : int) (z : int) : (term771 w x y z) = (term781 w y x z).
Proof. exact (TRANS (@lem2420880 w y x z) (@lem2420935 w y x z)). Qed.
Lemma lem2420937 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2420938 (w : int) (y : int) (x : int) (z : int) : (term782 w x y z) = (term783 w y x z).
Proof. exact (MK_COMB (@lem2420937) (@lem2420936 w y x z)). Qed.
Lemma lem2420939 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2420940 (w : int) (y : int) (x : int) (z : int) : (term769 w x y z) = (term784 w y x z).
Proof. exact (MK_COMB (@lem2420938 w y x z) (@lem2420939)). Qed.
Lemma lem2420941 (w : int) (y : int) (x : int) (z : int) : (term312 w x y z) = (term784 w y x z).
Proof. exact (TRANS (@lem2420761 w x y z) (@lem2420940 w y x z)). Qed.
Lemma lem2420942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2420943 (w : int) (y : int) (x : int) (z : int) : (term309 w x y z) = (term785 w y x z).
Proof. exact (MK_COMB (@lem2420942) (@lem2420760 w y x z)). Qed.
Lemma lem2420944 (w : int) (y : int) (x : int) (z : int) : (term313 w x y z) = (term786 w y x z).
Proof. exact (MK_COMB (@lem2420943 w y x z) (@lem2420941 w y x z)). Qed.
Lemma lem2420945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2420946 (w : int) (y : int) (x : int) (z : int) : (term315 w z x y) = (term787 w y x z).
Proof. exact (MK_COMB (@lem2420945) (@lem2420471 w y x z)). Qed.
Lemma lem2420947 (w : int) (y : int) (x : int) (z : int) : (term317 w x y z) = (term788 w y x z).
Proof. exact (MK_COMB (@lem2420946 w y x z) (@lem2420944 w y x z)). Qed.
Lemma lem2420948 (w : int) (y : int) (x : int) : (term452 w x y) = (term789 w y x).
Proof. exact (fun_ext (fun z : int => @lem2420947 w y x z)). Qed.
Lemma lem2420949 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2420950 (w : int) (y : int) (x : int) : (term463 w x y) = (term790 w y x).
Proof. exact (MK_COMB (@lem2420949) (@lem2420948 w y x)). Qed.
Lemma lem2420951 (w : int) (x : int) : (term474 w x) = (term791 w x).
Proof. exact (fun_ext (fun y : int => @lem2420950 w y x)). Qed.
Lemma lem2420952 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2420953 (w : int) (x : int) : (term485 w x) = (term792 w x).
Proof. exact (MK_COMB (@lem2420952) (@lem2420951 w x)). Qed.
Lemma lem2420954 (w : int) : (term496 w) = (term793 w).
Proof. exact (fun_ext (fun x : int => @lem2420953 w x)). Qed.
Lemma lem2420955 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2420956 (w : int) : (term507 w) = (term794 w).
Proof. exact (MK_COMB (@lem2420955) (@lem2420954 w)). Qed.
Lemma lem2420957 : term518 = term795.
Proof. exact (fun_ext (fun w : int => @lem2420956 w)). Qed.
Lemma lem2420958 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2420959 : term529 = term796.
Proof. exact (MK_COMB (@lem2420958) (@lem2420957)). Qed.
Lemma lem2420960 (w : int) (z : int) (x : int) (y : int) : (term330 w z x y) = (term797 w z x y).
Proof. exact (@lem1988287 term182 (term327 w z x y)). Qed.
Lemma lem2420961 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2421003 (w : int) (z : int) (x : int) (y : int) : (term287 w z x y) = (term700 w z x y).
Proof. exact (@lem1982792 (term284 w y x z) (term284 w z x y)). Qed.
Lemma lem2421010 (w : int) (z : int) (x : int) (y : int) : (term701 w z x y) = (term702 w z x y).
Proof. exact (@lem1982781 (term177 w z) term546 (term177 x y)). Qed.
Lemma lem2421011 (w : int) (y : int) (x : int) (z : int) : (term703 w y x z) = (term703 w y x z).
Proof. exact (eq_refl (term703 w y x z)). Qed.
Lemma lem2421012 (w : int) (z : int) (x : int) (y : int) : (term700 w z x y) = (term704 w z x y).
Proof. exact (MK_COMB (@lem2421011 w y x z) (@lem2421010 w z x y)). Qed.
Lemma lem2421013 (w : int) (z : int) (x : int) (y : int) : (term704 w z x y) = (term705 w z x y).
Proof. exact (@lem1982755 (term177 w y) (term177 x z) (term702 w z x y)). Qed.
Lemma lem2421014 (w : int) (z : int) (x : int) (y : int) : (term706 w z x y) = (term707 w z x y).
Proof. exact (@lem1982757 (term708 w z) (term177 x z) (term708 x y)). Qed.
Lemma lem2421015 (y : int) (x : int) (z : int) : (term709 z x y) = (term710 y x z).
Proof. exact (@lem1982761 (term708 x y) (term177 x z)). Qed.
Lemma lem2421016 (w : int) (z : int) : (term711 w z) = (term711 w z).
Proof. exact (eq_refl (term711 w z)). Qed.
Lemma lem2421017 (w : int) (y : int) (x : int) (z : int) : (term707 w z x y) = (term712 w y x z).
Proof. exact (MK_COMB (@lem2421016 w z) (@lem2421015 y x z)). Qed.
Lemma lem2421018 (w : int) (y : int) (x : int) (z : int) : (term706 w z x y) = (term712 w y x z).
Proof. exact (TRANS (@lem2421014 w z x y) (@lem2421017 w y x z)). Qed.
Lemma lem2421019 (w : int) (y : int) : (term283 w y) = (term283 w y).
Proof. exact (eq_refl (term283 w y)). Qed.
Lemma lem2421020 (w : int) (y : int) (x : int) (z : int) : (term705 w z x y) = (term713 w y x z).
Proof. exact (MK_COMB (@lem2421019 w y) (@lem2421018 w y x z)). Qed.
Lemma lem2421021 (w : int) (y : int) (x : int) (z : int) : (term704 w z x y) = (term713 w y x z).
Proof. exact (TRANS (@lem2421013 w z x y) (@lem2421020 w y x z)). Qed.
Lemma lem2421022 (w : int) (y : int) (x : int) (z : int) : (term700 w z x y) = (term713 w y x z).
Proof. exact (TRANS (@lem2421012 w z x y) (@lem2421021 w y x z)). Qed.
Lemma lem2421024 (w : int) (y : int) (x : int) (z : int) : (term287 w z x y) = (term713 w y x z).
Proof. exact (TRANS (@lem2421003 w z x y) (@lem2421022 w y x z)). Qed.
Lemma lem2421025 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2421026 (w : int) (y : int) (x : int) (z : int) : (term326 w z x y) = (term718 w y x z).
Proof. exact (MK_COMB (@lem2421025) (@lem2421024 w y x z)). Qed.
Lemma lem2421027 (w : int) (y : int) (x : int) (z : int) : (term327 w z x y) = (term739 w y x z).
Proof. exact (MK_COMB (@lem2421026 w y x z) (@lem2420961)). Qed.
Lemma lem2421028 (w : int) (y : int) (x : int) (z : int) : (term739 w y x z) = (term740 w y x z).
Proof. exact (@lem1982755 (term177 w y) (term712 w y x z) term192). Qed.
Lemma lem2421029 (w : int) (y : int) (x : int) (z : int) : (term741 w y x z) = (term742 w y x z).
Proof. exact (@lem1982755 (term708 w z) (term710 y x z) term192). Qed.
Lemma lem2421034 (y : int) (x : int) (z : int) : (term743 y x z) = (term744 y x z).
Proof. exact (@lem1982755 (term708 x y) (term177 x z) term192). Qed.
Lemma lem2421035 (w : int) (z : int) : (term711 w z) = (term711 w z).
Proof. exact (eq_refl (term711 w z)). Qed.
Lemma lem2421036 (w : int) (y : int) (x : int) (z : int) : (term742 w y x z) = (term745 w y x z).
Proof. exact (MK_COMB (@lem2421035 w z) (@lem2421034 y x z)). Qed.
Lemma lem2421037 (w : int) (y : int) (x : int) (z : int) : (term741 w y x z) = (term745 w y x z).
Proof. exact (TRANS (@lem2421029 w y x z) (@lem2421036 w y x z)). Qed.
Lemma lem2421038 (w : int) (y : int) : (term283 w y) = (term283 w y).
Proof. exact (eq_refl (term283 w y)). Qed.
Lemma lem2421039 (w : int) (y : int) (x : int) (z : int) : (term740 w y x z) = (term746 w y x z).
Proof. exact (MK_COMB (@lem2421038 w y) (@lem2421037 w y x z)). Qed.
Lemma lem2421040 (w : int) (y : int) (x : int) (z : int) : (term739 w y x z) = (term746 w y x z).
Proof. exact (TRANS (@lem2421028 w y x z) (@lem2421039 w y x z)). Qed.
Lemma lem2421041 (w : int) (y : int) (x : int) (z : int) : (term327 w z x y) = (term746 w y x z).
Proof. exact (TRANS (@lem2421027 w y x z) (@lem2421040 w y x z)). Qed.
Lemma lem2421044 : term539 = term539.
Proof. exact (eq_refl term539). Qed.
Lemma lem2421045 (w : int) (y : int) (x : int) (z : int) : (term798 w z x y) = (term748 w y x z).
Proof. exact (MK_COMB (@lem2421044) (@lem2421041 w y x z)). Qed.
Lemma lem2421046 (w : int) (y : int) (x : int) (z : int) : (term748 w y x z) = (term749 w y x z).
Proof. exact (@lem1982792 term182 (term746 w y x z)). Qed.
Lemma lem2421047 (w : int) (y : int) (x : int) (z : int) : (term750 w y x z) = (term751 w y x z).
Proof. exact (@lem1982781 (term177 w y) term546 (term745 w y x z)). Qed.
Lemma lem2421048 (w : int) (y : int) (x : int) (z : int) : (term752 w y x z) = (term753 w y x z).
Proof. exact (@lem1982781 (term708 w z) term546 (term744 y x z)). Qed.
Lemma lem2421049 (y : int) (x : int) (z : int) : (term754 y x z) = (term755 y x z).
Proof. exact (@lem1982781 (term708 x y) term546 (term756 x z)). Qed.
Lemma lem2421050 (x : int) (z : int) : (term757 x z) = (term758 x z).
Proof. exact (@lem1982781 (term177 x z) term546 term192). Qed.
Lemma lem2421052 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2421053 : term192 = term567.
Proof. exact (@lem2421052 term193). Qed.
Lemma lem2421055 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2421056 : term546 = term547.
Proof. exact (@lem2421055 term193). Qed.
Lemma lem2421057 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2421058 : term548 = term549.
Proof. exact (MK_COMB (@lem2421057) (@lem2421056)). Qed.
Lemma lem2421059 : term568 = term569.
Proof. exact (MK_COMB (@lem2421058) (@lem2421053)). Qed.
Lemma lem2421060 : term569 = term570.
Proof. exact (@lem1981613 term546 term192 term192 term192). Qed.
Lemma lem2421062 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2421063 : term555 = term556.
Proof. exact (@lem2421062 term193 term193). Qed.
Lemma lem2421064 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2421065 : term558 = term193.
Proof. exact (EQ_MP (@lem2421064) (@lem940073)). Qed.
Lemma lem2421066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2421067 : term556 = term192.
Proof. exact (MK_COMB (@lem2421066) (@lem2421065)). Qed.
Lemma lem2421068 : term555 = term192.
Proof. exact (TRANS (@lem2421063) (@lem2421067)). Qed.
Lemma lem2421070 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2421071 : term568 = term573.
Proof. exact (@lem2421070 term193 term193). Qed.
Lemma lem2421072 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2421073 : term558 = term193.
Proof. exact (EQ_MP (@lem2421072) (@lem940073)). Qed.
Lemma lem2421074 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2421075 : term556 = term192.
Proof. exact (MK_COMB (@lem2421074) (@lem2421073)). Qed.
Lemma lem2421076 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2421077 : term573 = term546.
Proof. exact (MK_COMB (@lem2421076) (@lem2421075)). Qed.
Lemma lem2421078 : term568 = term546.
Proof. exact (TRANS (@lem2421071) (@lem2421077)). Qed.
Lemma lem2421079 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2421080 : term574 = term575.
Proof. exact (MK_COMB (@lem2421079) (@lem2421078)). Qed.
Lemma lem2421081 : term570 = term547.
Proof. exact (MK_COMB (@lem2421080) (@lem2421068)). Qed.
Lemma lem2421082 : term569 = term547.
Proof. exact (TRANS (@lem2421060) (@lem2421081)). Qed.
Lemma lem2421083 : term568 = term547.
Proof. exact (TRANS (@lem2421059) (@lem2421082)). Qed.
Lemma lem2421085 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2421086 : term547 = term546.
Proof. exact (@lem2421085 term546). Qed.
Lemma lem2421087 : term568 = term546.
Proof. exact (TRANS (@lem2421083) (@lem2421086)). Qed.
Lemma lem2421090 (x : int) (z : int) : (term711 x z) = (term711 x z).
Proof. exact (eq_refl (term711 x z)). Qed.
Lemma lem2421091 (x : int) (z : int) : (term758 x z) = (term759 x z).
Proof. exact (MK_COMB (@lem2421090 x z) (@lem2421087)). Qed.
Lemma lem2421092 (x : int) (z : int) : (term757 x z) = (term759 x z).
Proof. exact (TRANS (@lem2421050 x z) (@lem2421091 x z)). Qed.
Lemma lem2421093 (x : int) (y : int) : (term760 x y) = (term734 x y).
Proof. exact (@lem1982749 term546 term546 (term177 x y)). Qed.
Lemma lem2421095 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2421096 : term546 = term547.
Proof. exact (@lem2421095 term193). Qed.
Lemma lem2421098 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2421099 : term546 = term547.
Proof. exact (@lem2421098 term193). Qed.
Lemma lem2421100 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2421101 : term548 = term549.
Proof. exact (MK_COMB (@lem2421100) (@lem2421099)). Qed.
Lemma lem2421102 : term643 = term644.
Proof. exact (MK_COMB (@lem2421101) (@lem2421096)). Qed.
Lemma lem2421103 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2421105 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2421106 : term555 = term556.
Proof. exact (@lem2421105 term193 term193). Qed.
Lemma lem2421107 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2421108 : term558 = term193.
Proof. exact (EQ_MP (@lem2421107) (@lem940073)). Qed.
Lemma lem2421109 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2421110 : term556 = term192.
Proof. exact (MK_COMB (@lem2421109) (@lem2421108)). Qed.
Lemma lem2421111 : term555 = term192.
Proof. exact (TRANS (@lem2421106) (@lem2421110)). Qed.
Lemma lem2421113 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2421114 : term643 = term556.
Proof. exact (@lem2421113 term193 term193). Qed.
Lemma lem2421115 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2421116 : term558 = term193.
Proof. exact (EQ_MP (@lem2421115) (@lem940073)). Qed.
Lemma lem2421117 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2421118 : term556 = term192.
Proof. exact (MK_COMB (@lem2421117) (@lem2421116)). Qed.
Lemma lem2421119 : term643 = term192.
Proof. exact (TRANS (@lem2421114) (@lem2421118)). Qed.
Lemma lem2421120 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2421121 : term647 = term648.
Proof. exact (MK_COMB (@lem2421120) (@lem2421119)). Qed.
Lemma lem2421122 : term645 = term567.
Proof. exact (MK_COMB (@lem2421121) (@lem2421111)). Qed.
Lemma lem2421123 : term644 = term567.
Proof. exact (TRANS (@lem2421103) (@lem2421122)). Qed.
Lemma lem2421124 : term643 = term567.
Proof. exact (TRANS (@lem2421102) (@lem2421123)). Qed.
Lemma lem2421126 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2421127 : term567 = term192.
Proof. exact (@lem2421126 term192). Qed.
Lemma lem2421128 : term643 = term192.
Proof. exact (TRANS (@lem2421124) (@lem2421127)). Qed.
Lemma lem2421129 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2421130 : term649 = term650.
Proof. exact (MK_COMB (@lem2421129) (@lem2421128)). Qed.
Lemma lem2421131 (x : int) (y : int) : (term177 x y) = (term177 x y).
Proof. exact (eq_refl (term177 x y)). Qed.
Lemma lem2421132 (x : int) (y : int) : (term734 x y) = (term735 x y).
Proof. exact (MK_COMB (@lem2421130) (@lem2421131 x y)). Qed.
Lemma lem2421133 (x : int) (y : int) : (term760 x y) = (term735 x y).
Proof. exact (TRANS (@lem2421093 x y) (@lem2421132 x y)). Qed.
Lemma lem2421134 (x : int) (y : int) : (term735 x y) = (term177 x y).
Proof. exact (@lem1982709 (term177 x y)). Qed.
Lemma lem2421135 (x : int) (y : int) : (term760 x y) = (term177 x y).
Proof. exact (TRANS (@lem2421133 x y) (@lem2421134 x y)). Qed.
Lemma lem2421136 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2421137 (x : int) (y : int) : (term761 x y) = (term283 x y).
Proof. exact (MK_COMB (@lem2421136) (@lem2421135 x y)). Qed.
Lemma lem2421138 (y : int) (x : int) (z : int) : (term755 y x z) = (term762 y x z).
Proof. exact (MK_COMB (@lem2421137 x y) (@lem2421092 x z)). Qed.
Lemma lem2421139 (y : int) (x : int) (z : int) : (term754 y x z) = (term762 y x z).
Proof. exact (TRANS (@lem2421049 y x z) (@lem2421138 y x z)). Qed.
Lemma lem2421140 (w : int) (z : int) : (term760 w z) = (term734 w z).
Proof. exact (@lem1982749 term546 term546 (term177 w z)). Qed.
Lemma lem2421142 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2421143 : term546 = term547.
Proof. exact (@lem2421142 term193). Qed.
Lemma lem2421145 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2421146 : term546 = term547.
Proof. exact (@lem2421145 term193). Qed.
Lemma lem2421147 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2421148 : term548 = term549.
Proof. exact (MK_COMB (@lem2421147) (@lem2421146)). Qed.
Lemma lem2421149 : term643 = term644.
Proof. exact (MK_COMB (@lem2421148) (@lem2421143)). Qed.
Lemma lem2421150 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2421152 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2421153 : term555 = term556.
Proof. exact (@lem2421152 term193 term193). Qed.
Lemma lem2421154 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2421155 : term558 = term193.
Proof. exact (EQ_MP (@lem2421154) (@lem940073)). Qed.
Lemma lem2421156 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2421157 : term556 = term192.
Proof. exact (MK_COMB (@lem2421156) (@lem2421155)). Qed.
Lemma lem2421158 : term555 = term192.
Proof. exact (TRANS (@lem2421153) (@lem2421157)). Qed.
Lemma lem2421160 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2421161 : term643 = term556.
Proof. exact (@lem2421160 term193 term193). Qed.
Lemma lem2421162 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2421163 : term558 = term193.
Proof. exact (EQ_MP (@lem2421162) (@lem940073)). Qed.
Lemma lem2421164 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2421165 : term556 = term192.
Proof. exact (MK_COMB (@lem2421164) (@lem2421163)). Qed.
Lemma lem2421166 : term643 = term192.
Proof. exact (TRANS (@lem2421161) (@lem2421165)). Qed.
Lemma lem2421167 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2421168 : term647 = term648.
Proof. exact (MK_COMB (@lem2421167) (@lem2421166)). Qed.
Lemma lem2421169 : term645 = term567.
Proof. exact (MK_COMB (@lem2421168) (@lem2421158)). Qed.
Lemma lem2421170 : term644 = term567.
Proof. exact (TRANS (@lem2421150) (@lem2421169)). Qed.
Lemma lem2421171 : term643 = term567.
Proof. exact (TRANS (@lem2421149) (@lem2421170)). Qed.
Lemma lem2421173 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2421174 : term567 = term192.
Proof. exact (@lem2421173 term192). Qed.
Lemma lem2421175 : term643 = term192.
Proof. exact (TRANS (@lem2421171) (@lem2421174)). Qed.
Lemma lem2421176 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2421177 : term649 = term650.
Proof. exact (MK_COMB (@lem2421176) (@lem2421175)). Qed.
Lemma lem2421178 (w : int) (z : int) : (term177 w z) = (term177 w z).
Proof. exact (eq_refl (term177 w z)). Qed.
Lemma lem2421179 (w : int) (z : int) : (term734 w z) = (term735 w z).
Proof. exact (MK_COMB (@lem2421177) (@lem2421178 w z)). Qed.
Lemma lem2421180 (w : int) (z : int) : (term760 w z) = (term735 w z).
Proof. exact (TRANS (@lem2421140 w z) (@lem2421179 w z)). Qed.
Lemma lem2421181 (w : int) (z : int) : (term735 w z) = (term177 w z).
Proof. exact (@lem1982709 (term177 w z)). Qed.
Lemma lem2421182 (w : int) (z : int) : (term760 w z) = (term177 w z).
Proof. exact (TRANS (@lem2421180 w z) (@lem2421181 w z)). Qed.
Lemma lem2421183 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2421184 (w : int) (z : int) : (term761 w z) = (term283 w z).
Proof. exact (MK_COMB (@lem2421183) (@lem2421182 w z)). Qed.
Lemma lem2421185 (w : int) (y : int) (x : int) (z : int) : (term753 w y x z) = (term763 w y x z).
Proof. exact (MK_COMB (@lem2421184 w z) (@lem2421139 y x z)). Qed.
Lemma lem2421186 (w : int) (y : int) (x : int) (z : int) : (term752 w y x z) = (term763 w y x z).
Proof. exact (TRANS (@lem2421048 w y x z) (@lem2421185 w y x z)). Qed.
Lemma lem2421189 (w : int) (y : int) : (term711 w y) = (term711 w y).
Proof. exact (eq_refl (term711 w y)). Qed.
Lemma lem2421190 (w : int) (y : int) (x : int) (z : int) : (term751 w y x z) = (term764 w y x z).
Proof. exact (MK_COMB (@lem2421189 w y) (@lem2421186 w y x z)). Qed.
Lemma lem2421191 (w : int) (y : int) (x : int) (z : int) : (term750 w y x z) = (term764 w y x z).
Proof. exact (TRANS (@lem2421047 w y x z) (@lem2421190 w y x z)). Qed.
Lemma lem2421192 : term206 = term206.
Proof. exact (eq_refl term206). Qed.
Lemma lem2421193 (w : int) (y : int) (x : int) (z : int) : (term749 w y x z) = (term765 w y x z).
Proof. exact (MK_COMB (@lem2421192) (@lem2421191 w y x z)). Qed.
Lemma lem2421194 (w : int) (y : int) (x : int) (z : int) : (term765 w y x z) = (term764 w y x z).
Proof. exact (@lem1982721 (term764 w y x z)). Qed.
Lemma lem2421195 (w : int) (y : int) (x : int) (z : int) : (term749 w y x z) = (term764 w y x z).
Proof. exact (TRANS (@lem2421193 w y x z) (@lem2421194 w y x z)). Qed.
Lemma lem2421196 (w : int) (y : int) (x : int) (z : int) : (term748 w y x z) = (term764 w y x z).
Proof. exact (TRANS (@lem2421046 w y x z) (@lem2421195 w y x z)). Qed.
Lemma lem2421197 (w : int) (y : int) (x : int) (z : int) : (term798 w z x y) = (term764 w y x z).
Proof. exact (TRANS (@lem2421045 w y x z) (@lem2421196 w y x z)). Qed.
Lemma lem2421198 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2421199 (w : int) (y : int) (x : int) (z : int) : (term799 w z x y) = (term767 w y x z).
Proof. exact (MK_COMB (@lem2421198) (@lem2421197 w y x z)). Qed.
Lemma lem2421200 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2421201 (w : int) (y : int) (x : int) (z : int) : (term797 w z x y) = (term768 w y x z).
Proof. exact (MK_COMB (@lem2421199 w y x z) (@lem2421200)). Qed.
Lemma lem2421202 (w : int) (y : int) (x : int) (z : int) : (term330 w z x y) = (term768 w y x z).
Proof. exact (TRANS (@lem2420960 w z x y) (@lem2421201 w y x z)). Qed.
Lemma lem2421203 (w : int) (z : int) (x : int) (y : int) : (term335 w z x y) = (term800 w z x y).
Proof. exact (@lem1988287 (term287 w z x y) term207). Qed.
Lemma lem2421210 : term207 = term192.
Proof. exact (@lem1982721 term192). Qed.
Lemma lem2421252 (w : int) (z : int) (x : int) (y : int) : (term287 w z x y) = (term700 w z x y).
Proof. exact (@lem1982792 (term284 w y x z) (term284 w z x y)). Qed.
Lemma lem2421259 (w : int) (z : int) (x : int) (y : int) : (term701 w z x y) = (term702 w z x y).
Proof. exact (@lem1982781 (term177 w z) term546 (term177 x y)). Qed.
Lemma lem2421260 (w : int) (y : int) (x : int) (z : int) : (term703 w y x z) = (term703 w y x z).
Proof. exact (eq_refl (term703 w y x z)). Qed.
Lemma lem2421261 (w : int) (z : int) (x : int) (y : int) : (term700 w z x y) = (term704 w z x y).
Proof. exact (MK_COMB (@lem2421260 w y x z) (@lem2421259 w z x y)). Qed.
Lemma lem2421262 (w : int) (z : int) (x : int) (y : int) : (term704 w z x y) = (term705 w z x y).
Proof. exact (@lem1982755 (term177 w y) (term177 x z) (term702 w z x y)). Qed.
Lemma lem2421263 (w : int) (z : int) (x : int) (y : int) : (term706 w z x y) = (term707 w z x y).
Proof. exact (@lem1982757 (term708 w z) (term177 x z) (term708 x y)). Qed.
Lemma lem2421264 (y : int) (x : int) (z : int) : (term709 z x y) = (term710 y x z).
Proof. exact (@lem1982761 (term708 x y) (term177 x z)). Qed.
Lemma lem2421265 (w : int) (z : int) : (term711 w z) = (term711 w z).
Proof. exact (eq_refl (term711 w z)). Qed.
Lemma lem2421266 (w : int) (y : int) (x : int) (z : int) : (term707 w z x y) = (term712 w y x z).
Proof. exact (MK_COMB (@lem2421265 w z) (@lem2421264 y x z)). Qed.
Lemma lem2421267 (w : int) (y : int) (x : int) (z : int) : (term706 w z x y) = (term712 w y x z).
Proof. exact (TRANS (@lem2421263 w z x y) (@lem2421266 w y x z)). Qed.
Lemma lem2421268 (w : int) (y : int) : (term283 w y) = (term283 w y).
Proof. exact (eq_refl (term283 w y)). Qed.
Lemma lem2421269 (w : int) (y : int) (x : int) (z : int) : (term705 w z x y) = (term713 w y x z).
Proof. exact (MK_COMB (@lem2421268 w y) (@lem2421267 w y x z)). Qed.
Lemma lem2421270 (w : int) (y : int) (x : int) (z : int) : (term704 w z x y) = (term713 w y x z).
Proof. exact (TRANS (@lem2421262 w z x y) (@lem2421269 w y x z)). Qed.
Lemma lem2421271 (w : int) (y : int) (x : int) (z : int) : (term700 w z x y) = (term713 w y x z).
Proof. exact (TRANS (@lem2421261 w z x y) (@lem2421270 w y x z)). Qed.
Lemma lem2421273 (w : int) (y : int) (x : int) (z : int) : (term287 w z x y) = (term713 w y x z).
Proof. exact (TRANS (@lem2421252 w z x y) (@lem2421271 w y x z)). Qed.
Lemma lem2421274 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2421275 (w : int) (y : int) (x : int) (z : int) : (term714 w z x y) = (term715 w y x z).
Proof. exact (MK_COMB (@lem2421274) (@lem2421273 w y x z)). Qed.
Lemma lem2421276 (w : int) (y : int) (x : int) (z : int) : (term801 w z x y) = (term772 w y x z).
Proof. exact (MK_COMB (@lem2421275 w y x z) (@lem2421210)). Qed.
Lemma lem2421277 (w : int) (y : int) (x : int) (z : int) : (term772 w y x z) = (term773 w y x z).
Proof. exact (@lem1982792 (term713 w y x z) term192). Qed.
Lemma lem2421279 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2421280 : term192 = term567.
Proof. exact (@lem2421279 term193). Qed.
Lemma lem2421282 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2421283 : term546 = term547.
Proof. exact (@lem2421282 term193). Qed.
Lemma lem2421284 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2421285 : term548 = term549.
Proof. exact (MK_COMB (@lem2421284) (@lem2421283)). Qed.
Lemma lem2421286 : term568 = term569.
Proof. exact (MK_COMB (@lem2421285) (@lem2421280)). Qed.
Lemma lem2421287 : term569 = term570.
Proof. exact (@lem1981613 term546 term192 term192 term192). Qed.
Lemma lem2421289 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2421290 : term555 = term556.
Proof. exact (@lem2421289 term193 term193). Qed.
Lemma lem2421291 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2421292 : term558 = term193.
Proof. exact (EQ_MP (@lem2421291) (@lem940073)). Qed.
Lemma lem2421293 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2421294 : term556 = term192.
Proof. exact (MK_COMB (@lem2421293) (@lem2421292)). Qed.
Lemma lem2421295 : term555 = term192.
Proof. exact (TRANS (@lem2421290) (@lem2421294)). Qed.
Lemma lem2421297 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2421298 : term568 = term573.
Proof. exact (@lem2421297 term193 term193). Qed.
Lemma lem2421299 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2421300 : term558 = term193.
Proof. exact (EQ_MP (@lem2421299) (@lem940073)). Qed.
Lemma lem2421301 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2421302 : term556 = term192.
Proof. exact (MK_COMB (@lem2421301) (@lem2421300)). Qed.
Lemma lem2421303 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2421304 : term573 = term546.
Proof. exact (MK_COMB (@lem2421303) (@lem2421302)). Qed.
Lemma lem2421305 : term568 = term546.
Proof. exact (TRANS (@lem2421298) (@lem2421304)). Qed.
Lemma lem2421306 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2421307 : term574 = term575.
Proof. exact (MK_COMB (@lem2421306) (@lem2421305)). Qed.
Lemma lem2421308 : term570 = term547.
Proof. exact (MK_COMB (@lem2421307) (@lem2421295)). Qed.
Lemma lem2421309 : term569 = term547.
Proof. exact (TRANS (@lem2421287) (@lem2421308)). Qed.
Lemma lem2421310 : term568 = term547.
Proof. exact (TRANS (@lem2421286) (@lem2421309)). Qed.
Lemma lem2421312 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2421313 : term547 = term546.
Proof. exact (@lem2421312 term546). Qed.
Lemma lem2421314 : term568 = term546.
Proof. exact (TRANS (@lem2421310) (@lem2421313)). Qed.
Lemma lem2421315 (w : int) (y : int) (x : int) (z : int) : (term718 w y x z) = (term718 w y x z).
Proof. exact (eq_refl (term718 w y x z)). Qed.
Lemma lem2421316 (w : int) (y : int) (x : int) (z : int) : (term773 w y x z) = (term774 w y x z).
Proof. exact (MK_COMB (@lem2421315 w y x z) (@lem2421314)). Qed.
Lemma lem2421317 (w : int) (y : int) (x : int) (z : int) : (term774 w y x z) = (term775 w y x z).
Proof. exact (@lem1982755 (term177 w y) (term712 w y x z) term546). Qed.
Lemma lem2421318 (w : int) (y : int) (x : int) (z : int) : (term776 w y x z) = (term777 w y x z).
Proof. exact (@lem1982755 (term708 w z) (term710 y x z) term546). Qed.
Lemma lem2421323 (y : int) (x : int) (z : int) : (term778 y x z) = (term779 y x z).
Proof. exact (@lem1982755 (term708 x y) (term177 x z) term546). Qed.
Lemma lem2421324 (w : int) (z : int) : (term711 w z) = (term711 w z).
Proof. exact (eq_refl (term711 w z)). Qed.
Lemma lem2421325 (w : int) (y : int) (x : int) (z : int) : (term777 w y x z) = (term780 w y x z).
Proof. exact (MK_COMB (@lem2421324 w z) (@lem2421323 y x z)). Qed.
Lemma lem2421326 (w : int) (y : int) (x : int) (z : int) : (term776 w y x z) = (term780 w y x z).
Proof. exact (TRANS (@lem2421318 w y x z) (@lem2421325 w y x z)). Qed.
Lemma lem2421327 (w : int) (y : int) : (term283 w y) = (term283 w y).
Proof. exact (eq_refl (term283 w y)). Qed.
Lemma lem2421328 (w : int) (y : int) (x : int) (z : int) : (term775 w y x z) = (term781 w y x z).
Proof. exact (MK_COMB (@lem2421327 w y) (@lem2421326 w y x z)). Qed.
Lemma lem2421329 (w : int) (y : int) (x : int) (z : int) : (term774 w y x z) = (term781 w y x z).
Proof. exact (TRANS (@lem2421317 w y x z) (@lem2421328 w y x z)). Qed.
Lemma lem2421330 (w : int) (y : int) (x : int) (z : int) : (term773 w y x z) = (term781 w y x z).
Proof. exact (TRANS (@lem2421316 w y x z) (@lem2421329 w y x z)). Qed.
Lemma lem2421331 (w : int) (y : int) (x : int) (z : int) : (term772 w y x z) = (term781 w y x z).
Proof. exact (TRANS (@lem2421277 w y x z) (@lem2421330 w y x z)). Qed.
Lemma lem2421332 (w : int) (y : int) (x : int) (z : int) : (term801 w z x y) = (term781 w y x z).
Proof. exact (TRANS (@lem2421276 w y x z) (@lem2421331 w y x z)). Qed.
Lemma lem2421333 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2421334 (w : int) (y : int) (x : int) (z : int) : (term802 w z x y) = (term783 w y x z).
Proof. exact (MK_COMB (@lem2421333) (@lem2421332 w y x z)). Qed.
Lemma lem2421335 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2421336 (w : int) (y : int) (x : int) (z : int) : (term800 w z x y) = (term784 w y x z).
Proof. exact (MK_COMB (@lem2421334 w y x z) (@lem2421335)). Qed.
Lemma lem2421337 (w : int) (y : int) (x : int) (z : int) : (term335 w z x y) = (term784 w y x z).
Proof. exact (TRANS (@lem2421203 w z x y) (@lem2421336 w y x z)). Qed.
Lemma lem2421338 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421339 (w : int) (y : int) (x : int) (z : int) : (term332 w z x y) = (term785 w y x z).
Proof. exact (MK_COMB (@lem2421338) (@lem2421202 w y x z)). Qed.
Lemma lem2421340 (w : int) (y : int) (x : int) (z : int) : (term336 w z x y) = (term786 w y x z).
Proof. exact (MK_COMB (@lem2421339 w y x z) (@lem2421337 w y x z)). Qed.
Lemma lem2421341 (w : int) (x : int) (y : int) (z : int) : ((term301 w x y z) = term182) = ((term803 w x y z) = term182).
Proof. exact (@lem1988293 (term301 w x y z) term182). Qed.
Lemma lem2421342 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2421355 (y : int) (z : int) : (term173 y z) = (term620 y z).
Proof. exact (@lem1982792 (real_of_int y) (real_of_int z)). Qed.
Lemma lem2421368 (w : int) (x : int) : (term173 w x) = (term620 w x).
Proof. exact (@lem1982792 (real_of_int w) (real_of_int x)). Qed.
Lemma lem2421369 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2421370 (w : int) (x : int) : (term300 w x) = (term723 w x).
Proof. exact (MK_COMB (@lem2421369) (@lem2421368 w x)). Qed.
Lemma lem2421371 (w : int) (x : int) (y : int) (z : int) : (term301 w x y z) = (term724 w x y z).
Proof. exact (MK_COMB (@lem2421370 w x) (@lem2421355 y z)). Qed.
Lemma lem2421372 (w : int) (x : int) (y : int) (z : int) : (term724 w x y z) = (term725 w x y z).
Proof. exact (@lem1982727 (real_of_int w) (term595 x) (term620 y z)). Qed.
Lemma lem2421373 (y : int) (w : int) (z : int) : (term726 w y z) = (term727 y w z).
Proof. exact (@lem1982781 (real_of_int y) (real_of_int w) (term595 z)). Qed.
Lemma lem2421378 (w : int) (z : int) : (term728 w z) = (term708 w z).
Proof. exact (@lem1982751 term546 (real_of_int w) (real_of_int z)). Qed.
Lemma lem2421381 (w : int) (y : int) : (term283 w y) = (term283 w y).
Proof. exact (eq_refl (term283 w y)). Qed.
Lemma lem2421382 (y : int) (w : int) (z : int) : (term727 y w z) = (term709 y w z).
Proof. exact (MK_COMB (@lem2421381 w y) (@lem2421378 w z)). Qed.
Lemma lem2421383 (y : int) (w : int) (z : int) : (term726 w y z) = (term709 y w z).
Proof. exact (TRANS (@lem2421373 y w z) (@lem2421382 y w z)). Qed.
Lemma lem2421384 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2421385 (y : int) (w : int) (z : int) : (term729 w y z) = (term730 y w z).
Proof. exact (MK_COMB (@lem2421384) (@lem2421383 y w z)). Qed.
Lemma lem2421386 (y : int) (x : int) (z : int) : (term731 x y z) = (term732 y x z).
Proof. exact (@lem1982781 (real_of_int y) (term595 x) (term595 z)). Qed.
Lemma lem2421387 (x : int) (z : int) : (term733 x z) = (term734 x z).
Proof. exact (@lem1982737 term546 term546 (real_of_int x) (real_of_int z)). Qed.
Lemma lem2421389 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2421390 : term546 = term547.
Proof. exact (@lem2421389 term193). Qed.
Lemma lem2421392 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2421393 : term546 = term547.
Proof. exact (@lem2421392 term193). Qed.
Lemma lem2421394 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2421395 : term548 = term549.
Proof. exact (MK_COMB (@lem2421394) (@lem2421393)). Qed.
Lemma lem2421396 : term643 = term644.
Proof. exact (MK_COMB (@lem2421395) (@lem2421390)). Qed.
Lemma lem2421397 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2421399 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2421400 : term555 = term556.
Proof. exact (@lem2421399 term193 term193). Qed.
Lemma lem2421401 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2421402 : term558 = term193.
Proof. exact (EQ_MP (@lem2421401) (@lem940073)). Qed.
Lemma lem2421403 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2421404 : term556 = term192.
Proof. exact (MK_COMB (@lem2421403) (@lem2421402)). Qed.
Lemma lem2421405 : term555 = term192.
Proof. exact (TRANS (@lem2421400) (@lem2421404)). Qed.
Lemma lem2421407 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2421408 : term643 = term556.
Proof. exact (@lem2421407 term193 term193). Qed.
Lemma lem2421409 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2421410 : term558 = term193.
Proof. exact (EQ_MP (@lem2421409) (@lem940073)). Qed.
Lemma lem2421411 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2421412 : term556 = term192.
Proof. exact (MK_COMB (@lem2421411) (@lem2421410)). Qed.
Lemma lem2421413 : term643 = term192.
Proof. exact (TRANS (@lem2421408) (@lem2421412)). Qed.
Lemma lem2421414 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2421415 : term647 = term648.
Proof. exact (MK_COMB (@lem2421414) (@lem2421413)). Qed.
Lemma lem2421416 : term645 = term567.
Proof. exact (MK_COMB (@lem2421415) (@lem2421405)). Qed.
Lemma lem2421417 : term644 = term567.
Proof. exact (TRANS (@lem2421397) (@lem2421416)). Qed.
Lemma lem2421418 : term643 = term567.
Proof. exact (TRANS (@lem2421396) (@lem2421417)). Qed.
Lemma lem2421420 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2421421 : term567 = term192.
Proof. exact (@lem2421420 term192). Qed.
Lemma lem2421422 : term643 = term192.
Proof. exact (TRANS (@lem2421418) (@lem2421421)). Qed.
Lemma lem2421423 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2421424 : term649 = term650.
Proof. exact (MK_COMB (@lem2421423) (@lem2421422)). Qed.
Lemma lem2421425 (x : int) (z : int) : (term177 x z) = (term177 x z).
Proof. exact (eq_refl (term177 x z)). Qed.
Lemma lem2421426 (x : int) (z : int) : (term734 x z) = (term735 x z).
Proof. exact (MK_COMB (@lem2421424) (@lem2421425 x z)). Qed.
Lemma lem2421431 (x : int) (z : int) : (term733 x z) = (term735 x z).
Proof. exact (TRANS (@lem2421387 x z) (@lem2421426 x z)). Qed.
Lemma lem2421432 (x : int) (z : int) : (term735 x z) = (term177 x z).
Proof. exact (@lem1982709 (term177 x z)). Qed.
Lemma lem2421433 (x : int) (z : int) : (term733 x z) = (term177 x z).
Proof. exact (TRANS (@lem2421431 x z) (@lem2421432 x z)). Qed.
Lemma lem2421438 (x : int) (y : int) : (term736 x y) = (term708 x y).
Proof. exact (@lem1982745 term546 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2421439 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2421440 (x : int) (y : int) : (term737 x y) = (term711 x y).
Proof. exact (MK_COMB (@lem2421439) (@lem2421438 x y)). Qed.
Lemma lem2421441 (y : int) (x : int) (z : int) : (term732 y x z) = (term710 y x z).
Proof. exact (MK_COMB (@lem2421440 x y) (@lem2421433 x z)). Qed.
Lemma lem2421442 (y : int) (x : int) (z : int) : (term731 x y z) = (term710 y x z).
Proof. exact (TRANS (@lem2421386 y x z) (@lem2421441 y x z)). Qed.
Lemma lem2421443 (w : int) (y : int) (x : int) (z : int) : (term725 w x y z) = (term738 w y x z).
Proof. exact (MK_COMB (@lem2421385 y w z) (@lem2421442 y x z)). Qed.
Lemma lem2421444 (w : int) (y : int) (x : int) (z : int) : (term724 w x y z) = (term738 w y x z).
Proof. exact (TRANS (@lem2421372 w x y z) (@lem2421443 w y x z)). Qed.
Lemma lem2421449 (w : int) (y : int) (x : int) (z : int) : (term738 w y x z) = (term713 w y x z).
Proof. exact (@lem1982755 (term177 w y) (term708 w z) (term710 y x z)). Qed.
Lemma lem2421450 (w : int) (y : int) (x : int) (z : int) : (term724 w x y z) = (term713 w y x z).
Proof. exact (TRANS (@lem2421444 w y x z) (@lem2421449 w y x z)). Qed.
Lemma lem2421451 (w : int) (y : int) (x : int) (z : int) : (term301 w x y z) = (term713 w y x z).
Proof. exact (TRANS (@lem2421371 w x y z) (@lem2421450 w y x z)). Qed.
Lemma lem2421452 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2421453 (w : int) (y : int) (x : int) (z : int) : (term770 w x y z) = (term715 w y x z).
Proof. exact (MK_COMB (@lem2421452) (@lem2421451 w y x z)). Qed.
Lemma lem2421454 (w : int) (y : int) (x : int) (z : int) : (term803 w x y z) = (term716 w y x z).
Proof. exact (MK_COMB (@lem2421453 w y x z) (@lem2421342)). Qed.
Lemma lem2421455 (w : int) (y : int) (x : int) (z : int) : (term716 w y x z) = (term717 w y x z).
Proof. exact (@lem1982792 (term713 w y x z) term182). Qed.
Lemma lem2421457 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2421458 : term182 = term543.
Proof. exact (@lem2421457 (NUMERAL 0)). Qed.
Lemma lem2421460 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2421461 : term546 = term547.
Proof. exact (@lem2421460 term193). Qed.
Lemma lem2421462 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2421463 : term548 = term549.
Proof. exact (MK_COMB (@lem2421462) (@lem2421461)). Qed.
Lemma lem2421464 : term550 = term551.
Proof. exact (MK_COMB (@lem2421463) (@lem2421458)). Qed.
Lemma lem2421465 : term551 = term552.
Proof. exact (@lem1981613 term546 term182 term192 term192). Qed.
Lemma lem2421467 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2421468 : term555 = term556.
Proof. exact (@lem2421467 term193 term193). Qed.
Lemma lem2421469 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2421470 : term558 = term193.
Proof. exact (EQ_MP (@lem2421469) (@lem940073)). Qed.
Lemma lem2421471 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2421472 : term556 = term192.
Proof. exact (MK_COMB (@lem2421471) (@lem2421470)). Qed.
Lemma lem2421473 : term555 = term192.
Proof. exact (TRANS (@lem2421468) (@lem2421472)). Qed.
Lemma lem2421475 (x : nat) : (term559 x) = term182.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2421476 : term550 = term182.
Proof. exact (@lem2421475 term193). Qed.
Lemma lem2421477 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2421478 : term560 = term561.
Proof. exact (MK_COMB (@lem2421477) (@lem2421476)). Qed.
Lemma lem2421479 : term552 = term543.
Proof. exact (MK_COMB (@lem2421478) (@lem2421473)). Qed.
Lemma lem2421480 : term551 = term543.
Proof. exact (TRANS (@lem2421465) (@lem2421479)). Qed.
Lemma lem2421481 : term550 = term543.
Proof. exact (TRANS (@lem2421464) (@lem2421480)). Qed.
Lemma lem2421483 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2421484 : term543 = term182.
Proof. exact (@lem2421483 term182). Qed.
Lemma lem2421485 : term550 = term182.
Proof. exact (TRANS (@lem2421481) (@lem2421484)). Qed.
Lemma lem2421486 (w : int) (y : int) (x : int) (z : int) : (term718 w y x z) = (term718 w y x z).
Proof. exact (eq_refl (term718 w y x z)). Qed.
Lemma lem2421487 (w : int) (y : int) (x : int) (z : int) : (term717 w y x z) = (term719 w y x z).
Proof. exact (MK_COMB (@lem2421486 w y x z) (@lem2421485)). Qed.
Lemma lem2421488 (w : int) (y : int) (x : int) (z : int) : (term719 w y x z) = (term713 w y x z).
Proof. exact (@lem1982723 (term713 w y x z)). Qed.
Lemma lem2421489 (w : int) (y : int) (x : int) (z : int) : (term717 w y x z) = (term713 w y x z).
Proof. exact (TRANS (@lem2421487 w y x z) (@lem2421488 w y x z)). Qed.
Lemma lem2421490 (w : int) (y : int) (x : int) (z : int) : (term716 w y x z) = (term713 w y x z).
Proof. exact (TRANS (@lem2421455 w y x z) (@lem2421489 w y x z)). Qed.
Lemma lem2421491 (w : int) (y : int) (x : int) (z : int) : (term803 w x y z) = (term713 w y x z).
Proof. exact (TRANS (@lem2421454 w y x z) (@lem2421490 w y x z)). Qed.
Lemma lem2421492 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2421493 (w : int) (y : int) (x : int) (z : int) : (term804 w x y z) = (term721 w y x z).
Proof. exact (MK_COMB (@lem2421492) (@lem2421491 w y x z)). Qed.
Lemma lem2421494 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2421495 (w : int) (y : int) (x : int) (z : int) : ((term803 w x y z) = term182) = ((term713 w y x z) = term182).
Proof. exact (MK_COMB (@lem2421493 w y x z) (@lem2421494)). Qed.
Lemma lem2421496 (w : int) (y : int) (x : int) (z : int) : ((term301 w x y z) = term182) = ((term713 w y x z) = term182).
Proof. exact (TRANS (@lem2421341 w x y z) (@lem2421495 w y x z)). Qed.
Lemma lem2421497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2421498 (w : int) (y : int) (x : int) (z : int) : (term340 w z x y) = (term805 w y x z).
Proof. exact (MK_COMB (@lem2421497) (@lem2421340 w y x z)). Qed.
Lemma lem2421499 (w : int) (y : int) (x : int) (z : int) : (term342 w x y z) = (term806 w y x z).
Proof. exact (MK_COMB (@lem2421498 w y x z) (@lem2421496 w y x z)). Qed.
Lemma lem2421500 (w : int) (y : int) (x : int) : (term453 w x y) = (term807 w y x).
Proof. exact (fun_ext (fun z : int => @lem2421499 w y x z)). Qed.
Lemma lem2421501 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421502 (w : int) (y : int) (x : int) : (term468 w x y) = (term808 w y x).
Proof. exact (MK_COMB (@lem2421501) (@lem2421500 w y x)). Qed.
Lemma lem2421503 (w : int) (x : int) : (term475 w x) = (term809 w x).
Proof. exact (fun_ext (fun y : int => @lem2421502 w y x)). Qed.
Lemma lem2421504 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421505 (w : int) (x : int) : (term490 w x) = (term810 w x).
Proof. exact (MK_COMB (@lem2421504) (@lem2421503 w x)). Qed.
Lemma lem2421506 (w : int) : (term497 w) = (term811 w).
Proof. exact (fun_ext (fun x : int => @lem2421505 w x)). Qed.
Lemma lem2421507 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421508 (w : int) : (term512 w) = (term812 w).
Proof. exact (MK_COMB (@lem2421507) (@lem2421506 w)). Qed.
Lemma lem2421509 : term519 = term813.
Proof. exact (fun_ext (fun w : int => @lem2421508 w)). Qed.
Lemma lem2421510 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421511 : term534 = term814.
Proof. exact (MK_COMB (@lem2421510) (@lem2421509)). Qed.
Lemma lem2421512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421513 : term531 = term815.
Proof. exact (MK_COMB (@lem2421512) (@lem2420959)). Qed.
Lemma lem2421514 : term535 = term816.
Proof. exact (MK_COMB (@lem2421513) (@lem2421511)). Qed.
Lemma lem2421515 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421516 : term449 = term817.
Proof. exact (MK_COMB (@lem2421515) (@lem2420361)). Qed.
Lemma lem2421517 : term536 = term818.
Proof. exact (MK_COMB (@lem2421516) (@lem2421514)). Qed.
Lemma lem2421518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421519 : term384 = term819.
Proof. exact (MK_COMB (@lem2421518) (@lem2419399)). Qed.
Lemma lem2421520 : term537 = term820.
Proof. exact (MK_COMB (@lem2421519) (@lem2421517)). Qed.
Lemma lem2421521 : term359 = term820.
Proof. exact (TRANS (@lem2419174) (@lem2421520)). Qed.
Lemma lem2421523 {A : Type'} (t : Prop) : (term821 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2421524 (t : Prop) : (term822 t) = t.
Proof. exact (@lem2421523 int t). Qed.
Lemma lem2421525 : term581 = term579.
Proof. exact (@lem2421524 term579). Qed.
Lemma lem2421526 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421527 : term586 = term823.
Proof. exact (MK_COMB (@lem2421526) (@lem2421525)). Qed.
Lemma lem2421529 {A : Type'} (t : Prop) : (term821 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2421530 (t : Prop) : (term822 t) = t.
Proof. exact (@lem2421529 int t). Qed.
Lemma lem2421531 : term581 = term579.
Proof. exact (@lem2421530 term579). Qed.
Lemma lem2421532 : term587 = term824.
Proof. exact (MK_COMB (@lem2421527) (@lem2421531)). Qed.
Lemma lem2421533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421534 : term819 = term825.
Proof. exact (MK_COMB (@lem2421533) (@lem2421532)). Qed.
Lemma lem2421536 {A : Type'} (t : Prop) : (term821 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2421537 (t : Prop) : (term822 t) = t.
Proof. exact (@lem2421536 int t). Qed.
Lemma lem2421538 : term680 = term678.
Proof. exact (@lem2421537 term678). Qed.
Lemma lem2421591 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421592 : term697 = term826.
Proof. exact (MK_COMB (@lem2421591) (@lem2421538)). Qed.
Lemma lem2421594 {A : Type'} (t : Prop) : (term821 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2421595 (t : Prop) : (term822 t) = t.
Proof. exact (@lem2421594 int t). Qed.
Lemma lem2421596 : term696 = term694.
Proof. exact (@lem2421595 term694). Qed.
Lemma lem2421649 : term698 = term827.
Proof. exact (MK_COMB (@lem2421592) (@lem2421596)). Qed.
Lemma lem2421650 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421651 : term817 = term828.
Proof. exact (MK_COMB (@lem2421650) (@lem2421649)). Qed.
Lemma lem2421772 : term816 = term816.
Proof. exact (eq_refl term816). Qed.
Lemma lem2421773 : term818 = term829.
Proof. exact (MK_COMB (@lem2421651) (@lem2421772)). Qed.
Lemma lem2421774 : term820 = term830.
Proof. exact (MK_COMB (@lem2421534) (@lem2421773)). Qed.
Lemma lem2421776 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term361 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2421777 (P : int -> Prop) (Q : int -> Prop) : (term363 P Q) = (term362 P Q).
Proof. exact (@lem2421776 int P Q). Qed.
Lemma lem2421778 : term831 = term832.
Proof. exact (@lem2421777 term677 term693). Qed.
Lemma lem2421779 (y : int) : (term833 y) = (term676 y).
Proof. exact (eq_refl (term833 y)). Qed.
Lemma lem2421780 : term834 = term677.
Proof. exact (fun_ext (fun y : int => @lem2421779 y)). Qed.
Lemma lem2421781 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421782 : term835 = term678.
Proof. exact (MK_COMB (@lem2421781) (@lem2421780)). Qed.
Lemma lem2421783 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421784 : term836 = term826.
Proof. exact (MK_COMB (@lem2421783) (@lem2421782)). Qed.
Lemma lem2421785 (y : int) : (term837 y) = (term692 y).
Proof. exact (eq_refl (term837 y)). Qed.
Lemma lem2421786 : term838 = term693.
Proof. exact (fun_ext (fun y : int => @lem2421785 y)). Qed.
Lemma lem2421787 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421788 : term839 = term694.
Proof. exact (MK_COMB (@lem2421787) (@lem2421786)). Qed.
Lemma lem2421789 : term831 = term827.
Proof. exact (MK_COMB (@lem2421784) (@lem2421788)). Qed.
Lemma lem2421790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2421791 : term840 = term841.
Proof. exact (MK_COMB (@lem2421790) (@lem2421789)). Qed.
Lemma lem2421792 (y : int) : (term833 y) = (term676 y).
Proof. exact (eq_refl (term833 y)). Qed.
Lemma lem2421793 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421794 (y : int) : (term842 y) = (term843 y).
Proof. exact (MK_COMB (@lem2421793) (@lem2421792 y)). Qed.
Lemma lem2421795 (y : int) : (term837 y) = (term692 y).
Proof. exact (eq_refl (term837 y)). Qed.
Lemma lem2421796 (y : int) : (term844 y) = (term845 y).
Proof. exact (MK_COMB (@lem2421794 y) (@lem2421795 y)). Qed.
Lemma lem2421797 : term846 = term847.
Proof. exact (fun_ext (fun y : int => @lem2421796 y)). Qed.
Lemma lem2421798 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421799 : term832 = term848.
Proof. exact (MK_COMB (@lem2421798) (@lem2421797)). Qed.
Lemma lem2421800 : (term831 = term832) = (term827 = term848).
Proof. exact (MK_COMB (@lem2421791) (@lem2421799)). Qed.
Lemma lem2421801 : term827 = term848.
Proof. exact (EQ_MP (@lem2421800) (@lem2421778)). Qed.
Lemma lem2421803 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term361 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2421804 (P : int -> Prop) (Q : int -> Prop) : (term363 P Q) = (term362 P Q).
Proof. exact (@lem2421803 int P Q). Qed.
Lemma lem2421805 (y : int) : (term849 y) = (term850 y).
Proof. exact (@lem2421804 (term675 y) (term691 y)). Qed.
Lemma lem2421806 (y : int) (z : int) : (term851 y z) = (term674 y z).
Proof. exact (eq_refl (term851 y z)). Qed.
Lemma lem2421807 (y : int) : (term852 y) = (term675 y).
Proof. exact (fun_ext (fun z : int => @lem2421806 y z)). Qed.
Lemma lem2421808 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421809 (y : int) : (term853 y) = (term676 y).
Proof. exact (MK_COMB (@lem2421808) (@lem2421807 y)). Qed.
Lemma lem2421810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421811 (y : int) : (term854 y) = (term843 y).
Proof. exact (MK_COMB (@lem2421810) (@lem2421809 y)). Qed.
Lemma lem2421812 (y : int) (z : int) : (term855 y z) = (term690 y z).
Proof. exact (eq_refl (term855 y z)). Qed.
Lemma lem2421813 (y : int) : (term856 y) = (term691 y).
Proof. exact (fun_ext (fun z : int => @lem2421812 y z)). Qed.
Lemma lem2421814 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421815 (y : int) : (term857 y) = (term692 y).
Proof. exact (MK_COMB (@lem2421814) (@lem2421813 y)). Qed.
Lemma lem2421816 (y : int) : (term849 y) = (term845 y).
Proof. exact (MK_COMB (@lem2421811 y) (@lem2421815 y)). Qed.
Lemma lem2421817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2421818 (y : int) : (term858 y) = (term859 y).
Proof. exact (MK_COMB (@lem2421817) (@lem2421816 y)). Qed.
Lemma lem2421819 (y : int) (z : int) : (term851 y z) = (term674 y z).
Proof. exact (eq_refl (term851 y z)). Qed.
Lemma lem2421820 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421821 (y : int) (z : int) : (term860 y z) = (term861 y z).
Proof. exact (MK_COMB (@lem2421820) (@lem2421819 y z)). Qed.
Lemma lem2421822 (y : int) (z : int) : (term855 y z) = (term690 y z).
Proof. exact (eq_refl (term855 y z)). Qed.
Lemma lem2421823 (y : int) (z : int) : (term862 y z) = (term863 y z).
Proof. exact (MK_COMB (@lem2421821 y z) (@lem2421822 y z)). Qed.
Lemma lem2421824 (y : int) : (term864 y) = (term865 y).
Proof. exact (fun_ext (fun z : int => @lem2421823 y z)). Qed.
Lemma lem2421825 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421826 (y : int) : (term850 y) = (term866 y).
Proof. exact (MK_COMB (@lem2421825) (@lem2421824 y)). Qed.
Lemma lem2421827 (y : int) : ((term849 y) = (term850 y)) = ((term845 y) = (term866 y)).
Proof. exact (MK_COMB (@lem2421818 y) (@lem2421826 y)). Qed.
Lemma lem2421828 (y : int) : (term845 y) = (term866 y).
Proof. exact (EQ_MP (@lem2421827 y) (@lem2421805 y)). Qed.
Lemma lem2421829 : term847 = term867.
Proof. exact (fun_ext (fun y : int => @lem2421828 y)). Qed.
Lemma lem2421830 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421831 : term848 = term868.
Proof. exact (MK_COMB (@lem2421830) (@lem2421829)). Qed.
Lemma lem2421832 : term827 = term868.
Proof. exact (TRANS (@lem2421801) (@lem2421831)). Qed.
Lemma lem2421833 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421834 : term828 = term869.
Proof. exact (MK_COMB (@lem2421833) (@lem2421832)). Qed.
Lemma lem2421836 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term361 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2421837 (P : int -> Prop) (Q : int -> Prop) : (term363 P Q) = (term362 P Q).
Proof. exact (@lem2421836 int P Q). Qed.
Lemma lem2421838 : term870 = term871.
Proof. exact (@lem2421837 term795 term813). Qed.
Lemma lem2421839 (w : int) : (term872 w) = (term794 w).
Proof. exact (eq_refl (term872 w)). Qed.
Lemma lem2421840 : term873 = term795.
Proof. exact (fun_ext (fun w : int => @lem2421839 w)). Qed.
Lemma lem2421841 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421842 : term874 = term796.
Proof. exact (MK_COMB (@lem2421841) (@lem2421840)). Qed.
Lemma lem2421843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421844 : term875 = term815.
Proof. exact (MK_COMB (@lem2421843) (@lem2421842)). Qed.
Lemma lem2421845 (w : int) : (term876 w) = (term812 w).
Proof. exact (eq_refl (term876 w)). Qed.
Lemma lem2421846 : term877 = term813.
Proof. exact (fun_ext (fun w : int => @lem2421845 w)). Qed.
Lemma lem2421847 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421848 : term878 = term814.
Proof. exact (MK_COMB (@lem2421847) (@lem2421846)). Qed.
Lemma lem2421849 : term870 = term816.
Proof. exact (MK_COMB (@lem2421844) (@lem2421848)). Qed.
Lemma lem2421850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2421851 : term879 = term880.
Proof. exact (MK_COMB (@lem2421850) (@lem2421849)). Qed.
Lemma lem2421852 (w : int) : (term872 w) = (term794 w).
Proof. exact (eq_refl (term872 w)). Qed.
Lemma lem2421853 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421854 (w : int) : (term881 w) = (term882 w).
Proof. exact (MK_COMB (@lem2421853) (@lem2421852 w)). Qed.
Lemma lem2421855 (w : int) : (term876 w) = (term812 w).
Proof. exact (eq_refl (term876 w)). Qed.
Lemma lem2421856 (w : int) : (term883 w) = (term884 w).
Proof. exact (MK_COMB (@lem2421854 w) (@lem2421855 w)). Qed.
Lemma lem2421857 : term885 = term886.
Proof. exact (fun_ext (fun w : int => @lem2421856 w)). Qed.
Lemma lem2421858 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421859 : term871 = term887.
Proof. exact (MK_COMB (@lem2421858) (@lem2421857)). Qed.
Lemma lem2421860 : (term870 = term871) = (term816 = term887).
Proof. exact (MK_COMB (@lem2421851) (@lem2421859)). Qed.
Lemma lem2421861 : term816 = term887.
Proof. exact (EQ_MP (@lem2421860) (@lem2421838)). Qed.
Lemma lem2421863 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term361 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2421864 (P : int -> Prop) (Q : int -> Prop) : (term363 P Q) = (term362 P Q).
Proof. exact (@lem2421863 int P Q). Qed.
Lemma lem2421865 (w : int) : (term888 w) = (term889 w).
Proof. exact (@lem2421864 (term793 w) (term811 w)). Qed.
Lemma lem2421866 (w : int) (x : int) : (term890 w x) = (term792 w x).
Proof. exact (eq_refl (term890 w x)). Qed.
Lemma lem2421867 (w : int) : (term891 w) = (term793 w).
Proof. exact (fun_ext (fun x : int => @lem2421866 w x)). Qed.
Lemma lem2421868 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421869 (w : int) : (term892 w) = (term794 w).
Proof. exact (MK_COMB (@lem2421868) (@lem2421867 w)). Qed.
Lemma lem2421870 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421871 (w : int) : (term893 w) = (term882 w).
Proof. exact (MK_COMB (@lem2421870) (@lem2421869 w)). Qed.
Lemma lem2421872 (w : int) (x : int) : (term894 w x) = (term810 w x).
Proof. exact (eq_refl (term894 w x)). Qed.
Lemma lem2421873 (w : int) : (term895 w) = (term811 w).
Proof. exact (fun_ext (fun x : int => @lem2421872 w x)). Qed.
Lemma lem2421874 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421875 (w : int) : (term896 w) = (term812 w).
Proof. exact (MK_COMB (@lem2421874) (@lem2421873 w)). Qed.
Lemma lem2421876 (w : int) : (term888 w) = (term884 w).
Proof. exact (MK_COMB (@lem2421871 w) (@lem2421875 w)). Qed.
Lemma lem2421877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2421878 (w : int) : (term897 w) = (term898 w).
Proof. exact (MK_COMB (@lem2421877) (@lem2421876 w)). Qed.
Lemma lem2421879 (w : int) (x : int) : (term890 w x) = (term792 w x).
Proof. exact (eq_refl (term890 w x)). Qed.
Lemma lem2421880 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421881 (w : int) (x : int) : (term899 w x) = (term900 w x).
Proof. exact (MK_COMB (@lem2421880) (@lem2421879 w x)). Qed.
Lemma lem2421882 (w : int) (x : int) : (term894 w x) = (term810 w x).
Proof. exact (eq_refl (term894 w x)). Qed.
Lemma lem2421883 (w : int) (x : int) : (term901 w x) = (term902 w x).
Proof. exact (MK_COMB (@lem2421881 w x) (@lem2421882 w x)). Qed.
Lemma lem2421884 (w : int) : (term903 w) = (term904 w).
Proof. exact (fun_ext (fun x : int => @lem2421883 w x)). Qed.
Lemma lem2421885 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421886 (w : int) : (term889 w) = (term905 w).
Proof. exact (MK_COMB (@lem2421885) (@lem2421884 w)). Qed.
Lemma lem2421887 (w : int) : ((term888 w) = (term889 w)) = ((term884 w) = (term905 w)).
Proof. exact (MK_COMB (@lem2421878 w) (@lem2421886 w)). Qed.
Lemma lem2421888 (w : int) : (term884 w) = (term905 w).
Proof. exact (EQ_MP (@lem2421887 w) (@lem2421865 w)). Qed.
Lemma lem2421890 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term361 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2421891 (P : int -> Prop) (Q : int -> Prop) : (term363 P Q) = (term362 P Q).
Proof. exact (@lem2421890 int P Q). Qed.
Lemma lem2421892 (w : int) (x : int) : (term906 w x) = (term907 w x).
Proof. exact (@lem2421891 (term791 w x) (term809 w x)). Qed.
Lemma lem2421893 (w : int) (y : int) (x : int) : (term908 w x y) = (term790 w y x).
Proof. exact (eq_refl (term908 w x y)). Qed.
Lemma lem2421894 (w : int) (x : int) : (term909 w x) = (term791 w x).
Proof. exact (fun_ext (fun y : int => @lem2421893 w y x)). Qed.
Lemma lem2421895 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421896 (w : int) (x : int) : (term910 w x) = (term792 w x).
Proof. exact (MK_COMB (@lem2421895) (@lem2421894 w x)). Qed.
Lemma lem2421897 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421898 (w : int) (x : int) : (term911 w x) = (term900 w x).
Proof. exact (MK_COMB (@lem2421897) (@lem2421896 w x)). Qed.
Lemma lem2421899 (w : int) (y : int) (x : int) : (term912 w x y) = (term808 w y x).
Proof. exact (eq_refl (term912 w x y)). Qed.
Lemma lem2421900 (w : int) (x : int) : (term913 w x) = (term809 w x).
Proof. exact (fun_ext (fun y : int => @lem2421899 w y x)). Qed.
Lemma lem2421901 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421902 (w : int) (x : int) : (term914 w x) = (term810 w x).
Proof. exact (MK_COMB (@lem2421901) (@lem2421900 w x)). Qed.
Lemma lem2421903 (w : int) (x : int) : (term906 w x) = (term902 w x).
Proof. exact (MK_COMB (@lem2421898 w x) (@lem2421902 w x)). Qed.
Lemma lem2421904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2421905 (w : int) (x : int) : (term915 w x) = (term916 w x).
Proof. exact (MK_COMB (@lem2421904) (@lem2421903 w x)). Qed.
Lemma lem2421906 (w : int) (y : int) (x : int) : (term908 w x y) = (term790 w y x).
Proof. exact (eq_refl (term908 w x y)). Qed.
Lemma lem2421907 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421908 (w : int) (y : int) (x : int) : (term917 w x y) = (term918 w y x).
Proof. exact (MK_COMB (@lem2421907) (@lem2421906 w y x)). Qed.
Lemma lem2421909 (w : int) (y : int) (x : int) : (term912 w x y) = (term808 w y x).
Proof. exact (eq_refl (term912 w x y)). Qed.
Lemma lem2421910 (w : int) (y : int) (x : int) : (term919 w x y) = (term920 w y x).
Proof. exact (MK_COMB (@lem2421908 w y x) (@lem2421909 w y x)). Qed.
Lemma lem2421911 (w : int) (x : int) : (term921 w x) = (term922 w x).
Proof. exact (fun_ext (fun y : int => @lem2421910 w y x)). Qed.
Lemma lem2421912 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421913 (w : int) (x : int) : (term907 w x) = (term923 w x).
Proof. exact (MK_COMB (@lem2421912) (@lem2421911 w x)). Qed.
Lemma lem2421914 (w : int) (x : int) : ((term906 w x) = (term907 w x)) = ((term902 w x) = (term923 w x)).
Proof. exact (MK_COMB (@lem2421905 w x) (@lem2421913 w x)). Qed.
Lemma lem2421915 (w : int) (x : int) : (term902 w x) = (term923 w x).
Proof. exact (EQ_MP (@lem2421914 w x) (@lem2421892 w x)). Qed.
Lemma lem2421917 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term361 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2421918 (P : int -> Prop) (Q : int -> Prop) : (term363 P Q) = (term362 P Q).
Proof. exact (@lem2421917 int P Q). Qed.
Lemma lem2421919 (w : int) (y : int) (x : int) : (term924 w y x) = (term925 w y x).
Proof. exact (@lem2421918 (term789 w y x) (term807 w y x)). Qed.
Lemma lem2421920 (w : int) (y : int) (x : int) (z : int) : (term926 w y x z) = (term788 w y x z).
Proof. exact (eq_refl (term926 w y x z)). Qed.
Lemma lem2421921 (w : int) (y : int) (x : int) : (term927 w y x) = (term789 w y x).
Proof. exact (fun_ext (fun z : int => @lem2421920 w y x z)). Qed.
Lemma lem2421922 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421923 (w : int) (y : int) (x : int) : (term928 w y x) = (term790 w y x).
Proof. exact (MK_COMB (@lem2421922) (@lem2421921 w y x)). Qed.
Lemma lem2421924 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421925 (w : int) (y : int) (x : int) : (term929 w y x) = (term918 w y x).
Proof. exact (MK_COMB (@lem2421924) (@lem2421923 w y x)). Qed.
Lemma lem2421926 (w : int) (y : int) (x : int) (z : int) : (term930 w y x z) = (term806 w y x z).
Proof. exact (eq_refl (term930 w y x z)). Qed.
Lemma lem2421927 (w : int) (y : int) (x : int) : (term931 w y x) = (term807 w y x).
Proof. exact (fun_ext (fun z : int => @lem2421926 w y x z)). Qed.
Lemma lem2421928 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421929 (w : int) (y : int) (x : int) : (term932 w y x) = (term808 w y x).
Proof. exact (MK_COMB (@lem2421928) (@lem2421927 w y x)). Qed.
Lemma lem2421930 (w : int) (y : int) (x : int) : (term924 w y x) = (term920 w y x).
Proof. exact (MK_COMB (@lem2421925 w y x) (@lem2421929 w y x)). Qed.
Lemma lem2421931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2421932 (w : int) (y : int) (x : int) : (term933 w y x) = (term934 w y x).
Proof. exact (MK_COMB (@lem2421931) (@lem2421930 w y x)). Qed.
Lemma lem2421933 (w : int) (y : int) (x : int) (z : int) : (term926 w y x z) = (term788 w y x z).
Proof. exact (eq_refl (term926 w y x z)). Qed.
Lemma lem2421934 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421935 (w : int) (y : int) (x : int) (z : int) : (term935 w y x z) = (term936 w y x z).
Proof. exact (MK_COMB (@lem2421934) (@lem2421933 w y x z)). Qed.
Lemma lem2421936 (w : int) (y : int) (x : int) (z : int) : (term930 w y x z) = (term806 w y x z).
Proof. exact (eq_refl (term930 w y x z)). Qed.
Lemma lem2421937 (w : int) (y : int) (x : int) (z : int) : (term937 w y x z) = (term938 w y x z).
Proof. exact (MK_COMB (@lem2421935 w y x z) (@lem2421936 w y x z)). Qed.
Lemma lem2421938 (w : int) (y : int) (x : int) : (term939 w y x) = (term940 w y x).
Proof. exact (fun_ext (fun z : int => @lem2421937 w y x z)). Qed.
Lemma lem2421939 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421940 (w : int) (y : int) (x : int) : (term925 w y x) = (term941 w y x).
Proof. exact (MK_COMB (@lem2421939) (@lem2421938 w y x)). Qed.
Lemma lem2421941 (w : int) (y : int) (x : int) : ((term924 w y x) = (term925 w y x)) = ((term920 w y x) = (term941 w y x)).
Proof. exact (MK_COMB (@lem2421932 w y x) (@lem2421940 w y x)). Qed.
Lemma lem2421942 (w : int) (y : int) (x : int) : (term920 w y x) = (term941 w y x).
Proof. exact (EQ_MP (@lem2421941 w y x) (@lem2421919 w y x)). Qed.
Lemma lem2421943 (w : int) (x : int) : (term922 w x) = (term942 w x).
Proof. exact (fun_ext (fun y : int => @lem2421942 w y x)). Qed.
Lemma lem2421944 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421945 (w : int) (x : int) : (term923 w x) = (term943 w x).
Proof. exact (MK_COMB (@lem2421944) (@lem2421943 w x)). Qed.
Lemma lem2421946 (w : int) (x : int) : (term902 w x) = (term943 w x).
Proof. exact (TRANS (@lem2421915 w x) (@lem2421945 w x)). Qed.
Lemma lem2421947 (w : int) : (term904 w) = (term944 w).
Proof. exact (fun_ext (fun x : int => @lem2421946 w x)). Qed.
Lemma lem2421948 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421949 (w : int) : (term905 w) = (term945 w).
Proof. exact (MK_COMB (@lem2421948) (@lem2421947 w)). Qed.
Lemma lem2421950 (w : int) : (term884 w) = (term945 w).
Proof. exact (TRANS (@lem2421888 w) (@lem2421949 w)). Qed.
Lemma lem2421951 : term886 = term946.
Proof. exact (fun_ext (fun w : int => @lem2421950 w)). Qed.
Lemma lem2421952 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421953 : term887 = term947.
Proof. exact (MK_COMB (@lem2421952) (@lem2421951)). Qed.
Lemma lem2421954 : term816 = term947.
Proof. exact (TRANS (@lem2421861) (@lem2421953)). Qed.
Lemma lem2421955 : term829 = term948.
Proof. exact (MK_COMB (@lem2421834) (@lem2421954)). Qed.
Lemma lem2421957 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term361 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2421958 (P : int -> Prop) (Q : int -> Prop) : (term363 P Q) = (term362 P Q).
Proof. exact (@lem2421957 int P Q). Qed.
Lemma lem2421959 : term949 = term950.
Proof. exact (@lem2421958 term867 term946). Qed.
Lemma lem2421960 (y : int) : (term951 y) = (term866 y).
Proof. exact (eq_refl (term951 y)). Qed.
Lemma lem2421961 : term952 = term867.
Proof. exact (fun_ext (fun y : int => @lem2421960 y)). Qed.
Lemma lem2421962 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421963 : term953 = term868.
Proof. exact (MK_COMB (@lem2421962) (@lem2421961)). Qed.
Lemma lem2421964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421965 : term954 = term869.
Proof. exact (MK_COMB (@lem2421964) (@lem2421963)). Qed.
Lemma lem2421966 (y : int) : (term955 y) = (term945 y).
Proof. exact (eq_refl (term955 y)). Qed.
Lemma lem2421967 : term956 = term946.
Proof. exact (fun_ext (fun y : int => @lem2421966 y)). Qed.
Lemma lem2421968 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421969 : term957 = term947.
Proof. exact (MK_COMB (@lem2421968) (@lem2421967)). Qed.
Lemma lem2421970 : term949 = term948.
Proof. exact (MK_COMB (@lem2421965) (@lem2421969)). Qed.
Lemma lem2421971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2421972 : term958 = term959.
Proof. exact (MK_COMB (@lem2421971) (@lem2421970)). Qed.
Lemma lem2421973 (y : int) : (term951 y) = (term866 y).
Proof. exact (eq_refl (term951 y)). Qed.
Lemma lem2421974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2421975 (y : int) : (term960 y) = (term961 y).
Proof. exact (MK_COMB (@lem2421974) (@lem2421973 y)). Qed.
Lemma lem2421976 (y : int) : (term955 y) = (term945 y).
Proof. exact (eq_refl (term955 y)). Qed.
Lemma lem2421977 (y : int) : (term962 y) = (term963 y).
Proof. exact (MK_COMB (@lem2421975 y) (@lem2421976 y)). Qed.
Lemma lem2421978 : term964 = term965.
Proof. exact (fun_ext (fun y : int => @lem2421977 y)). Qed.
Lemma lem2421979 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2421980 : term950 = term966.
Proof. exact (MK_COMB (@lem2421979) (@lem2421978)). Qed.
Lemma lem2421981 : (term949 = term950) = (term948 = term966).
Proof. exact (MK_COMB (@lem2421972) (@lem2421980)). Qed.
Lemma lem2421982 : term948 = term966.
Proof. exact (EQ_MP (@lem2421981) (@lem2421959)). Qed.
Lemma lem2421985 : term967 = term967.
Proof. exact (eq_refl term967). Qed.
Lemma lem2421986 : term967 = (term948 = term966).
Proof. exact (eq_refl term967). Qed.
Lemma lem2421987 : term968 = term968.
Proof. exact (eq_refl term968). Qed.
Lemma lem2421988 : (term967 = term967) = (term967 = (term948 = term966)).
Proof. exact (MK_COMB (@lem2421987) (@lem2421986)). Qed.
Lemma lem2421989 : term967 = (term948 = term966).
Proof. exact (eq_refl term967). Qed.
Lemma lem2421990 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2421991 : term968 = term969.
Proof. exact (MK_COMB (@lem2421990) (@lem2421989)). Qed.
Lemma lem2421992 : (term948 = term966) = (term948 = term966).
Proof. exact (eq_refl (term948 = term966)). Qed.
Lemma lem2421993 : (term967 = (term948 = term966)) = ((term948 = term966) = (term948 = term966)).
Proof. exact (MK_COMB (@lem2421991) (@lem2421992)). Qed.
Lemma lem2421994 : (term967 = term967) = ((term948 = term966) = (term948 = term966)).
Proof. exact (TRANS (@lem2421988) (@lem2421993)). Qed.
Lemma lem2421995 : (term948 = term966) = (term948 = term966).
Proof. exact (EQ_MP (@lem2421994) (@lem2421985)). Qed.
Lemma lem2421996 : term948 = term966.
Proof. exact (EQ_MP (@lem2421995) (@lem2421982)). Qed.
Lemma lem2421998 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term361 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2421999 (P : int -> Prop) (Q : int -> Prop) : (term363 P Q) = (term362 P Q).
Proof. exact (@lem2421998 int P Q). Qed.
Lemma lem2422000 (y : int) : (term970 y) = (term971 y).
Proof. exact (@lem2421999 (term865 y) (term944 y)). Qed.
Lemma lem2422001 (y : int) (z : int) : (term972 y z) = (term863 y z).
Proof. exact (eq_refl (term972 y z)). Qed.
Lemma lem2422002 (y : int) : (term973 y) = (term865 y).
Proof. exact (fun_ext (fun z : int => @lem2422001 y z)). Qed.
Lemma lem2422003 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422004 (y : int) : (term974 y) = (term866 y).
Proof. exact (MK_COMB (@lem2422003) (@lem2422002 y)). Qed.
Lemma lem2422005 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2422006 (y : int) : (term975 y) = (term961 y).
Proof. exact (MK_COMB (@lem2422005) (@lem2422004 y)). Qed.
Lemma lem2422007 (y : int) (z : int) : (term976 y z) = (term943 y z).
Proof. exact (eq_refl (term976 y z)). Qed.
Lemma lem2422008 (y : int) : (term977 y) = (term944 y).
Proof. exact (fun_ext (fun z : int => @lem2422007 y z)). Qed.
Lemma lem2422009 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422010 (y : int) : (term978 y) = (term945 y).
Proof. exact (MK_COMB (@lem2422009) (@lem2422008 y)). Qed.
Lemma lem2422011 (y : int) : (term970 y) = (term963 y).
Proof. exact (MK_COMB (@lem2422006 y) (@lem2422010 y)). Qed.
Lemma lem2422012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2422013 (y : int) : (term979 y) = (term980 y).
Proof. exact (MK_COMB (@lem2422012) (@lem2422011 y)). Qed.
Lemma lem2422014 (y : int) (z : int) : (term972 y z) = (term863 y z).
Proof. exact (eq_refl (term972 y z)). Qed.
Lemma lem2422015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2422016 (y : int) (z : int) : (term981 y z) = (term982 y z).
Proof. exact (MK_COMB (@lem2422015) (@lem2422014 y z)). Qed.
Lemma lem2422017 (y : int) (z : int) : (term976 y z) = (term943 y z).
Proof. exact (eq_refl (term976 y z)). Qed.
Lemma lem2422018 (y : int) (z : int) : (term983 y z) = (term984 y z).
Proof. exact (MK_COMB (@lem2422016 y z) (@lem2422017 y z)). Qed.
Lemma lem2422019 (y : int) : (term985 y) = (term986 y).
Proof. exact (fun_ext (fun z : int => @lem2422018 y z)). Qed.
Lemma lem2422020 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422021 (y : int) : (term971 y) = (term987 y).
Proof. exact (MK_COMB (@lem2422020) (@lem2422019 y)). Qed.
Lemma lem2422022 (y : int) : ((term970 y) = (term971 y)) = ((term963 y) = (term987 y)).
Proof. exact (MK_COMB (@lem2422013 y) (@lem2422021 y)). Qed.
Lemma lem2422023 (y : int) : (term963 y) = (term987 y).
Proof. exact (EQ_MP (@lem2422022 y) (@lem2422000 y)). Qed.
Lemma lem2422026 (y : int) : (term988 y) = (term988 y).
Proof. exact (eq_refl (term988 y)). Qed.
Lemma lem2422027 (y : int) : (term988 y) = ((term963 y) = (term987 y)).
Proof. exact (eq_refl (term988 y)). Qed.
Lemma lem2422028 (y : int) : (term989 y) = (term989 y).
Proof. exact (eq_refl (term989 y)). Qed.
Lemma lem2422029 (y : int) : ((term988 y) = (term988 y)) = ((term988 y) = ((term963 y) = (term987 y))).
Proof. exact (MK_COMB (@lem2422028 y) (@lem2422027 y)). Qed.
Lemma lem2422030 (y : int) : (term988 y) = ((term963 y) = (term987 y)).
Proof. exact (eq_refl (term988 y)). Qed.
Lemma lem2422031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2422032 (y : int) : (term989 y) = (term990 y).
Proof. exact (MK_COMB (@lem2422031) (@lem2422030 y)). Qed.
Lemma lem2422033 (y : int) : ((term963 y) = (term987 y)) = ((term963 y) = (term987 y)).
Proof. exact (eq_refl ((term963 y) = (term987 y))). Qed.
Lemma lem2422034 (y : int) : ((term988 y) = ((term963 y) = (term987 y))) = (((term963 y) = (term987 y)) = ((term963 y) = (term987 y))).
Proof. exact (MK_COMB (@lem2422032 y) (@lem2422033 y)). Qed.
Lemma lem2422035 (y : int) : ((term988 y) = (term988 y)) = (((term963 y) = (term987 y)) = ((term963 y) = (term987 y))).
Proof. exact (TRANS (@lem2422029 y) (@lem2422034 y)). Qed.
Lemma lem2422036 (y : int) : ((term963 y) = (term987 y)) = ((term963 y) = (term987 y)).
Proof. exact (EQ_MP (@lem2422035 y) (@lem2422026 y)). Qed.
Lemma lem2422037 (y : int) : (term963 y) = (term987 y).
Proof. exact (EQ_MP (@lem2422036 y) (@lem2422023 y)). Qed.
Lemma lem2422039 {A : Type'} (P : Prop) (Q : A -> Prop) : (term991 A P Q) = (term992 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem2422040 (P : Prop) (Q : int -> Prop) : (term993 P Q) = (term994 P Q).
Proof. exact (@lem2422039 int P Q). Qed.
Lemma lem2422041 (y : int) (z : int) : (term995 y z) = (term996 y z).
Proof. exact (@lem2422040 (term863 y z) (term942 y z)). Qed.
Lemma lem2422042 (y : int) (y' : int) (z : int) : (term997 y z y') = (term941 y y' z).
Proof. exact (eq_refl (term997 y z y')). Qed.
Lemma lem2422043 (y : int) (z : int) : (term998 y z) = (term942 y z).
Proof. exact (fun_ext (fun y' : int => @lem2422042 y y' z)). Qed.
Lemma lem2422044 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422045 (y : int) (z : int) : (term999 y z) = (term943 y z).
Proof. exact (MK_COMB (@lem2422044) (@lem2422043 y z)). Qed.
Lemma lem2422046 (y : int) (z : int) : (term982 y z) = (term982 y z).
Proof. exact (eq_refl (term982 y z)). Qed.
Lemma lem2422047 (y : int) (z : int) : (term995 y z) = (term984 y z).
Proof. exact (MK_COMB (@lem2422046 y z) (@lem2422045 y z)). Qed.
Lemma lem2422048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2422049 (y : int) (z : int) : (term1000 y z) = (term1001 y z).
Proof. exact (MK_COMB (@lem2422048) (@lem2422047 y z)). Qed.
Lemma lem2422050 (y : int) (y' : int) (z : int) : (term997 y z y') = (term941 y y' z).
Proof. exact (eq_refl (term997 y z y')). Qed.
Lemma lem2422051 (y : int) (z : int) : (term982 y z) = (term982 y z).
Proof. exact (eq_refl (term982 y z)). Qed.
Lemma lem2422052 (y : int) (y' : int) (z : int) : (term1002 y z y') = (term1003 y y' z).
Proof. exact (MK_COMB (@lem2422051 y z) (@lem2422050 y y' z)). Qed.
Lemma lem2422053 (y : int) (z : int) : (term1004 y z) = (term1005 y z).
Proof. exact (fun_ext (fun y' : int => @lem2422052 y y' z)). Qed.
Lemma lem2422054 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422055 (y : int) (z : int) : (term996 y z) = (term1006 y z).
Proof. exact (MK_COMB (@lem2422054) (@lem2422053 y z)). Qed.
Lemma lem2422056 (y : int) (z : int) : ((term995 y z) = (term996 y z)) = ((term984 y z) = (term1006 y z)).
Proof. exact (MK_COMB (@lem2422049 y z) (@lem2422055 y z)). Qed.
Lemma lem2422057 (y : int) (z : int) : (term984 y z) = (term1006 y z).
Proof. exact (EQ_MP (@lem2422056 y z) (@lem2422041 y z)). Qed.
Lemma lem2422059 {A : Type'} (P : Prop) (Q : A -> Prop) : (term991 A P Q) = (term992 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem2422060 (P : Prop) (Q : int -> Prop) : (term993 P Q) = (term994 P Q).
Proof. exact (@lem2422059 int P Q). Qed.
Lemma lem2422061 (y : int) (y' : int) (z : int) : (term1007 y y' z) = (term1008 y y' z).
Proof. exact (@lem2422060 (term863 y z) (term940 y y' z)). Qed.
Lemma lem2422062 (y : int) (y' : int) (z : int) (z' : int) : (term1009 y y' z z') = (term938 y y' z z').
Proof. exact (eq_refl (term1009 y y' z z')). Qed.
Lemma lem2422063 (y : int) (y' : int) (z : int) : (term1010 y y' z) = (term940 y y' z).
Proof. exact (fun_ext (fun z' : int => @lem2422062 y y' z z')). Qed.
Lemma lem2422064 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422065 (y : int) (y' : int) (z : int) : (term1011 y y' z) = (term941 y y' z).
Proof. exact (MK_COMB (@lem2422064) (@lem2422063 y y' z)). Qed.
Lemma lem2422066 (y : int) (z : int) : (term982 y z) = (term982 y z).
Proof. exact (eq_refl (term982 y z)). Qed.
Lemma lem2422067 (y : int) (y' : int) (z : int) : (term1007 y y' z) = (term1003 y y' z).
Proof. exact (MK_COMB (@lem2422066 y z) (@lem2422065 y y' z)). Qed.
Lemma lem2422068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2422069 (y : int) (y' : int) (z : int) : (term1012 y y' z) = (term1013 y y' z).
Proof. exact (MK_COMB (@lem2422068) (@lem2422067 y y' z)). Qed.
Lemma lem2422070 (y : int) (y' : int) (z : int) (z' : int) : (term1009 y y' z z') = (term938 y y' z z').
Proof. exact (eq_refl (term1009 y y' z z')). Qed.
Lemma lem2422071 (y : int) (z : int) : (term982 y z) = (term982 y z).
Proof. exact (eq_refl (term982 y z)). Qed.
Lemma lem2422072 (y : int) (y' : int) (z : int) (z' : int) : (term1014 y y' z z') = (term1015 y y' z z').
Proof. exact (MK_COMB (@lem2422071 y z) (@lem2422070 y y' z z')). Qed.
Lemma lem2422073 (y : int) (y' : int) (z : int) : (term1016 y y' z) = (term1017 y y' z).
Proof. exact (fun_ext (fun z' : int => @lem2422072 y y' z z')). Qed.
Lemma lem2422074 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422075 (y : int) (y' : int) (z : int) : (term1008 y y' z) = (term1018 y y' z).
Proof. exact (MK_COMB (@lem2422074) (@lem2422073 y y' z)). Qed.
Lemma lem2422076 (y : int) (y' : int) (z : int) : ((term1007 y y' z) = (term1008 y y' z)) = ((term1003 y y' z) = (term1018 y y' z)).
Proof. exact (MK_COMB (@lem2422069 y y' z) (@lem2422075 y y' z)). Qed.
Lemma lem2422077 (y : int) (y' : int) (z : int) : (term1003 y y' z) = (term1018 y y' z).
Proof. exact (EQ_MP (@lem2422076 y y' z) (@lem2422061 y y' z)). Qed.
Lemma lem2422078 (y : int) (z : int) : (term1005 y z) = (term1019 y z).
Proof. exact (fun_ext (fun y' : int => @lem2422077 y y' z)). Qed.
Lemma lem2422079 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422080 (y : int) (z : int) : (term1006 y z) = (term1020 y z).
Proof. exact (MK_COMB (@lem2422079) (@lem2422078 y z)). Qed.
Lemma lem2422081 (y : int) (z : int) : (term984 y z) = (term1020 y z).
Proof. exact (TRANS (@lem2422057 y z) (@lem2422080 y z)). Qed.
Lemma lem2422082 (y : int) : (term986 y) = (term1021 y).
Proof. exact (fun_ext (fun z : int => @lem2422081 y z)). Qed.
Lemma lem2422083 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422084 (y : int) : (term987 y) = (term1022 y).
Proof. exact (MK_COMB (@lem2422083) (@lem2422082 y)). Qed.
Lemma lem2422085 (y : int) : (term963 y) = (term1022 y).
Proof. exact (TRANS (@lem2422037 y) (@lem2422084 y)). Qed.
Lemma lem2422086 : term965 = term1023.
Proof. exact (fun_ext (fun y : int => @lem2422085 y)). Qed.
Lemma lem2422087 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422088 : term966 = term1024.
Proof. exact (MK_COMB (@lem2422087) (@lem2422086)). Qed.
Lemma lem2422089 : term948 = term1024.
Proof. exact (TRANS (@lem2421996) (@lem2422088)). Qed.
Lemma lem2422090 : term829 = term1024.
Proof. exact (TRANS (@lem2421955) (@lem2422089)). Qed.
Lemma lem2422091 : term825 = term825.
Proof. exact (eq_refl term825). Qed.
Lemma lem2422092 : term830 = term1025.
Proof. exact (MK_COMB (@lem2422091) (@lem2422090)). Qed.
Lemma lem2422094 {A : Type'} (P : Prop) (Q : A -> Prop) : (term991 A P Q) = (term992 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem2422095 (P : Prop) (Q : int -> Prop) : (term993 P Q) = (term994 P Q).
Proof. exact (@lem2422094 int P Q). Qed.
Lemma lem2422096 : term1026 = term1027.
Proof. exact (@lem2422095 term824 term1023). Qed.
Lemma lem2422097 (y : int) : (term1028 y) = (term1022 y).
Proof. exact (eq_refl (term1028 y)). Qed.
Lemma lem2422098 : term1029 = term1023.
Proof. exact (fun_ext (fun y : int => @lem2422097 y)). Qed.
Lemma lem2422099 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422100 : term1030 = term1024.
Proof. exact (MK_COMB (@lem2422099) (@lem2422098)). Qed.
Lemma lem2422101 : term825 = term825.
Proof. exact (eq_refl term825). Qed.
Lemma lem2422102 : term1026 = term1025.
Proof. exact (MK_COMB (@lem2422101) (@lem2422100)). Qed.
Lemma lem2422103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2422104 : term1031 = term1032.
Proof. exact (MK_COMB (@lem2422103) (@lem2422102)). Qed.
Lemma lem2422105 (y : int) : (term1028 y) = (term1022 y).
Proof. exact (eq_refl (term1028 y)). Qed.
Lemma lem2422106 : term825 = term825.
Proof. exact (eq_refl term825). Qed.
Lemma lem2422107 (y : int) : (term1033 y) = (term1034 y).
Proof. exact (MK_COMB (@lem2422106) (@lem2422105 y)). Qed.
Lemma lem2422108 : term1035 = term1036.
Proof. exact (fun_ext (fun y : int => @lem2422107 y)). Qed.
Lemma lem2422109 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422110 : term1027 = term1037.
Proof. exact (MK_COMB (@lem2422109) (@lem2422108)). Qed.
Lemma lem2422111 : (term1026 = term1027) = (term1025 = term1037).
Proof. exact (MK_COMB (@lem2422104) (@lem2422110)). Qed.
Lemma lem2422112 : term1025 = term1037.
Proof. exact (EQ_MP (@lem2422111) (@lem2422096)). Qed.
Lemma lem2422114 {A : Type'} (P : Prop) (Q : A -> Prop) : (term991 A P Q) = (term992 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem2422115 (P : Prop) (Q : int -> Prop) : (term993 P Q) = (term994 P Q).
Proof. exact (@lem2422114 int P Q). Qed.
Lemma lem2422116 (y : int) : (term1038 y) = (term1039 y).
Proof. exact (@lem2422115 term824 (term1021 y)). Qed.
Lemma lem2422117 (y : int) (z : int) : (term1040 y z) = (term1020 y z).
Proof. exact (eq_refl (term1040 y z)). Qed.
Lemma lem2422118 (y : int) : (term1041 y) = (term1021 y).
Proof. exact (fun_ext (fun z : int => @lem2422117 y z)). Qed.
Lemma lem2422119 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422120 (y : int) : (term1042 y) = (term1022 y).
Proof. exact (MK_COMB (@lem2422119) (@lem2422118 y)). Qed.
Lemma lem2422121 : term825 = term825.
Proof. exact (eq_refl term825). Qed.
Lemma lem2422122 (y : int) : (term1038 y) = (term1034 y).
Proof. exact (MK_COMB (@lem2422121) (@lem2422120 y)). Qed.
Lemma lem2422123 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2422124 (y : int) : (term1043 y) = (term1044 y).
Proof. exact (MK_COMB (@lem2422123) (@lem2422122 y)). Qed.
Lemma lem2422125 (y : int) (z : int) : (term1040 y z) = (term1020 y z).
Proof. exact (eq_refl (term1040 y z)). Qed.
Lemma lem2422126 : term825 = term825.
Proof. exact (eq_refl term825). Qed.
Lemma lem2422127 (y : int) (z : int) : (term1045 y z) = (term1046 y z).
Proof. exact (MK_COMB (@lem2422126) (@lem2422125 y z)). Qed.
Lemma lem2422128 (y : int) : (term1047 y) = (term1048 y).
Proof. exact (fun_ext (fun z : int => @lem2422127 y z)). Qed.
Lemma lem2422129 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422130 (y : int) : (term1039 y) = (term1049 y).
Proof. exact (MK_COMB (@lem2422129) (@lem2422128 y)). Qed.
Lemma lem2422131 (y : int) : ((term1038 y) = (term1039 y)) = ((term1034 y) = (term1049 y)).
Proof. exact (MK_COMB (@lem2422124 y) (@lem2422130 y)). Qed.
Lemma lem2422132 (y : int) : (term1034 y) = (term1049 y).
Proof. exact (EQ_MP (@lem2422131 y) (@lem2422116 y)). Qed.
Lemma lem2422134 {A : Type'} (P : Prop) (Q : A -> Prop) : (term991 A P Q) = (term992 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem2422135 (P : Prop) (Q : int -> Prop) : (term993 P Q) = (term994 P Q).
Proof. exact (@lem2422134 int P Q). Qed.
Lemma lem2422136 (y : int) (z : int) : (term1050 y z) = (term1051 y z).
Proof. exact (@lem2422135 term824 (term1019 y z)). Qed.
Lemma lem2422137 (y : int) (y' : int) (z : int) : (term1052 y z y') = (term1018 y y' z).
Proof. exact (eq_refl (term1052 y z y')). Qed.
Lemma lem2422138 (y : int) (z : int) : (term1053 y z) = (term1019 y z).
Proof. exact (fun_ext (fun y' : int => @lem2422137 y y' z)). Qed.
Lemma lem2422139 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422140 (y : int) (z : int) : (term1054 y z) = (term1020 y z).
Proof. exact (MK_COMB (@lem2422139) (@lem2422138 y z)). Qed.
Lemma lem2422141 : term825 = term825.
Proof. exact (eq_refl term825). Qed.
Lemma lem2422142 (y : int) (z : int) : (term1050 y z) = (term1046 y z).
Proof. exact (MK_COMB (@lem2422141) (@lem2422140 y z)). Qed.
Lemma lem2422143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2422144 (y : int) (z : int) : (term1055 y z) = (term1056 y z).
Proof. exact (MK_COMB (@lem2422143) (@lem2422142 y z)). Qed.
Lemma lem2422145 (y : int) (y' : int) (z : int) : (term1052 y z y') = (term1018 y y' z).
Proof. exact (eq_refl (term1052 y z y')). Qed.
Lemma lem2422146 : term825 = term825.
Proof. exact (eq_refl term825). Qed.
Lemma lem2422147 (y : int) (y' : int) (z : int) : (term1057 y z y') = (term1058 y y' z).
Proof. exact (MK_COMB (@lem2422146) (@lem2422145 y y' z)). Qed.
Lemma lem2422148 (y : int) (z : int) : (term1059 y z) = (term1060 y z).
Proof. exact (fun_ext (fun y' : int => @lem2422147 y y' z)). Qed.
Lemma lem2422149 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422150 (y : int) (z : int) : (term1051 y z) = (term1061 y z).
Proof. exact (MK_COMB (@lem2422149) (@lem2422148 y z)). Qed.
Lemma lem2422151 (y : int) (z : int) : ((term1050 y z) = (term1051 y z)) = ((term1046 y z) = (term1061 y z)).
Proof. exact (MK_COMB (@lem2422144 y z) (@lem2422150 y z)). Qed.
Lemma lem2422152 (y : int) (z : int) : (term1046 y z) = (term1061 y z).
Proof. exact (EQ_MP (@lem2422151 y z) (@lem2422136 y z)). Qed.
Lemma lem2422154 {A : Type'} (P : Prop) (Q : A -> Prop) : (term991 A P Q) = (term992 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem2422155 (P : Prop) (Q : int -> Prop) : (term993 P Q) = (term994 P Q).
Proof. exact (@lem2422154 int P Q). Qed.
Lemma lem2422156 (y : int) (y' : int) (z : int) : (term1062 y y' z) = (term1063 y y' z).
Proof. exact (@lem2422155 term824 (term1017 y y' z)). Qed.
Lemma lem2422157 (y : int) (y' : int) (z : int) (z' : int) : (term1064 y y' z z') = (term1015 y y' z z').
Proof. exact (eq_refl (term1064 y y' z z')). Qed.
Lemma lem2422158 (y : int) (y' : int) (z : int) : (term1065 y y' z) = (term1017 y y' z).
Proof. exact (fun_ext (fun z' : int => @lem2422157 y y' z z')). Qed.
Lemma lem2422159 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422160 (y : int) (y' : int) (z : int) : (term1066 y y' z) = (term1018 y y' z).
Proof. exact (MK_COMB (@lem2422159) (@lem2422158 y y' z)). Qed.
Lemma lem2422161 : term825 = term825.
Proof. exact (eq_refl term825). Qed.
Lemma lem2422162 (y : int) (y' : int) (z : int) : (term1062 y y' z) = (term1058 y y' z).
Proof. exact (MK_COMB (@lem2422161) (@lem2422160 y y' z)). Qed.
Lemma lem2422163 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2422164 (y : int) (y' : int) (z : int) : (term1067 y y' z) = (term1068 y y' z).
Proof. exact (MK_COMB (@lem2422163) (@lem2422162 y y' z)). Qed.
Lemma lem2422165 (y : int) (y' : int) (z : int) (z' : int) : (term1064 y y' z z') = (term1015 y y' z z').
Proof. exact (eq_refl (term1064 y y' z z')). Qed.
Lemma lem2422166 : term825 = term825.
Proof. exact (eq_refl term825). Qed.
Lemma lem2422167 (y : int) (y' : int) (z : int) (z' : int) : (term1069 y y' z z') = (term1070 y y' z z').
Proof. exact (MK_COMB (@lem2422166) (@lem2422165 y y' z z')). Qed.
Lemma lem2422168 (y : int) (y' : int) (z : int) : (term1071 y y' z) = (term1072 y y' z).
Proof. exact (fun_ext (fun z' : int => @lem2422167 y y' z z')). Qed.
Lemma lem2422169 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422170 (y : int) (y' : int) (z : int) : (term1063 y y' z) = (term1073 y y' z).
Proof. exact (MK_COMB (@lem2422169) (@lem2422168 y y' z)). Qed.
Lemma lem2422171 (y : int) (y' : int) (z : int) : ((term1062 y y' z) = (term1063 y y' z)) = ((term1058 y y' z) = (term1073 y y' z)).
Proof. exact (MK_COMB (@lem2422164 y y' z) (@lem2422170 y y' z)). Qed.
Lemma lem2422172 (y : int) (y' : int) (z : int) : (term1058 y y' z) = (term1073 y y' z).
Proof. exact (EQ_MP (@lem2422171 y y' z) (@lem2422156 y y' z)). Qed.
Lemma lem2422173 (y : int) (z : int) : (term1060 y z) = (term1074 y z).
Proof. exact (fun_ext (fun y' : int => @lem2422172 y y' z)). Qed.
Lemma lem2422174 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422175 (y : int) (z : int) : (term1061 y z) = (term1075 y z).
Proof. exact (MK_COMB (@lem2422174) (@lem2422173 y z)). Qed.
Lemma lem2422176 (y : int) (z : int) : (term1046 y z) = (term1075 y z).
Proof. exact (TRANS (@lem2422152 y z) (@lem2422175 y z)). Qed.
Lemma lem2422177 (y : int) : (term1048 y) = (term1076 y).
Proof. exact (fun_ext (fun z : int => @lem2422176 y z)). Qed.
Lemma lem2422178 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422179 (y : int) : (term1049 y) = (term1077 y).
Proof. exact (MK_COMB (@lem2422178) (@lem2422177 y)). Qed.
Lemma lem2422180 (y : int) : (term1034 y) = (term1077 y).
Proof. exact (TRANS (@lem2422132 y) (@lem2422179 y)). Qed.
Lemma lem2422181 : term1036 = term1078.
Proof. exact (fun_ext (fun y : int => @lem2422180 y)). Qed.
Lemma lem2422182 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422183 : term1037 = term1079.
Proof. exact (MK_COMB (@lem2422182) (@lem2422181)). Qed.
Lemma lem2422184 : term1025 = term1079.
Proof. exact (TRANS (@lem2422112) (@lem2422183)). Qed.
Lemma lem2422185 : term830 = term1079.
Proof. exact (TRANS (@lem2422092) (@lem2422184)). Qed.
Lemma lem2422186 : term820 = term1079.
Proof. exact (TRANS (@lem2421774) (@lem2422185)). Qed.
Lemma lem2422189 : term359 = term1079.
Proof. exact (TRANS (@lem2421521) (@lem2422186)). Qed.
Lemma lem2422206 (y : int) (y' : int) (z : int) (z' : int) : (term806 y y' z z') = (term1080 y y' z z').
Proof. exact (@lem19367 (term768 y y' z z') (term784 y y' z z') ((term713 y y' z z') = term182)). Qed.
Lemma lem2422223 (y : int) (y' : int) (z : int) (z' : int) : (term788 y y' z z') = (term1081 y y' z z').
Proof. exact (@lem19158 (term768 y y' z z') ((term713 y y' z z') = term182) (term784 y y' z z')). Qed.
Lemma lem2422224 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2422225 (y : int) (y' : int) (z : int) (z' : int) : (term936 y y' z z') = (term1082 y y' z z').
Proof. exact (MK_COMB (@lem2422224) (@lem2422223 y y' z z')). Qed.
Lemma lem2422226 (y : int) (y' : int) (z : int) (z' : int) : (term938 y y' z z') = (term1083 y y' z z').
Proof. exact (MK_COMB (@lem2422225 y y' z z') (@lem2422206 y y' z z')). Qed.
Lemma lem2422243 (y : int) (z : int) : (term690 y z) = (term1084 y z).
Proof. exact (@lem19367 (term660 y z) (term670 y z) ((term620 y z) = term182)). Qed.
Lemma lem2422260 (y : int) (z : int) : (term674 y z) = (term1085 y z).
Proof. exact (@lem19158 (term660 y z) ((term620 y z) = term182) (term670 y z)). Qed.
Lemma lem2422261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2422262 (y : int) (z : int) : (term861 y z) = (term1086 y z).
Proof. exact (MK_COMB (@lem2422261) (@lem2422260 y z)). Qed.
Lemma lem2422263 (y : int) (z : int) : (term863 y z) = (term1087 y z).
Proof. exact (MK_COMB (@lem2422262 y z) (@lem2422243 y z)). Qed.
Lemma lem2422264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2422265 (y : int) (z : int) : (term982 y z) = (term1088 y z).
Proof. exact (MK_COMB (@lem2422264) (@lem2422263 y z)). Qed.
Lemma lem2422266 (y : int) (y' : int) (z : int) (z' : int) : (term1015 y y' z z') = (term1089 y y' z z').
Proof. exact (MK_COMB (@lem2422265 y z) (@lem2422226 y y' z z')). Qed.
Lemma lem2422273 : term825 = term825.
Proof. exact (eq_refl term825). Qed.
Lemma lem2422274 (y : int) (y' : int) (z : int) (z' : int) : (term1070 y y' z z') = (term1090 y y' z z').
Proof. exact (MK_COMB (@lem2422273) (@lem2422266 y y' z z')). Qed.
Lemma lem2422275 (y : int) (y' : int) (z : int) : (term1072 y y' z) = (term1091 y y' z).
Proof. exact (fun_ext (fun z' : int => @lem2422274 y y' z z')). Qed.
Lemma lem2422276 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422277 (y : int) (y' : int) (z : int) : (term1073 y y' z) = (term1092 y y' z).
Proof. exact (MK_COMB (@lem2422276) (@lem2422275 y y' z)). Qed.
Lemma lem2422278 (y : int) (z : int) : (term1074 y z) = (term1093 y z).
Proof. exact (fun_ext (fun y' : int => @lem2422277 y y' z)). Qed.
Lemma lem2422279 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422280 (y : int) (z : int) : (term1075 y z) = (term1094 y z).
Proof. exact (MK_COMB (@lem2422279) (@lem2422278 y z)). Qed.
Lemma lem2422281 (y : int) : (term1076 y) = (term1095 y).
Proof. exact (fun_ext (fun z : int => @lem2422280 y z)). Qed.
Lemma lem2422282 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422283 (y : int) : (term1077 y) = (term1096 y).
Proof. exact (MK_COMB (@lem2422282) (@lem2422281 y)). Qed.
Lemma lem2422284 : term1078 = term1097.
Proof. exact (fun_ext (fun y : int => @lem2422283 y)). Qed.
Lemma lem2422285 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2422286 : term1079 = term1098.
Proof. exact (MK_COMB (@lem2422285) (@lem2422284)). Qed.
Lemma lem2422287 : term359 = term1098.
Proof. exact (TRANS (@lem2422189) (@lem2422286)). Qed.
Lemma lem2422345 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1090 y y' z z') : term1090 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem2422346 (h1 : term824) : term824.
Proof. exact (h1). Qed.
Lemma lem2422347 (h1 : term579) : term579.
Proof. exact (h1). Qed.
Lemma lem2422349 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2422350 : term579 = term1099.
Proof. exact (@lem2422349 term182 term546). Qed.
Lemma lem2422352 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2422353 : term546 = term547.
Proof. exact (@lem2422352 term193). Qed.
Lemma lem2422355 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2422356 : term182 = term543.
Proof. exact (@lem2422355 (NUMERAL 0)). Qed.
Lemma lem2422357 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2422358 : term1100 = term1101.
Proof. exact (MK_COMB (@lem2422357) (@lem2422356)). Qed.
Lemma lem2422359 : term1099 = term1102.
Proof. exact (MK_COMB (@lem2422358) (@lem2422353)). Qed.
Lemma lem2422360 : term1103.
Proof. exact (@lem1980026 term182 term192 term546 term192). Qed.
Lemma lem2422362 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422363 : term604 = term605.
Proof. exact (@lem2422362 (NUMERAL 0) term193). Qed.
Lemma lem2422364 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422365 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422366 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422365 h1) (fun h1 : term605 = True => @lem2422364)). Qed.
Lemma lem2422367 : term605 = True.
Proof. exact (EQ_MP (@lem2422366) (@lem2422364)). Qed.
Lemma lem2422368 : term604 = True.
Proof. exact (TRANS (@lem2422363) (@lem2422367)). Qed.
Lemma lem2422369 : True = term604.
Proof. exact (SYM (@lem2422368)). Qed.
Lemma lem2422370 : term604.
Proof. exact (EQ_MP (@lem2422369) (@lem0)). Qed.
Lemma lem2422371 : term1104.
Proof. exact (@lem2422360 (@lem2422370)). Qed.
Lemma lem2422373 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422374 : term604 = term605.
Proof. exact (@lem2422373 (NUMERAL 0) term193). Qed.
Lemma lem2422375 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422376 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422377 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422376 h1) (fun h1 : term605 = True => @lem2422375)). Qed.
Lemma lem2422378 : term605 = True.
Proof. exact (EQ_MP (@lem2422377) (@lem2422375)). Qed.
Lemma lem2422379 : term604 = True.
Proof. exact (TRANS (@lem2422374) (@lem2422378)). Qed.
Lemma lem2422380 : True = term604.
Proof. exact (SYM (@lem2422379)). Qed.
Lemma lem2422381 : term604.
Proof. exact (EQ_MP (@lem2422380) (@lem0)). Qed.
Lemma lem2422382 : term1102 = term1105.
Proof. exact (@lem2422371 (@lem2422381)). Qed.
Lemma lem2422384 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2422385 : term568 = term573.
Proof. exact (@lem2422384 term193 term193). Qed.
Lemma lem2422386 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2422387 : term558 = term193.
Proof. exact (EQ_MP (@lem2422386) (@lem940073)). Qed.
Lemma lem2422388 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2422389 : term556 = term192.
Proof. exact (MK_COMB (@lem2422388) (@lem2422387)). Qed.
Lemma lem2422390 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2422391 : term573 = term546.
Proof. exact (MK_COMB (@lem2422390) (@lem2422389)). Qed.
Lemma lem2422392 : term568 = term546.
Proof. exact (TRANS (@lem2422385) (@lem2422391)). Qed.
Lemma lem2422394 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2422395 : term615 = term182.
Proof. exact (@lem2422394 term193). Qed.
Lemma lem2422396 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2422397 : term1106 = term1100.
Proof. exact (MK_COMB (@lem2422396) (@lem2422395)). Qed.
Lemma lem2422398 : term1105 = term1099.
Proof. exact (MK_COMB (@lem2422397) (@lem2422392)). Qed.
Lemma lem2422400 (m : nat) (n : nat) : (term1107 m n) = (term1108 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2422401 : term1099 = term1109.
Proof. exact (@lem2422400 (NUMERAL 0) term193). Qed.
Lemma lem2422402 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422403 (h1 : term606 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2422404 : (term606 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422403 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem2422402)). Qed.
Lemma lem2422405 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2422404) (@lem2422402)). Qed.
Lemma lem2422406 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2422407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2422408 : term1110 = (and True).
Proof. exact (MK_COMB (@lem2422407) (@lem2422406)). Qed.
Lemma lem2422409 : term1109 = (True /\ False).
Proof. exact (MK_COMB (@lem2422408) (@lem2422405)). Qed.
Lemma lem2422411 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2422412 : term1109 = False.
Proof. exact (TRANS (@lem2422409) (@lem2422411)). Qed.
Lemma lem2422413 : term1099 = False.
Proof. exact (TRANS (@lem2422401) (@lem2422412)). Qed.
Lemma lem2422414 : term1105 = False.
Proof. exact (TRANS (@lem2422398) (@lem2422413)). Qed.
Lemma lem2422415 : term1102 = False.
Proof. exact (TRANS (@lem2422382) (@lem2422414)). Qed.
Lemma lem2422416 : term1099 = False.
Proof. exact (TRANS (@lem2422359) (@lem2422415)). Qed.
Lemma lem2422417 : term579 = False.
Proof. exact (TRANS (@lem2422350) (@lem2422416)). Qed.
Lemma lem2422418 (h1 : term579) : False.
Proof. exact (EQ_MP (@lem2422417) (@lem2422347 h1)). Qed.
Lemma lem2422419 (h1 : term579) : term579.
Proof. exact (h1). Qed.
Lemma lem2422421 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2422422 : term579 = term1099.
Proof. exact (@lem2422421 term182 term546). Qed.
Lemma lem2422424 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2422425 : term546 = term547.
Proof. exact (@lem2422424 term193). Qed.
Lemma lem2422427 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2422428 : term182 = term543.
Proof. exact (@lem2422427 (NUMERAL 0)). Qed.
Lemma lem2422429 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2422430 : term1100 = term1101.
Proof. exact (MK_COMB (@lem2422429) (@lem2422428)). Qed.
Lemma lem2422431 : term1099 = term1102.
Proof. exact (MK_COMB (@lem2422430) (@lem2422425)). Qed.
Lemma lem2422432 : term1103.
Proof. exact (@lem1980026 term182 term192 term546 term192). Qed.
Lemma lem2422434 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422435 : term604 = term605.
Proof. exact (@lem2422434 (NUMERAL 0) term193). Qed.
Lemma lem2422436 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422437 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422438 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422437 h1) (fun h1 : term605 = True => @lem2422436)). Qed.
Lemma lem2422439 : term605 = True.
Proof. exact (EQ_MP (@lem2422438) (@lem2422436)). Qed.
Lemma lem2422440 : term604 = True.
Proof. exact (TRANS (@lem2422435) (@lem2422439)). Qed.
Lemma lem2422441 : True = term604.
Proof. exact (SYM (@lem2422440)). Qed.
Lemma lem2422442 : term604.
Proof. exact (EQ_MP (@lem2422441) (@lem0)). Qed.
Lemma lem2422443 : term1104.
Proof. exact (@lem2422432 (@lem2422442)). Qed.
Lemma lem2422445 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422446 : term604 = term605.
Proof. exact (@lem2422445 (NUMERAL 0) term193). Qed.
Lemma lem2422447 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422448 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422449 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422448 h1) (fun h1 : term605 = True => @lem2422447)). Qed.
Lemma lem2422450 : term605 = True.
Proof. exact (EQ_MP (@lem2422449) (@lem2422447)). Qed.
Lemma lem2422451 : term604 = True.
Proof. exact (TRANS (@lem2422446) (@lem2422450)). Qed.
Lemma lem2422452 : True = term604.
Proof. exact (SYM (@lem2422451)). Qed.
Lemma lem2422453 : term604.
Proof. exact (EQ_MP (@lem2422452) (@lem0)). Qed.
Lemma lem2422454 : term1102 = term1105.
Proof. exact (@lem2422443 (@lem2422453)). Qed.
Lemma lem2422456 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2422457 : term568 = term573.
Proof. exact (@lem2422456 term193 term193). Qed.
Lemma lem2422458 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2422459 : term558 = term193.
Proof. exact (EQ_MP (@lem2422458) (@lem940073)). Qed.
Lemma lem2422460 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2422461 : term556 = term192.
Proof. exact (MK_COMB (@lem2422460) (@lem2422459)). Qed.
Lemma lem2422462 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2422463 : term573 = term546.
Proof. exact (MK_COMB (@lem2422462) (@lem2422461)). Qed.
Lemma lem2422464 : term568 = term546.
Proof. exact (TRANS (@lem2422457) (@lem2422463)). Qed.
Lemma lem2422466 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2422467 : term615 = term182.
Proof. exact (@lem2422466 term193). Qed.
Lemma lem2422468 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2422469 : term1106 = term1100.
Proof. exact (MK_COMB (@lem2422468) (@lem2422467)). Qed.
Lemma lem2422470 : term1105 = term1099.
Proof. exact (MK_COMB (@lem2422469) (@lem2422464)). Qed.
Lemma lem2422472 (m : nat) (n : nat) : (term1107 m n) = (term1108 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2422473 : term1099 = term1109.
Proof. exact (@lem2422472 (NUMERAL 0) term193). Qed.
Lemma lem2422474 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422475 (h1 : term606 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2422476 : (term606 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422475 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem2422474)). Qed.
Lemma lem2422477 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2422476) (@lem2422474)). Qed.
Lemma lem2422478 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2422479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2422480 : term1110 = (and True).
Proof. exact (MK_COMB (@lem2422479) (@lem2422478)). Qed.
Lemma lem2422481 : term1109 = (True /\ False).
Proof. exact (MK_COMB (@lem2422480) (@lem2422477)). Qed.
Lemma lem2422483 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2422484 : term1109 = False.
Proof. exact (TRANS (@lem2422481) (@lem2422483)). Qed.
Lemma lem2422485 : term1099 = False.
Proof. exact (TRANS (@lem2422473) (@lem2422484)). Qed.
Lemma lem2422486 : term1105 = False.
Proof. exact (TRANS (@lem2422470) (@lem2422485)). Qed.
Lemma lem2422487 : term1102 = False.
Proof. exact (TRANS (@lem2422454) (@lem2422486)). Qed.
Lemma lem2422488 : term1099 = False.
Proof. exact (TRANS (@lem2422431) (@lem2422487)). Qed.
Lemma lem2422489 : term579 = False.
Proof. exact (TRANS (@lem2422422) (@lem2422488)). Qed.
Lemma lem2422490 (h1 : term579) : False.
Proof. exact (EQ_MP (@lem2422489) (@lem2422419 h1)). Qed.
Lemma lem2422491 (h1 : term824) : False.
Proof. exact (or_elim (@lem2422346 h1) (fun h0 : term579 => @lem2422418 h0) (fun h0 : term579 => @lem2422490 h0)). Qed.
Lemma lem2422492 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1089 y y' z z') : term1089 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem2422493 (y : int) (z : int) (h1 : term1087 y z) : term1087 y z.
Proof. exact (h1). Qed.
Lemma lem2422494 (y : int) (z : int) (h1 : term1085 y z) : term1085 y z.
Proof. exact (h1). Qed.
Lemma lem2422495 (y : int) (z : int) (h1 : term1111 y z) : term1111 y z.
Proof. exact (h1). Qed.
Lemma lem2422496 (y : int) (z : int) (h1 : term1111 y z) : term660 y z.
Proof. exact (proj2 (@lem2422495 y z h1)). Qed.
Lemma lem2422497 (y : int) (z : int) (h1 : term1111 y z) : (term620 y z) = term182.
Proof. exact (proj1 (@lem2422495 y z h1)). Qed.
Lemma lem2422499 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2422500 : term1112 = term604.
Proof. exact (@lem2422499 term182 term192). Qed.
Lemma lem2422502 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2422503 : term192 = term567.
Proof. exact (@lem2422502 term193). Qed.
Lemma lem2422505 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2422506 : term182 = term543.
Proof. exact (@lem2422505 (NUMERAL 0)). Qed.
Lemma lem2422507 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2422508 : term1113 = term1114.
Proof. exact (MK_COMB (@lem2422507) (@lem2422506)). Qed.
Lemma lem2422509 : term604 = term1115.
Proof. exact (MK_COMB (@lem2422508) (@lem2422503)). Qed.
Lemma lem2422510 : term1116.
Proof. exact (@lem1980255 term182 term192 term192 term192). Qed.
Lemma lem2422512 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422513 : term604 = term605.
Proof. exact (@lem2422512 (NUMERAL 0) term193). Qed.
Lemma lem2422514 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422515 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422516 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422515 h1) (fun h1 : term605 = True => @lem2422514)). Qed.
Lemma lem2422517 : term605 = True.
Proof. exact (EQ_MP (@lem2422516) (@lem2422514)). Qed.
Lemma lem2422518 : term604 = True.
Proof. exact (TRANS (@lem2422513) (@lem2422517)). Qed.
Lemma lem2422519 : True = term604.
Proof. exact (SYM (@lem2422518)). Qed.
Lemma lem2422520 : term604.
Proof. exact (EQ_MP (@lem2422519) (@lem0)). Qed.
Lemma lem2422521 : term1117.
Proof. exact (@lem2422510 (@lem2422520)). Qed.
Lemma lem2422523 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422524 : term604 = term605.
Proof. exact (@lem2422523 (NUMERAL 0) term193). Qed.
Lemma lem2422525 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422526 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422527 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422526 h1) (fun h1 : term605 = True => @lem2422525)). Qed.
Lemma lem2422528 : term605 = True.
Proof. exact (EQ_MP (@lem2422527) (@lem2422525)). Qed.
Lemma lem2422529 : term604 = True.
Proof. exact (TRANS (@lem2422524) (@lem2422528)). Qed.
Lemma lem2422530 : True = term604.
Proof. exact (SYM (@lem2422529)). Qed.
Lemma lem2422531 : term604.
Proof. exact (EQ_MP (@lem2422530) (@lem0)). Qed.
Lemma lem2422532 : term1115 = term1118.
Proof. exact (@lem2422521 (@lem2422531)). Qed.
Lemma lem2422534 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2422535 : term555 = term556.
Proof. exact (@lem2422534 term193 term193). Qed.
Lemma lem2422536 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2422537 : term558 = term193.
Proof. exact (EQ_MP (@lem2422536) (@lem940073)). Qed.
Lemma lem2422538 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2422539 : term556 = term192.
Proof. exact (MK_COMB (@lem2422538) (@lem2422537)). Qed.
Lemma lem2422540 : term555 = term192.
Proof. exact (TRANS (@lem2422535) (@lem2422539)). Qed.
Lemma lem2422542 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2422543 : term615 = term182.
Proof. exact (@lem2422542 term193). Qed.
Lemma lem2422544 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2422545 : term1119 = term1113.
Proof. exact (MK_COMB (@lem2422544) (@lem2422543)). Qed.
Lemma lem2422546 : term1118 = term604.
Proof. exact (MK_COMB (@lem2422545) (@lem2422540)). Qed.
Lemma lem2422548 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422549 : term604 = term605.
Proof. exact (@lem2422548 (NUMERAL 0) term193). Qed.
Lemma lem2422550 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422551 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422552 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422551 h1) (fun h1 : term605 = True => @lem2422550)). Qed.
Lemma lem2422553 : term605 = True.
Proof. exact (EQ_MP (@lem2422552) (@lem2422550)). Qed.
Lemma lem2422554 : term604 = True.
Proof. exact (TRANS (@lem2422549) (@lem2422553)). Qed.
Lemma lem2422555 : term1118 = True.
Proof. exact (TRANS (@lem2422546) (@lem2422554)). Qed.
Lemma lem2422556 : term1115 = True.
Proof. exact (TRANS (@lem2422532) (@lem2422555)). Qed.
Lemma lem2422557 : term604 = True.
Proof. exact (TRANS (@lem2422509) (@lem2422556)). Qed.
Lemma lem2422558 : term1112 = True.
Proof. exact (TRANS (@lem2422500) (@lem2422557)). Qed.
Lemma lem2422559 : True = term1112.
Proof. exact (SYM (@lem2422558)). Qed.
Lemma lem2422560 : term1112.
Proof. exact (EQ_MP (@lem2422559) (@lem0)). Qed.
Lemma lem2422561 (y : int) (z : int) (h1 : term1111 y z) : term1120 y z.
Proof. exact (conj (@lem2422560) (@lem2422496 y z h1)). Qed.
Lemma lem2422563 (x : real) (y : real) : term1121 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2422564 (y : int) (z : int) : term1122 y z.
Proof. exact (@lem2422563 term192 (term656 y z)). Qed.
Lemma lem2422565 (y : int) (z : int) (h1 : term1111 y z) : term1123 y z.
Proof. exact (@lem2422564 y z (@lem2422561 y z h1)). Qed.
Lemma lem2422566 (y : int) (z : int) : (term1124 y z) = (term656 y z).
Proof. exact (@lem1982733 (term656 y z)). Qed.
Lemma lem2422567 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2422568 (y : int) (z : int) : (term1125 y z) = (term659 y z).
Proof. exact (MK_COMB (@lem2422567) (@lem2422566 y z)). Qed.
Lemma lem2422569 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2422570 (y : int) (z : int) : (term1123 y z) = (term660 y z).
Proof. exact (MK_COMB (@lem2422568 y z) (@lem2422569)). Qed.
Lemma lem2422571 (y : int) (z : int) (h1 : term1111 y z) : term660 y z.
Proof. exact (EQ_MP (@lem2422570 y z) (@lem2422565 y z h1)). Qed.
Lemma lem2422573 (y : real) : term1126 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2422574 (y : int) (z : int) : term1127 y z.
Proof. exact (@lem2422573 (term620 y z)). Qed.
Lemma lem2422575 (y : int) (z : int) (h1 : term1111 y z) : term1128 y z.
Proof. exact (@lem2422574 y z (@lem2422497 y z h1)). Qed.
Lemma lem2422576 (y : int) (z : int) (h1 : term1111 y z) : term1129 y z.
Proof. exact (@lem2422575 y z h1 term192). Qed.
Lemma lem2422577 (y : int) (z : int) : (term1129 y z) = ((term1130 y z) = term182).
Proof. exact (eq_refl (term1129 y z)). Qed.
Lemma lem2422578 (y : int) (z : int) (h1 : term1111 y z) : (term1130 y z) = term182.
Proof. exact (EQ_MP (@lem2422577 y z) (@lem2422576 y z h1)). Qed.
Lemma lem2422579 (y : int) (z : int) : (term1130 y z) = (term620 y z).
Proof. exact (@lem1982733 (term620 y z)). Qed.
Lemma lem2422580 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2422581 (y : int) (z : int) : (term1131 y z) = (term629 y z).
Proof. exact (MK_COMB (@lem2422580) (@lem2422579 y z)). Qed.
Lemma lem2422582 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2422583 (y : int) (z : int) : ((term1130 y z) = term182) = ((term620 y z) = term182).
Proof. exact (MK_COMB (@lem2422581 y z) (@lem2422582)). Qed.
Lemma lem2422584 (y : int) (z : int) (h1 : term1111 y z) : (term620 y z) = term182.
Proof. exact (EQ_MP (@lem2422583 y z) (@lem2422578 y z h1)). Qed.
Lemma lem2422585 (y : int) (z : int) (h1 : term1111 y z) : term1111 y z.
Proof. exact (conj (@lem2422584 y z h1) (@lem2422571 y z h1)). Qed.
Lemma lem2422587 (x : real) (y : real) : term1132 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2422588 (y : int) (z : int) : term1133 y z.
Proof. exact (@lem2422587 (term620 y z) (term656 y z)). Qed.
Lemma lem2422589 (y : int) (z : int) (h1 : term1111 y z) : term1134 y z.
Proof. exact (@lem2422588 y z (@lem2422585 y z h1)). Qed.
Lemma lem2422590 (y : int) (z : int) : (term1135 y z) = (term1136 y z).
Proof. exact (@lem1982753 (real_of_int y) (term595 y) (term595 z) (term654 z)). Qed.
Lemma lem2422591 (y : int) : (term596 y) = (term597 y).
Proof. exact (@lem1982715 term546 (real_of_int y)). Qed.
Lemma lem2422593 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2422594 : term192 = term567.
Proof. exact (@lem2422593 term193). Qed.
Lemma lem2422596 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2422597 : term546 = term547.
Proof. exact (@lem2422596 term193). Qed.
Lemma lem2422598 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2422599 : term598 = term599.
Proof. exact (MK_COMB (@lem2422598) (@lem2422597)). Qed.
Lemma lem2422600 : term600 = term601.
Proof. exact (MK_COMB (@lem2422599) (@lem2422594)). Qed.
Lemma lem2422601 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2422603 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422604 : term604 = term605.
Proof. exact (@lem2422603 (NUMERAL 0) term193). Qed.
Lemma lem2422605 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422606 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422607 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422606 h1) (fun h1 : term605 = True => @lem2422605)). Qed.
Lemma lem2422608 : term605 = True.
Proof. exact (EQ_MP (@lem2422607) (@lem2422605)). Qed.
Lemma lem2422609 : term604 = True.
Proof. exact (TRANS (@lem2422604) (@lem2422608)). Qed.
Lemma lem2422610 : True = term604.
Proof. exact (SYM (@lem2422609)). Qed.
Lemma lem2422611 : term604.
Proof. exact (EQ_MP (@lem2422610) (@lem0)). Qed.
Lemma lem2422612 : term607.
Proof. exact (@lem2422601 (@lem2422611)). Qed.
Lemma lem2422614 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422615 : term604 = term605.
Proof. exact (@lem2422614 (NUMERAL 0) term193). Qed.
Lemma lem2422616 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422617 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422618 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422617 h1) (fun h1 : term605 = True => @lem2422616)). Qed.
Lemma lem2422619 : term605 = True.
Proof. exact (EQ_MP (@lem2422618) (@lem2422616)). Qed.
Lemma lem2422620 : term604 = True.
Proof. exact (TRANS (@lem2422615) (@lem2422619)). Qed.
Lemma lem2422621 : True = term604.
Proof. exact (SYM (@lem2422620)). Qed.
Lemma lem2422622 : term604.
Proof. exact (EQ_MP (@lem2422621) (@lem0)). Qed.
Lemma lem2422623 : term608.
Proof. exact (@lem2422612 (@lem2422622)). Qed.
Lemma lem2422625 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422626 : term604 = term605.
Proof. exact (@lem2422625 (NUMERAL 0) term193). Qed.
Lemma lem2422627 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422628 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422629 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422628 h1) (fun h1 : term605 = True => @lem2422627)). Qed.
Lemma lem2422630 : term605 = True.
Proof. exact (EQ_MP (@lem2422629) (@lem2422627)). Qed.
Lemma lem2422631 : term604 = True.
Proof. exact (TRANS (@lem2422626) (@lem2422630)). Qed.
Lemma lem2422632 : True = term604.
Proof. exact (SYM (@lem2422631)). Qed.
Lemma lem2422633 : term604.
Proof. exact (EQ_MP (@lem2422632) (@lem0)). Qed.
Lemma lem2422634 : term609.
Proof. exact (@lem2422623 (@lem2422633)). Qed.
Lemma lem2422636 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2422637 : term555 = term556.
Proof. exact (@lem2422636 term193 term193). Qed.
Lemma lem2422638 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2422639 : term558 = term193.
Proof. exact (EQ_MP (@lem2422638) (@lem940073)). Qed.
Lemma lem2422640 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2422641 : term556 = term192.
Proof. exact (MK_COMB (@lem2422640) (@lem2422639)). Qed.
Lemma lem2422642 : term555 = term192.
Proof. exact (TRANS (@lem2422637) (@lem2422641)). Qed.
Lemma lem2422644 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2422645 : term568 = term573.
Proof. exact (@lem2422644 term193 term193). Qed.
Lemma lem2422646 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2422647 : term558 = term193.
Proof. exact (EQ_MP (@lem2422646) (@lem940073)). Qed.
Lemma lem2422648 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2422649 : term556 = term192.
Proof. exact (MK_COMB (@lem2422648) (@lem2422647)). Qed.
Lemma lem2422650 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2422651 : term573 = term546.
Proof. exact (MK_COMB (@lem2422650) (@lem2422649)). Qed.
Lemma lem2422652 : term568 = term546.
Proof. exact (TRANS (@lem2422645) (@lem2422651)). Qed.
Lemma lem2422653 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2422654 : term610 = term598.
Proof. exact (MK_COMB (@lem2422653) (@lem2422652)). Qed.
Lemma lem2422655 : term611 = term600.
Proof. exact (MK_COMB (@lem2422654) (@lem2422642)). Qed.
Lemma lem2422657 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2422658 : term600 = term182.
Proof. exact (@lem2422657 term193). Qed.
Lemma lem2422659 : term611 = term182.
Proof. exact (TRANS (@lem2422655) (@lem2422658)). Qed.
Lemma lem2422660 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2422661 : term613 = term184.
Proof. exact (MK_COMB (@lem2422660) (@lem2422659)). Qed.
Lemma lem2422662 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2422663 : term614 = term615.
Proof. exact (MK_COMB (@lem2422661) (@lem2422662)). Qed.
Lemma lem2422665 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2422666 : term615 = term182.
Proof. exact (@lem2422665 term193). Qed.
Lemma lem2422667 : term614 = term182.
Proof. exact (TRANS (@lem2422663) (@lem2422666)). Qed.
Lemma lem2422669 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2422670 : term555 = term556.
Proof. exact (@lem2422669 term193 term193). Qed.
Lemma lem2422671 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2422672 : term558 = term193.
Proof. exact (EQ_MP (@lem2422671) (@lem940073)). Qed.
Lemma lem2422673 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2422674 : term556 = term192.
Proof. exact (MK_COMB (@lem2422673) (@lem2422672)). Qed.
Lemma lem2422675 : term555 = term192.
Proof. exact (TRANS (@lem2422670) (@lem2422674)). Qed.
Lemma lem2422676 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2422677 : term617 = term615.
Proof. exact (MK_COMB (@lem2422676) (@lem2422675)). Qed.
Lemma lem2422679 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2422680 : term615 = term182.
Proof. exact (@lem2422679 term193). Qed.
Lemma lem2422681 : term617 = term182.
Proof. exact (TRANS (@lem2422677) (@lem2422680)). Qed.
Lemma lem2422682 : term182 = term617.
Proof. exact (SYM (@lem2422681)). Qed.
Lemma lem2422683 : term614 = term617.
Proof. exact (TRANS (@lem2422667) (@lem2422682)). Qed.
Lemma lem2422684 : term601 = term543.
Proof. exact (@lem2422634 (@lem2422683)). Qed.
Lemma lem2422685 : term600 = term543.
Proof. exact (TRANS (@lem2422600) (@lem2422684)). Qed.
Lemma lem2422687 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2422688 : term543 = term182.
Proof. exact (@lem2422687 term182). Qed.
Lemma lem2422689 : term600 = term182.
Proof. exact (TRANS (@lem2422685) (@lem2422688)). Qed.
Lemma lem2422690 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2422691 : term618 = term184.
Proof. exact (MK_COMB (@lem2422690) (@lem2422689)). Qed.
Lemma lem2422692 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2422693 (y : int) : (term597 y) = (term185 y).
Proof. exact (MK_COMB (@lem2422691) (@lem2422692 y)). Qed.
Lemma lem2422694 (y : int) : (term596 y) = (term185 y).
Proof. exact (TRANS (@lem2422591 y) (@lem2422693 y)). Qed.
Lemma lem2422695 (y : int) : (term185 y) = term182.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2422696 (y : int) : (term596 y) = term182.
Proof. exact (TRANS (@lem2422694 y) (@lem2422695 y)). Qed.
Lemma lem2422697 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2422698 (y : int) : (term619 y) = term206.
Proof. exact (MK_COMB (@lem2422697) (@lem2422696 y)). Qed.
Lemma lem2422699 (z : int) : (term1137 z) = (term1138 z).
Proof. exact (@lem1982763 (term595 z) (real_of_int z) term546). Qed.
Lemma lem2422700 (z : int) : (term1139 z) = (term597 z).
Proof. exact (@lem1982713 term546 (real_of_int z)). Qed.
Lemma lem2422702 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2422703 : term192 = term567.
Proof. exact (@lem2422702 term193). Qed.
Lemma lem2422705 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2422706 : term546 = term547.
Proof. exact (@lem2422705 term193). Qed.
Lemma lem2422707 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2422708 : term598 = term599.
Proof. exact (MK_COMB (@lem2422707) (@lem2422706)). Qed.
Lemma lem2422709 : term600 = term601.
Proof. exact (MK_COMB (@lem2422708) (@lem2422703)). Qed.
Lemma lem2422710 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2422712 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422713 : term604 = term605.
Proof. exact (@lem2422712 (NUMERAL 0) term193). Qed.
Lemma lem2422714 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422715 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422716 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422715 h1) (fun h1 : term605 = True => @lem2422714)). Qed.
Lemma lem2422717 : term605 = True.
Proof. exact (EQ_MP (@lem2422716) (@lem2422714)). Qed.
Lemma lem2422718 : term604 = True.
Proof. exact (TRANS (@lem2422713) (@lem2422717)). Qed.
Lemma lem2422719 : True = term604.
Proof. exact (SYM (@lem2422718)). Qed.
Lemma lem2422720 : term604.
Proof. exact (EQ_MP (@lem2422719) (@lem0)). Qed.
Lemma lem2422721 : term607.
Proof. exact (@lem2422710 (@lem2422720)). Qed.
Lemma lem2422723 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422724 : term604 = term605.
Proof. exact (@lem2422723 (NUMERAL 0) term193). Qed.
Lemma lem2422725 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422726 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422727 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422726 h1) (fun h1 : term605 = True => @lem2422725)). Qed.
Lemma lem2422728 : term605 = True.
Proof. exact (EQ_MP (@lem2422727) (@lem2422725)). Qed.
Lemma lem2422729 : term604 = True.
Proof. exact (TRANS (@lem2422724) (@lem2422728)). Qed.
Lemma lem2422730 : True = term604.
Proof. exact (SYM (@lem2422729)). Qed.
Lemma lem2422731 : term604.
Proof. exact (EQ_MP (@lem2422730) (@lem0)). Qed.
Lemma lem2422732 : term608.
Proof. exact (@lem2422721 (@lem2422731)). Qed.
Lemma lem2422734 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422735 : term604 = term605.
Proof. exact (@lem2422734 (NUMERAL 0) term193). Qed.
Lemma lem2422736 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422737 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422738 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422737 h1) (fun h1 : term605 = True => @lem2422736)). Qed.
Lemma lem2422739 : term605 = True.
Proof. exact (EQ_MP (@lem2422738) (@lem2422736)). Qed.
Lemma lem2422740 : term604 = True.
Proof. exact (TRANS (@lem2422735) (@lem2422739)). Qed.
Lemma lem2422741 : True = term604.
Proof. exact (SYM (@lem2422740)). Qed.
Lemma lem2422742 : term604.
Proof. exact (EQ_MP (@lem2422741) (@lem0)). Qed.
Lemma lem2422743 : term609.
Proof. exact (@lem2422732 (@lem2422742)). Qed.
Lemma lem2422745 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2422746 : term555 = term556.
Proof. exact (@lem2422745 term193 term193). Qed.
Lemma lem2422747 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2422748 : term558 = term193.
Proof. exact (EQ_MP (@lem2422747) (@lem940073)). Qed.
Lemma lem2422749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2422750 : term556 = term192.
Proof. exact (MK_COMB (@lem2422749) (@lem2422748)). Qed.
Lemma lem2422751 : term555 = term192.
Proof. exact (TRANS (@lem2422746) (@lem2422750)). Qed.
Lemma lem2422753 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2422754 : term568 = term573.
Proof. exact (@lem2422753 term193 term193). Qed.
Lemma lem2422755 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2422756 : term558 = term193.
Proof. exact (EQ_MP (@lem2422755) (@lem940073)). Qed.
Lemma lem2422757 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2422758 : term556 = term192.
Proof. exact (MK_COMB (@lem2422757) (@lem2422756)). Qed.
Lemma lem2422759 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2422760 : term573 = term546.
Proof. exact (MK_COMB (@lem2422759) (@lem2422758)). Qed.
Lemma lem2422761 : term568 = term546.
Proof. exact (TRANS (@lem2422754) (@lem2422760)). Qed.
Lemma lem2422762 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2422763 : term610 = term598.
Proof. exact (MK_COMB (@lem2422762) (@lem2422761)). Qed.
Lemma lem2422764 : term611 = term600.
Proof. exact (MK_COMB (@lem2422763) (@lem2422751)). Qed.
Lemma lem2422766 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2422767 : term600 = term182.
Proof. exact (@lem2422766 term193). Qed.
Lemma lem2422768 : term611 = term182.
Proof. exact (TRANS (@lem2422764) (@lem2422767)). Qed.
Lemma lem2422769 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2422770 : term613 = term184.
Proof. exact (MK_COMB (@lem2422769) (@lem2422768)). Qed.
Lemma lem2422771 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2422772 : term614 = term615.
Proof. exact (MK_COMB (@lem2422770) (@lem2422771)). Qed.
Lemma lem2422774 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2422775 : term615 = term182.
Proof. exact (@lem2422774 term193). Qed.
Lemma lem2422776 : term614 = term182.
Proof. exact (TRANS (@lem2422772) (@lem2422775)). Qed.
Lemma lem2422778 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2422779 : term555 = term556.
Proof. exact (@lem2422778 term193 term193). Qed.
Lemma lem2422780 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2422781 : term558 = term193.
Proof. exact (EQ_MP (@lem2422780) (@lem940073)). Qed.
Lemma lem2422782 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2422783 : term556 = term192.
Proof. exact (MK_COMB (@lem2422782) (@lem2422781)). Qed.
Lemma lem2422784 : term555 = term192.
Proof. exact (TRANS (@lem2422779) (@lem2422783)). Qed.
Lemma lem2422785 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2422786 : term617 = term615.
Proof. exact (MK_COMB (@lem2422785) (@lem2422784)). Qed.
Lemma lem2422788 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2422789 : term615 = term182.
Proof. exact (@lem2422788 term193). Qed.
Lemma lem2422790 : term617 = term182.
Proof. exact (TRANS (@lem2422786) (@lem2422789)). Qed.
Lemma lem2422791 : term182 = term617.
Proof. exact (SYM (@lem2422790)). Qed.
Lemma lem2422792 : term614 = term617.
Proof. exact (TRANS (@lem2422776) (@lem2422791)). Qed.
Lemma lem2422793 : term601 = term543.
Proof. exact (@lem2422743 (@lem2422792)). Qed.
Lemma lem2422794 : term600 = term543.
Proof. exact (TRANS (@lem2422709) (@lem2422793)). Qed.
Lemma lem2422796 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2422797 : term543 = term182.
Proof. exact (@lem2422796 term182). Qed.
Lemma lem2422798 : term600 = term182.
Proof. exact (TRANS (@lem2422794) (@lem2422797)). Qed.
Lemma lem2422799 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2422800 : term618 = term184.
Proof. exact (MK_COMB (@lem2422799) (@lem2422798)). Qed.
Lemma lem2422801 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2422802 (z : int) : (term597 z) = (term185 z).
Proof. exact (MK_COMB (@lem2422800) (@lem2422801 z)). Qed.
Lemma lem2422803 (z : int) : (term1139 z) = (term185 z).
Proof. exact (TRANS (@lem2422700 z) (@lem2422802 z)). Qed.
Lemma lem2422804 (z : int) : (term185 z) = term182.
Proof. exact (@lem1982719 (real_of_int z)). Qed.
Lemma lem2422805 (z : int) : (term1139 z) = term182.
Proof. exact (TRANS (@lem2422803 z) (@lem2422804 z)). Qed.
Lemma lem2422806 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2422807 (z : int) : (term1140 z) = term206.
Proof. exact (MK_COMB (@lem2422806) (@lem2422805 z)). Qed.
Lemma lem2422808 : term546 = term546.
Proof. exact (eq_refl term546). Qed.
Lemma lem2422809 (z : int) : (term1138 z) = term576.
Proof. exact (MK_COMB (@lem2422807 z) (@lem2422808)). Qed.
Lemma lem2422810 (z : int) : (term1137 z) = term576.
Proof. exact (TRANS (@lem2422699 z) (@lem2422809 z)). Qed.
Lemma lem2422811 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2422812 (z : int) : (term1137 z) = term546.
Proof. exact (TRANS (@lem2422810 z) (@lem2422811)). Qed.
Lemma lem2422813 (y : int) (z : int) : (term1136 y z) = term576.
Proof. exact (MK_COMB (@lem2422698 y) (@lem2422812 z)). Qed.
Lemma lem2422814 (y : int) (z : int) : (term1135 y z) = term576.
Proof. exact (TRANS (@lem2422590 y z) (@lem2422813 y z)). Qed.
Lemma lem2422815 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2422816 (y : int) (z : int) : (term1135 y z) = term546.
Proof. exact (TRANS (@lem2422814 y z) (@lem2422815)). Qed.
Lemma lem2422817 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2422818 (y : int) (z : int) : (term1141 y z) = term578.
Proof. exact (MK_COMB (@lem2422817) (@lem2422816 y z)). Qed.
Lemma lem2422819 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2422820 (y : int) (z : int) : (term1134 y z) = term579.
Proof. exact (MK_COMB (@lem2422818 y z) (@lem2422819)). Qed.
Lemma lem2422821 (y : int) (z : int) (h1 : term1111 y z) : term579.
Proof. exact (EQ_MP (@lem2422820 y z) (@lem2422589 y z h1)). Qed.
Lemma lem2422823 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2422824 : term579 = term1099.
Proof. exact (@lem2422823 term182 term546). Qed.
Lemma lem2422826 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2422827 : term546 = term547.
Proof. exact (@lem2422826 term193). Qed.
Lemma lem2422829 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2422830 : term182 = term543.
Proof. exact (@lem2422829 (NUMERAL 0)). Qed.
Lemma lem2422831 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2422832 : term1100 = term1101.
Proof. exact (MK_COMB (@lem2422831) (@lem2422830)). Qed.
Lemma lem2422833 : term1099 = term1102.
Proof. exact (MK_COMB (@lem2422832) (@lem2422827)). Qed.
Lemma lem2422834 : term1103.
Proof. exact (@lem1980026 term182 term192 term546 term192). Qed.
Lemma lem2422836 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422837 : term604 = term605.
Proof. exact (@lem2422836 (NUMERAL 0) term193). Qed.
Lemma lem2422838 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422839 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422840 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422839 h1) (fun h1 : term605 = True => @lem2422838)). Qed.
Lemma lem2422841 : term605 = True.
Proof. exact (EQ_MP (@lem2422840) (@lem2422838)). Qed.
Lemma lem2422842 : term604 = True.
Proof. exact (TRANS (@lem2422837) (@lem2422841)). Qed.
Lemma lem2422843 : True = term604.
Proof. exact (SYM (@lem2422842)). Qed.
Lemma lem2422844 : term604.
Proof. exact (EQ_MP (@lem2422843) (@lem0)). Qed.
Lemma lem2422845 : term1104.
Proof. exact (@lem2422834 (@lem2422844)). Qed.
Lemma lem2422847 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422848 : term604 = term605.
Proof. exact (@lem2422847 (NUMERAL 0) term193). Qed.
Lemma lem2422849 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422850 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422851 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422850 h1) (fun h1 : term605 = True => @lem2422849)). Qed.
Lemma lem2422852 : term605 = True.
Proof. exact (EQ_MP (@lem2422851) (@lem2422849)). Qed.
Lemma lem2422853 : term604 = True.
Proof. exact (TRANS (@lem2422848) (@lem2422852)). Qed.
Lemma lem2422854 : True = term604.
Proof. exact (SYM (@lem2422853)). Qed.
Lemma lem2422855 : term604.
Proof. exact (EQ_MP (@lem2422854) (@lem0)). Qed.
Lemma lem2422856 : term1102 = term1105.
Proof. exact (@lem2422845 (@lem2422855)). Qed.
Lemma lem2422858 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2422859 : term568 = term573.
Proof. exact (@lem2422858 term193 term193). Qed.
Lemma lem2422860 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2422861 : term558 = term193.
Proof. exact (EQ_MP (@lem2422860) (@lem940073)). Qed.
Lemma lem2422862 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2422863 : term556 = term192.
Proof. exact (MK_COMB (@lem2422862) (@lem2422861)). Qed.
Lemma lem2422864 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2422865 : term573 = term546.
Proof. exact (MK_COMB (@lem2422864) (@lem2422863)). Qed.
Lemma lem2422866 : term568 = term546.
Proof. exact (TRANS (@lem2422859) (@lem2422865)). Qed.
Lemma lem2422868 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2422869 : term615 = term182.
Proof. exact (@lem2422868 term193). Qed.
Lemma lem2422870 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2422871 : term1106 = term1100.
Proof. exact (MK_COMB (@lem2422870) (@lem2422869)). Qed.
Lemma lem2422872 : term1105 = term1099.
Proof. exact (MK_COMB (@lem2422871) (@lem2422866)). Qed.
Lemma lem2422874 (m : nat) (n : nat) : (term1107 m n) = (term1108 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2422875 : term1099 = term1109.
Proof. exact (@lem2422874 (NUMERAL 0) term193). Qed.
Lemma lem2422876 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422877 (h1 : term606 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2422878 : (term606 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422877 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem2422876)). Qed.
Lemma lem2422879 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2422878) (@lem2422876)). Qed.
Lemma lem2422880 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2422881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2422882 : term1110 = (and True).
Proof. exact (MK_COMB (@lem2422881) (@lem2422880)). Qed.
Lemma lem2422883 : term1109 = (True /\ False).
Proof. exact (MK_COMB (@lem2422882) (@lem2422879)). Qed.
Lemma lem2422885 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2422886 : term1109 = False.
Proof. exact (TRANS (@lem2422883) (@lem2422885)). Qed.
Lemma lem2422887 : term1099 = False.
Proof. exact (TRANS (@lem2422875) (@lem2422886)). Qed.
Lemma lem2422888 : term1105 = False.
Proof. exact (TRANS (@lem2422872) (@lem2422887)). Qed.
Lemma lem2422889 : term1102 = False.
Proof. exact (TRANS (@lem2422856) (@lem2422888)). Qed.
Lemma lem2422890 : term1099 = False.
Proof. exact (TRANS (@lem2422833) (@lem2422889)). Qed.
Lemma lem2422891 : term579 = False.
Proof. exact (TRANS (@lem2422824) (@lem2422890)). Qed.
Lemma lem2422892 (y : int) (z : int) (h1 : term1111 y z) : False.
Proof. exact (EQ_MP (@lem2422891) (@lem2422821 y z h1)). Qed.
Lemma lem2422893 (y : int) (z : int) (h1 : term1142 y z) : term1142 y z.
Proof. exact (h1). Qed.
Lemma lem2422894 (y : int) (z : int) (h1 : term1142 y z) : term670 y z.
Proof. exact (proj2 (@lem2422893 y z h1)). Qed.
Lemma lem2422895 (y : int) (z : int) (h1 : term1142 y z) : (term620 y z) = term182.
Proof. exact (proj1 (@lem2422893 y z h1)). Qed.
Lemma lem2422897 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2422898 : term1112 = term604.
Proof. exact (@lem2422897 term182 term192). Qed.
Lemma lem2422900 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2422901 : term192 = term567.
Proof. exact (@lem2422900 term193). Qed.
Lemma lem2422903 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2422904 : term182 = term543.
Proof. exact (@lem2422903 (NUMERAL 0)). Qed.
Lemma lem2422905 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2422906 : term1113 = term1114.
Proof. exact (MK_COMB (@lem2422905) (@lem2422904)). Qed.
Lemma lem2422907 : term604 = term1115.
Proof. exact (MK_COMB (@lem2422906) (@lem2422901)). Qed.
Lemma lem2422908 : term1116.
Proof. exact (@lem1980255 term182 term192 term192 term192). Qed.
Lemma lem2422910 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422911 : term604 = term605.
Proof. exact (@lem2422910 (NUMERAL 0) term193). Qed.
Lemma lem2422912 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422913 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422914 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422913 h1) (fun h1 : term605 = True => @lem2422912)). Qed.
Lemma lem2422915 : term605 = True.
Proof. exact (EQ_MP (@lem2422914) (@lem2422912)). Qed.
Lemma lem2422916 : term604 = True.
Proof. exact (TRANS (@lem2422911) (@lem2422915)). Qed.
Lemma lem2422917 : True = term604.
Proof. exact (SYM (@lem2422916)). Qed.
Lemma lem2422918 : term604.
Proof. exact (EQ_MP (@lem2422917) (@lem0)). Qed.
Lemma lem2422919 : term1117.
Proof. exact (@lem2422908 (@lem2422918)). Qed.
Lemma lem2422921 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422922 : term604 = term605.
Proof. exact (@lem2422921 (NUMERAL 0) term193). Qed.
Lemma lem2422923 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422924 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422925 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422924 h1) (fun h1 : term605 = True => @lem2422923)). Qed.
Lemma lem2422926 : term605 = True.
Proof. exact (EQ_MP (@lem2422925) (@lem2422923)). Qed.
Lemma lem2422927 : term604 = True.
Proof. exact (TRANS (@lem2422922) (@lem2422926)). Qed.
Lemma lem2422928 : True = term604.
Proof. exact (SYM (@lem2422927)). Qed.
Lemma lem2422929 : term604.
Proof. exact (EQ_MP (@lem2422928) (@lem0)). Qed.
Lemma lem2422930 : term1115 = term1118.
Proof. exact (@lem2422919 (@lem2422929)). Qed.
Lemma lem2422932 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2422933 : term555 = term556.
Proof. exact (@lem2422932 term193 term193). Qed.
Lemma lem2422934 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2422935 : term558 = term193.
Proof. exact (EQ_MP (@lem2422934) (@lem940073)). Qed.
Lemma lem2422936 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2422937 : term556 = term192.
Proof. exact (MK_COMB (@lem2422936) (@lem2422935)). Qed.
Lemma lem2422938 : term555 = term192.
Proof. exact (TRANS (@lem2422933) (@lem2422937)). Qed.
Lemma lem2422940 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2422941 : term615 = term182.
Proof. exact (@lem2422940 term193). Qed.
Lemma lem2422942 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2422943 : term1119 = term1113.
Proof. exact (MK_COMB (@lem2422942) (@lem2422941)). Qed.
Lemma lem2422944 : term1118 = term604.
Proof. exact (MK_COMB (@lem2422943) (@lem2422938)). Qed.
Lemma lem2422946 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2422947 : term604 = term605.
Proof. exact (@lem2422946 (NUMERAL 0) term193). Qed.
Lemma lem2422948 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2422949 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2422950 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2422949 h1) (fun h1 : term605 = True => @lem2422948)). Qed.
Lemma lem2422951 : term605 = True.
Proof. exact (EQ_MP (@lem2422950) (@lem2422948)). Qed.
Lemma lem2422952 : term604 = True.
Proof. exact (TRANS (@lem2422947) (@lem2422951)). Qed.
Lemma lem2422953 : term1118 = True.
Proof. exact (TRANS (@lem2422944) (@lem2422952)). Qed.
Lemma lem2422954 : term1115 = True.
Proof. exact (TRANS (@lem2422930) (@lem2422953)). Qed.
Lemma lem2422955 : term604 = True.
Proof. exact (TRANS (@lem2422907) (@lem2422954)). Qed.
Lemma lem2422956 : term1112 = True.
Proof. exact (TRANS (@lem2422898) (@lem2422955)). Qed.
Lemma lem2422957 : True = term1112.
Proof. exact (SYM (@lem2422956)). Qed.
Lemma lem2422958 : term1112.
Proof. exact (EQ_MP (@lem2422957) (@lem0)). Qed.
Lemma lem2422959 (y : int) (z : int) (h1 : term1142 y z) : term1143 y z.
Proof. exact (conj (@lem2422958) (@lem2422894 y z h1)). Qed.
Lemma lem2422961 (x : real) (y : real) : term1121 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2422962 (y : int) (z : int) : term1144 y z.
Proof. exact (@lem2422961 term192 (term667 y z)). Qed.
Lemma lem2422963 (y : int) (z : int) (h1 : term1142 y z) : term1145 y z.
Proof. exact (@lem2422962 y z (@lem2422959 y z h1)). Qed.
Lemma lem2422964 (y : int) (z : int) : (term1146 y z) = (term667 y z).
Proof. exact (@lem1982733 (term667 y z)). Qed.
Lemma lem2422965 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2422966 (y : int) (z : int) : (term1147 y z) = (term669 y z).
Proof. exact (MK_COMB (@lem2422965) (@lem2422964 y z)). Qed.
Lemma lem2422967 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2422968 (y : int) (z : int) : (term1145 y z) = (term670 y z).
Proof. exact (MK_COMB (@lem2422966 y z) (@lem2422967)). Qed.
Lemma lem2422969 (y : int) (z : int) (h1 : term1142 y z) : term670 y z.
Proof. exact (EQ_MP (@lem2422968 y z) (@lem2422963 y z h1)). Qed.
Lemma lem2422971 (y : real) : term1126 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2422972 (y : int) (z : int) : term1127 y z.
Proof. exact (@lem2422971 (term620 y z)). Qed.
Lemma lem2422973 (y : int) (z : int) (h1 : term1142 y z) : term1128 y z.
Proof. exact (@lem2422972 y z (@lem2422895 y z h1)). Qed.
Lemma lem2422974 (y : int) (z : int) (h1 : term1142 y z) : term1148 y z.
Proof. exact (@lem2422973 y z h1 term546). Qed.
Lemma lem2422975 (y : int) (z : int) : (term1148 y z) = ((term1149 y z) = term182).
Proof. exact (eq_refl (term1148 y z)). Qed.
Lemma lem2422976 (y : int) (z : int) (h1 : term1142 y z) : (term1149 y z) = term182.
Proof. exact (EQ_MP (@lem2422975 y z) (@lem2422974 y z h1)). Qed.
Lemma lem2422977 (y : int) (z : int) : (term1149 y z) = (term1150 y z).
Proof. exact (@lem1982781 (real_of_int y) term546 (term595 z)). Qed.
Lemma lem2422978 (z : int) : (term641 z) = (term642 z).
Proof. exact (@lem1982749 term546 term546 (real_of_int z)). Qed.
Lemma lem2422980 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2422981 : term546 = term547.
Proof. exact (@lem2422980 term193). Qed.
Lemma lem2422983 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2422984 : term546 = term547.
Proof. exact (@lem2422983 term193). Qed.
Lemma lem2422985 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2422986 : term548 = term549.
Proof. exact (MK_COMB (@lem2422985) (@lem2422984)). Qed.
Lemma lem2422987 : term643 = term644.
Proof. exact (MK_COMB (@lem2422986) (@lem2422981)). Qed.
Lemma lem2422988 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2422990 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2422991 : term555 = term556.
Proof. exact (@lem2422990 term193 term193). Qed.
Lemma lem2422992 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2422993 : term558 = term193.
Proof. exact (EQ_MP (@lem2422992) (@lem940073)). Qed.
Lemma lem2422994 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2422995 : term556 = term192.
Proof. exact (MK_COMB (@lem2422994) (@lem2422993)). Qed.
Lemma lem2422996 : term555 = term192.
Proof. exact (TRANS (@lem2422991) (@lem2422995)). Qed.
Lemma lem2422998 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2422999 : term643 = term556.
Proof. exact (@lem2422998 term193 term193). Qed.
Lemma lem2423000 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423001 : term558 = term193.
Proof. exact (EQ_MP (@lem2423000) (@lem940073)). Qed.
Lemma lem2423002 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423003 : term556 = term192.
Proof. exact (MK_COMB (@lem2423002) (@lem2423001)). Qed.
Lemma lem2423004 : term643 = term192.
Proof. exact (TRANS (@lem2422999) (@lem2423003)). Qed.
Lemma lem2423005 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2423006 : term647 = term648.
Proof. exact (MK_COMB (@lem2423005) (@lem2423004)). Qed.
Lemma lem2423007 : term645 = term567.
Proof. exact (MK_COMB (@lem2423006) (@lem2422996)). Qed.
Lemma lem2423008 : term644 = term567.
Proof. exact (TRANS (@lem2422988) (@lem2423007)). Qed.
Lemma lem2423009 : term643 = term567.
Proof. exact (TRANS (@lem2422987) (@lem2423008)). Qed.
Lemma lem2423011 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2423012 : term567 = term192.
Proof. exact (@lem2423011 term192). Qed.
Lemma lem2423013 : term643 = term192.
Proof. exact (TRANS (@lem2423009) (@lem2423012)). Qed.
Lemma lem2423014 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423015 : term649 = term650.
Proof. exact (MK_COMB (@lem2423014) (@lem2423013)). Qed.
Lemma lem2423016 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2423017 (z : int) : (term642 z) = (term651 z).
Proof. exact (MK_COMB (@lem2423015) (@lem2423016 z)). Qed.
Lemma lem2423018 (z : int) : (term641 z) = (term651 z).
Proof. exact (TRANS (@lem2422978 z) (@lem2423017 z)). Qed.
Lemma lem2423019 (z : int) : (term651 z) = (real_of_int z).
Proof. exact (@lem1982709 (real_of_int z)). Qed.
Lemma lem2423020 (z : int) : (term641 z) = (real_of_int z).
Proof. exact (TRANS (@lem2423018 z) (@lem2423019 z)). Qed.
Lemma lem2423023 (y : int) : (term655 y) = (term655 y).
Proof. exact (eq_refl (term655 y)). Qed.
Lemma lem2423024 (y : int) (z : int) : (term1150 y z) = (term1151 y z).
Proof. exact (MK_COMB (@lem2423023 y) (@lem2423020 z)). Qed.
Lemma lem2423025 (y : int) (z : int) : (term1149 y z) = (term1151 y z).
Proof. exact (TRANS (@lem2422977 y z) (@lem2423024 y z)). Qed.
Lemma lem2423026 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2423027 (y : int) (z : int) : (term1152 y z) = (term1153 y z).
Proof. exact (MK_COMB (@lem2423026) (@lem2423025 y z)). Qed.
Lemma lem2423028 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2423029 (y : int) (z : int) : ((term1149 y z) = term182) = ((term1151 y z) = term182).
Proof. exact (MK_COMB (@lem2423027 y z) (@lem2423028)). Qed.
Lemma lem2423030 (y : int) (z : int) (h1 : term1142 y z) : (term1151 y z) = term182.
Proof. exact (EQ_MP (@lem2423029 y z) (@lem2422976 y z h1)). Qed.
Lemma lem2423031 (y : int) (z : int) (h1 : term1142 y z) : term1154 y z.
Proof. exact (conj (@lem2423030 y z h1) (@lem2422969 y z h1)). Qed.
Lemma lem2423033 (x : real) (y : real) : term1132 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2423034 (y : int) (z : int) : term1155 y z.
Proof. exact (@lem2423033 (term1151 y z) (term667 y z)). Qed.
Lemma lem2423035 (y : int) (z : int) (h1 : term1142 y z) : term1156 y z.
Proof. exact (@lem2423034 y z (@lem2423031 y z h1)). Qed.
Lemma lem2423036 (y : int) (z : int) : (term1157 y z) = (term1158 y z).
Proof. exact (@lem1982753 (term595 y) (real_of_int y) (real_of_int z) (term1159 z)). Qed.
Lemma lem2423037 (y : int) : (term1139 y) = (term597 y).
Proof. exact (@lem1982713 term546 (real_of_int y)). Qed.
Lemma lem2423039 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2423040 : term192 = term567.
Proof. exact (@lem2423039 term193). Qed.
Lemma lem2423042 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2423043 : term546 = term547.
Proof. exact (@lem2423042 term193). Qed.
Lemma lem2423044 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423045 : term598 = term599.
Proof. exact (MK_COMB (@lem2423044) (@lem2423043)). Qed.
Lemma lem2423046 : term600 = term601.
Proof. exact (MK_COMB (@lem2423045) (@lem2423040)). Qed.
Lemma lem2423047 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2423049 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423050 : term604 = term605.
Proof. exact (@lem2423049 (NUMERAL 0) term193). Qed.
Lemma lem2423051 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423052 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423053 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423052 h1) (fun h1 : term605 = True => @lem2423051)). Qed.
Lemma lem2423054 : term605 = True.
Proof. exact (EQ_MP (@lem2423053) (@lem2423051)). Qed.
Lemma lem2423055 : term604 = True.
Proof. exact (TRANS (@lem2423050) (@lem2423054)). Qed.
Lemma lem2423056 : True = term604.
Proof. exact (SYM (@lem2423055)). Qed.
Lemma lem2423057 : term604.
Proof. exact (EQ_MP (@lem2423056) (@lem0)). Qed.
Lemma lem2423058 : term607.
Proof. exact (@lem2423047 (@lem2423057)). Qed.
Lemma lem2423060 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423061 : term604 = term605.
Proof. exact (@lem2423060 (NUMERAL 0) term193). Qed.
Lemma lem2423062 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423063 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423064 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423063 h1) (fun h1 : term605 = True => @lem2423062)). Qed.
Lemma lem2423065 : term605 = True.
Proof. exact (EQ_MP (@lem2423064) (@lem2423062)). Qed.
Lemma lem2423066 : term604 = True.
Proof. exact (TRANS (@lem2423061) (@lem2423065)). Qed.
Lemma lem2423067 : True = term604.
Proof. exact (SYM (@lem2423066)). Qed.
Lemma lem2423068 : term604.
Proof. exact (EQ_MP (@lem2423067) (@lem0)). Qed.
Lemma lem2423069 : term608.
Proof. exact (@lem2423058 (@lem2423068)). Qed.
Lemma lem2423071 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423072 : term604 = term605.
Proof. exact (@lem2423071 (NUMERAL 0) term193). Qed.
Lemma lem2423073 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423074 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423075 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423074 h1) (fun h1 : term605 = True => @lem2423073)). Qed.
Lemma lem2423076 : term605 = True.
Proof. exact (EQ_MP (@lem2423075) (@lem2423073)). Qed.
Lemma lem2423077 : term604 = True.
Proof. exact (TRANS (@lem2423072) (@lem2423076)). Qed.
Lemma lem2423078 : True = term604.
Proof. exact (SYM (@lem2423077)). Qed.
Lemma lem2423079 : term604.
Proof. exact (EQ_MP (@lem2423078) (@lem0)). Qed.
Lemma lem2423080 : term609.
Proof. exact (@lem2423069 (@lem2423079)). Qed.
Lemma lem2423082 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423083 : term555 = term556.
Proof. exact (@lem2423082 term193 term193). Qed.
Lemma lem2423084 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423085 : term558 = term193.
Proof. exact (EQ_MP (@lem2423084) (@lem940073)). Qed.
Lemma lem2423086 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423087 : term556 = term192.
Proof. exact (MK_COMB (@lem2423086) (@lem2423085)). Qed.
Lemma lem2423088 : term555 = term192.
Proof. exact (TRANS (@lem2423083) (@lem2423087)). Qed.
Lemma lem2423090 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2423091 : term568 = term573.
Proof. exact (@lem2423090 term193 term193). Qed.
Lemma lem2423092 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423093 : term558 = term193.
Proof. exact (EQ_MP (@lem2423092) (@lem940073)). Qed.
Lemma lem2423094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423095 : term556 = term192.
Proof. exact (MK_COMB (@lem2423094) (@lem2423093)). Qed.
Lemma lem2423096 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2423097 : term573 = term546.
Proof. exact (MK_COMB (@lem2423096) (@lem2423095)). Qed.
Lemma lem2423098 : term568 = term546.
Proof. exact (TRANS (@lem2423091) (@lem2423097)). Qed.
Lemma lem2423099 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423100 : term610 = term598.
Proof. exact (MK_COMB (@lem2423099) (@lem2423098)). Qed.
Lemma lem2423101 : term611 = term600.
Proof. exact (MK_COMB (@lem2423100) (@lem2423088)). Qed.
Lemma lem2423103 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2423104 : term600 = term182.
Proof. exact (@lem2423103 term193). Qed.
Lemma lem2423105 : term611 = term182.
Proof. exact (TRANS (@lem2423101) (@lem2423104)). Qed.
Lemma lem2423106 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423107 : term613 = term184.
Proof. exact (MK_COMB (@lem2423106) (@lem2423105)). Qed.
Lemma lem2423108 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2423109 : term614 = term615.
Proof. exact (MK_COMB (@lem2423107) (@lem2423108)). Qed.
Lemma lem2423111 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423112 : term615 = term182.
Proof. exact (@lem2423111 term193). Qed.
Lemma lem2423113 : term614 = term182.
Proof. exact (TRANS (@lem2423109) (@lem2423112)). Qed.
Lemma lem2423115 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423116 : term555 = term556.
Proof. exact (@lem2423115 term193 term193). Qed.
Lemma lem2423117 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423118 : term558 = term193.
Proof. exact (EQ_MP (@lem2423117) (@lem940073)). Qed.
Lemma lem2423119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423120 : term556 = term192.
Proof. exact (MK_COMB (@lem2423119) (@lem2423118)). Qed.
Lemma lem2423121 : term555 = term192.
Proof. exact (TRANS (@lem2423116) (@lem2423120)). Qed.
Lemma lem2423122 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2423123 : term617 = term615.
Proof. exact (MK_COMB (@lem2423122) (@lem2423121)). Qed.
Lemma lem2423125 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423126 : term615 = term182.
Proof. exact (@lem2423125 term193). Qed.
Lemma lem2423127 : term617 = term182.
Proof. exact (TRANS (@lem2423123) (@lem2423126)). Qed.
Lemma lem2423128 : term182 = term617.
Proof. exact (SYM (@lem2423127)). Qed.
Lemma lem2423129 : term614 = term617.
Proof. exact (TRANS (@lem2423113) (@lem2423128)). Qed.
Lemma lem2423130 : term601 = term543.
Proof. exact (@lem2423080 (@lem2423129)). Qed.
Lemma lem2423131 : term600 = term543.
Proof. exact (TRANS (@lem2423046) (@lem2423130)). Qed.
Lemma lem2423133 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2423134 : term543 = term182.
Proof. exact (@lem2423133 term182). Qed.
Lemma lem2423135 : term600 = term182.
Proof. exact (TRANS (@lem2423131) (@lem2423134)). Qed.
Lemma lem2423136 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423137 : term618 = term184.
Proof. exact (MK_COMB (@lem2423136) (@lem2423135)). Qed.
Lemma lem2423138 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2423139 (y : int) : (term597 y) = (term185 y).
Proof. exact (MK_COMB (@lem2423137) (@lem2423138 y)). Qed.
Lemma lem2423140 (y : int) : (term1139 y) = (term185 y).
Proof. exact (TRANS (@lem2423037 y) (@lem2423139 y)). Qed.
Lemma lem2423141 (y : int) : (term185 y) = term182.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2423142 (y : int) : (term1139 y) = term182.
Proof. exact (TRANS (@lem2423140 y) (@lem2423141 y)). Qed.
Lemma lem2423143 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423144 (y : int) : (term1140 y) = term206.
Proof. exact (MK_COMB (@lem2423143) (@lem2423142 y)). Qed.
Lemma lem2423145 (z : int) : (term1160 z) = (term1161 z).
Proof. exact (@lem1982763 (real_of_int z) (term595 z) term546). Qed.
Lemma lem2423146 (z : int) : (term596 z) = (term597 z).
Proof. exact (@lem1982715 term546 (real_of_int z)). Qed.
Lemma lem2423148 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2423149 : term192 = term567.
Proof. exact (@lem2423148 term193). Qed.
Lemma lem2423151 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2423152 : term546 = term547.
Proof. exact (@lem2423151 term193). Qed.
Lemma lem2423153 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423154 : term598 = term599.
Proof. exact (MK_COMB (@lem2423153) (@lem2423152)). Qed.
Lemma lem2423155 : term600 = term601.
Proof. exact (MK_COMB (@lem2423154) (@lem2423149)). Qed.
Lemma lem2423156 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2423158 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423159 : term604 = term605.
Proof. exact (@lem2423158 (NUMERAL 0) term193). Qed.
Lemma lem2423160 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423161 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423162 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423161 h1) (fun h1 : term605 = True => @lem2423160)). Qed.
Lemma lem2423163 : term605 = True.
Proof. exact (EQ_MP (@lem2423162) (@lem2423160)). Qed.
Lemma lem2423164 : term604 = True.
Proof. exact (TRANS (@lem2423159) (@lem2423163)). Qed.
Lemma lem2423165 : True = term604.
Proof. exact (SYM (@lem2423164)). Qed.
Lemma lem2423166 : term604.
Proof. exact (EQ_MP (@lem2423165) (@lem0)). Qed.
Lemma lem2423167 : term607.
Proof. exact (@lem2423156 (@lem2423166)). Qed.
Lemma lem2423169 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423170 : term604 = term605.
Proof. exact (@lem2423169 (NUMERAL 0) term193). Qed.
Lemma lem2423171 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423172 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423173 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423172 h1) (fun h1 : term605 = True => @lem2423171)). Qed.
Lemma lem2423174 : term605 = True.
Proof. exact (EQ_MP (@lem2423173) (@lem2423171)). Qed.
Lemma lem2423175 : term604 = True.
Proof. exact (TRANS (@lem2423170) (@lem2423174)). Qed.
Lemma lem2423176 : True = term604.
Proof. exact (SYM (@lem2423175)). Qed.
Lemma lem2423177 : term604.
Proof. exact (EQ_MP (@lem2423176) (@lem0)). Qed.
Lemma lem2423178 : term608.
Proof. exact (@lem2423167 (@lem2423177)). Qed.
Lemma lem2423180 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423181 : term604 = term605.
Proof. exact (@lem2423180 (NUMERAL 0) term193). Qed.
Lemma lem2423182 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423183 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423184 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423183 h1) (fun h1 : term605 = True => @lem2423182)). Qed.
Lemma lem2423185 : term605 = True.
Proof. exact (EQ_MP (@lem2423184) (@lem2423182)). Qed.
Lemma lem2423186 : term604 = True.
Proof. exact (TRANS (@lem2423181) (@lem2423185)). Qed.
Lemma lem2423187 : True = term604.
Proof. exact (SYM (@lem2423186)). Qed.
Lemma lem2423188 : term604.
Proof. exact (EQ_MP (@lem2423187) (@lem0)). Qed.
Lemma lem2423189 : term609.
Proof. exact (@lem2423178 (@lem2423188)). Qed.
Lemma lem2423191 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423192 : term555 = term556.
Proof. exact (@lem2423191 term193 term193). Qed.
Lemma lem2423193 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423194 : term558 = term193.
Proof. exact (EQ_MP (@lem2423193) (@lem940073)). Qed.
Lemma lem2423195 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423196 : term556 = term192.
Proof. exact (MK_COMB (@lem2423195) (@lem2423194)). Qed.
Lemma lem2423197 : term555 = term192.
Proof. exact (TRANS (@lem2423192) (@lem2423196)). Qed.
Lemma lem2423199 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2423200 : term568 = term573.
Proof. exact (@lem2423199 term193 term193). Qed.
Lemma lem2423201 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423202 : term558 = term193.
Proof. exact (EQ_MP (@lem2423201) (@lem940073)). Qed.
Lemma lem2423203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423204 : term556 = term192.
Proof. exact (MK_COMB (@lem2423203) (@lem2423202)). Qed.
Lemma lem2423205 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2423206 : term573 = term546.
Proof. exact (MK_COMB (@lem2423205) (@lem2423204)). Qed.
Lemma lem2423207 : term568 = term546.
Proof. exact (TRANS (@lem2423200) (@lem2423206)). Qed.
Lemma lem2423208 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423209 : term610 = term598.
Proof. exact (MK_COMB (@lem2423208) (@lem2423207)). Qed.
Lemma lem2423210 : term611 = term600.
Proof. exact (MK_COMB (@lem2423209) (@lem2423197)). Qed.
Lemma lem2423212 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2423213 : term600 = term182.
Proof. exact (@lem2423212 term193). Qed.
Lemma lem2423214 : term611 = term182.
Proof. exact (TRANS (@lem2423210) (@lem2423213)). Qed.
Lemma lem2423215 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423216 : term613 = term184.
Proof. exact (MK_COMB (@lem2423215) (@lem2423214)). Qed.
Lemma lem2423217 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2423218 : term614 = term615.
Proof. exact (MK_COMB (@lem2423216) (@lem2423217)). Qed.
Lemma lem2423220 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423221 : term615 = term182.
Proof. exact (@lem2423220 term193). Qed.
Lemma lem2423222 : term614 = term182.
Proof. exact (TRANS (@lem2423218) (@lem2423221)). Qed.
Lemma lem2423224 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423225 : term555 = term556.
Proof. exact (@lem2423224 term193 term193). Qed.
Lemma lem2423226 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423227 : term558 = term193.
Proof. exact (EQ_MP (@lem2423226) (@lem940073)). Qed.
Lemma lem2423228 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423229 : term556 = term192.
Proof. exact (MK_COMB (@lem2423228) (@lem2423227)). Qed.
Lemma lem2423230 : term555 = term192.
Proof. exact (TRANS (@lem2423225) (@lem2423229)). Qed.
Lemma lem2423231 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2423232 : term617 = term615.
Proof. exact (MK_COMB (@lem2423231) (@lem2423230)). Qed.
Lemma lem2423234 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423235 : term615 = term182.
Proof. exact (@lem2423234 term193). Qed.
Lemma lem2423236 : term617 = term182.
Proof. exact (TRANS (@lem2423232) (@lem2423235)). Qed.
Lemma lem2423237 : term182 = term617.
Proof. exact (SYM (@lem2423236)). Qed.
Lemma lem2423238 : term614 = term617.
Proof. exact (TRANS (@lem2423222) (@lem2423237)). Qed.
Lemma lem2423239 : term601 = term543.
Proof. exact (@lem2423189 (@lem2423238)). Qed.
Lemma lem2423240 : term600 = term543.
Proof. exact (TRANS (@lem2423155) (@lem2423239)). Qed.
Lemma lem2423242 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2423243 : term543 = term182.
Proof. exact (@lem2423242 term182). Qed.
Lemma lem2423244 : term600 = term182.
Proof. exact (TRANS (@lem2423240) (@lem2423243)). Qed.
Lemma lem2423245 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423246 : term618 = term184.
Proof. exact (MK_COMB (@lem2423245) (@lem2423244)). Qed.
Lemma lem2423247 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2423248 (z : int) : (term597 z) = (term185 z).
Proof. exact (MK_COMB (@lem2423246) (@lem2423247 z)). Qed.
Lemma lem2423249 (z : int) : (term596 z) = (term185 z).
Proof. exact (TRANS (@lem2423146 z) (@lem2423248 z)). Qed.
Lemma lem2423250 (z : int) : (term185 z) = term182.
Proof. exact (@lem1982719 (real_of_int z)). Qed.
Lemma lem2423251 (z : int) : (term596 z) = term182.
Proof. exact (TRANS (@lem2423249 z) (@lem2423250 z)). Qed.
Lemma lem2423252 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423253 (z : int) : (term619 z) = term206.
Proof. exact (MK_COMB (@lem2423252) (@lem2423251 z)). Qed.
Lemma lem2423254 : term546 = term546.
Proof. exact (eq_refl term546). Qed.
Lemma lem2423255 (z : int) : (term1161 z) = term576.
Proof. exact (MK_COMB (@lem2423253 z) (@lem2423254)). Qed.
Lemma lem2423256 (z : int) : (term1160 z) = term576.
Proof. exact (TRANS (@lem2423145 z) (@lem2423255 z)). Qed.
Lemma lem2423257 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2423258 (z : int) : (term1160 z) = term546.
Proof. exact (TRANS (@lem2423256 z) (@lem2423257)). Qed.
Lemma lem2423259 (y : int) (z : int) : (term1158 y z) = term576.
Proof. exact (MK_COMB (@lem2423144 y) (@lem2423258 z)). Qed.
Lemma lem2423260 (y : int) (z : int) : (term1157 y z) = term576.
Proof. exact (TRANS (@lem2423036 y z) (@lem2423259 y z)). Qed.
Lemma lem2423261 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2423262 (y : int) (z : int) : (term1157 y z) = term546.
Proof. exact (TRANS (@lem2423260 y z) (@lem2423261)). Qed.
Lemma lem2423263 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2423264 (y : int) (z : int) : (term1162 y z) = term578.
Proof. exact (MK_COMB (@lem2423263) (@lem2423262 y z)). Qed.
Lemma lem2423265 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2423266 (y : int) (z : int) : (term1156 y z) = term579.
Proof. exact (MK_COMB (@lem2423264 y z) (@lem2423265)). Qed.
Lemma lem2423267 (y : int) (z : int) (h1 : term1142 y z) : term579.
Proof. exact (EQ_MP (@lem2423266 y z) (@lem2423035 y z h1)). Qed.
Lemma lem2423269 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2423270 : term579 = term1099.
Proof. exact (@lem2423269 term182 term546). Qed.
Lemma lem2423272 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2423273 : term546 = term547.
Proof. exact (@lem2423272 term193). Qed.
Lemma lem2423275 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2423276 : term182 = term543.
Proof. exact (@lem2423275 (NUMERAL 0)). Qed.
Lemma lem2423277 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2423278 : term1100 = term1101.
Proof. exact (MK_COMB (@lem2423277) (@lem2423276)). Qed.
Lemma lem2423279 : term1099 = term1102.
Proof. exact (MK_COMB (@lem2423278) (@lem2423273)). Qed.
Lemma lem2423280 : term1103.
Proof. exact (@lem1980026 term182 term192 term546 term192). Qed.
Lemma lem2423282 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423283 : term604 = term605.
Proof. exact (@lem2423282 (NUMERAL 0) term193). Qed.
Lemma lem2423284 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423285 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423286 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423285 h1) (fun h1 : term605 = True => @lem2423284)). Qed.
Lemma lem2423287 : term605 = True.
Proof. exact (EQ_MP (@lem2423286) (@lem2423284)). Qed.
Lemma lem2423288 : term604 = True.
Proof. exact (TRANS (@lem2423283) (@lem2423287)). Qed.
Lemma lem2423289 : True = term604.
Proof. exact (SYM (@lem2423288)). Qed.
Lemma lem2423290 : term604.
Proof. exact (EQ_MP (@lem2423289) (@lem0)). Qed.
Lemma lem2423291 : term1104.
Proof. exact (@lem2423280 (@lem2423290)). Qed.
Lemma lem2423293 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423294 : term604 = term605.
Proof. exact (@lem2423293 (NUMERAL 0) term193). Qed.
Lemma lem2423295 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423296 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423297 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423296 h1) (fun h1 : term605 = True => @lem2423295)). Qed.
Lemma lem2423298 : term605 = True.
Proof. exact (EQ_MP (@lem2423297) (@lem2423295)). Qed.
Lemma lem2423299 : term604 = True.
Proof. exact (TRANS (@lem2423294) (@lem2423298)). Qed.
Lemma lem2423300 : True = term604.
Proof. exact (SYM (@lem2423299)). Qed.
Lemma lem2423301 : term604.
Proof. exact (EQ_MP (@lem2423300) (@lem0)). Qed.
Lemma lem2423302 : term1102 = term1105.
Proof. exact (@lem2423291 (@lem2423301)). Qed.
Lemma lem2423304 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2423305 : term568 = term573.
Proof. exact (@lem2423304 term193 term193). Qed.
Lemma lem2423306 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423307 : term558 = term193.
Proof. exact (EQ_MP (@lem2423306) (@lem940073)). Qed.
Lemma lem2423308 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423309 : term556 = term192.
Proof. exact (MK_COMB (@lem2423308) (@lem2423307)). Qed.
Lemma lem2423310 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2423311 : term573 = term546.
Proof. exact (MK_COMB (@lem2423310) (@lem2423309)). Qed.
Lemma lem2423312 : term568 = term546.
Proof. exact (TRANS (@lem2423305) (@lem2423311)). Qed.
Lemma lem2423314 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423315 : term615 = term182.
Proof. exact (@lem2423314 term193). Qed.
Lemma lem2423316 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2423317 : term1106 = term1100.
Proof. exact (MK_COMB (@lem2423316) (@lem2423315)). Qed.
Lemma lem2423318 : term1105 = term1099.
Proof. exact (MK_COMB (@lem2423317) (@lem2423312)). Qed.
Lemma lem2423320 (m : nat) (n : nat) : (term1107 m n) = (term1108 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2423321 : term1099 = term1109.
Proof. exact (@lem2423320 (NUMERAL 0) term193). Qed.
Lemma lem2423322 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423323 (h1 : term606 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2423324 : (term606 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423323 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem2423322)). Qed.
Lemma lem2423325 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2423324) (@lem2423322)). Qed.
Lemma lem2423326 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2423327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2423328 : term1110 = (and True).
Proof. exact (MK_COMB (@lem2423327) (@lem2423326)). Qed.
Lemma lem2423329 : term1109 = (True /\ False).
Proof. exact (MK_COMB (@lem2423328) (@lem2423325)). Qed.
Lemma lem2423331 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2423332 : term1109 = False.
Proof. exact (TRANS (@lem2423329) (@lem2423331)). Qed.
Lemma lem2423333 : term1099 = False.
Proof. exact (TRANS (@lem2423321) (@lem2423332)). Qed.
Lemma lem2423334 : term1105 = False.
Proof. exact (TRANS (@lem2423318) (@lem2423333)). Qed.
Lemma lem2423335 : term1102 = False.
Proof. exact (TRANS (@lem2423302) (@lem2423334)). Qed.
Lemma lem2423336 : term1099 = False.
Proof. exact (TRANS (@lem2423279) (@lem2423335)). Qed.
Lemma lem2423337 : term579 = False.
Proof. exact (TRANS (@lem2423270) (@lem2423336)). Qed.
Lemma lem2423338 (y : int) (z : int) (h1 : term1142 y z) : False.
Proof. exact (EQ_MP (@lem2423337) (@lem2423267 y z h1)). Qed.
Lemma lem2423339 (y : int) (z : int) (h1 : term1085 y z) : False.
Proof. exact (or_elim (@lem2422494 y z h1) (fun h0 : term1111 y z => @lem2422892 y z h0) (fun h0 : term1142 y z => @lem2423338 y z h0)). Qed.
Lemma lem2423340 (y : int) (z : int) (h1 : term1084 y z) : term1084 y z.
Proof. exact (h1). Qed.
Lemma lem2423341 (y : int) (z : int) (h1 : term1163 y z) : term1163 y z.
Proof. exact (h1). Qed.
Lemma lem2423342 (y : int) (z : int) (h1 : term1163 y z) : (term620 y z) = term182.
Proof. exact (proj2 (@lem2423341 y z h1)). Qed.
Lemma lem2423343 (y : int) (z : int) (h1 : term1163 y z) : term660 y z.
Proof. exact (proj1 (@lem2423341 y z h1)). Qed.
Lemma lem2423345 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2423346 : term1112 = term604.
Proof. exact (@lem2423345 term182 term192). Qed.
Lemma lem2423348 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2423349 : term192 = term567.
Proof. exact (@lem2423348 term193). Qed.
Lemma lem2423351 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2423352 : term182 = term543.
Proof. exact (@lem2423351 (NUMERAL 0)). Qed.
Lemma lem2423353 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2423354 : term1113 = term1114.
Proof. exact (MK_COMB (@lem2423353) (@lem2423352)). Qed.
Lemma lem2423355 : term604 = term1115.
Proof. exact (MK_COMB (@lem2423354) (@lem2423349)). Qed.
Lemma lem2423356 : term1116.
Proof. exact (@lem1980255 term182 term192 term192 term192). Qed.
Lemma lem2423358 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423359 : term604 = term605.
Proof. exact (@lem2423358 (NUMERAL 0) term193). Qed.
Lemma lem2423360 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423361 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423362 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423361 h1) (fun h1 : term605 = True => @lem2423360)). Qed.
Lemma lem2423363 : term605 = True.
Proof. exact (EQ_MP (@lem2423362) (@lem2423360)). Qed.
Lemma lem2423364 : term604 = True.
Proof. exact (TRANS (@lem2423359) (@lem2423363)). Qed.
Lemma lem2423365 : True = term604.
Proof. exact (SYM (@lem2423364)). Qed.
Lemma lem2423366 : term604.
Proof. exact (EQ_MP (@lem2423365) (@lem0)). Qed.
Lemma lem2423367 : term1117.
Proof. exact (@lem2423356 (@lem2423366)). Qed.
Lemma lem2423369 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423370 : term604 = term605.
Proof. exact (@lem2423369 (NUMERAL 0) term193). Qed.
Lemma lem2423371 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423372 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423373 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423372 h1) (fun h1 : term605 = True => @lem2423371)). Qed.
Lemma lem2423374 : term605 = True.
Proof. exact (EQ_MP (@lem2423373) (@lem2423371)). Qed.
Lemma lem2423375 : term604 = True.
Proof. exact (TRANS (@lem2423370) (@lem2423374)). Qed.
Lemma lem2423376 : True = term604.
Proof. exact (SYM (@lem2423375)). Qed.
Lemma lem2423377 : term604.
Proof. exact (EQ_MP (@lem2423376) (@lem0)). Qed.
Lemma lem2423378 : term1115 = term1118.
Proof. exact (@lem2423367 (@lem2423377)). Qed.
Lemma lem2423380 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423381 : term555 = term556.
Proof. exact (@lem2423380 term193 term193). Qed.
Lemma lem2423382 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423383 : term558 = term193.
Proof. exact (EQ_MP (@lem2423382) (@lem940073)). Qed.
Lemma lem2423384 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423385 : term556 = term192.
Proof. exact (MK_COMB (@lem2423384) (@lem2423383)). Qed.
Lemma lem2423386 : term555 = term192.
Proof. exact (TRANS (@lem2423381) (@lem2423385)). Qed.
Lemma lem2423388 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423389 : term615 = term182.
Proof. exact (@lem2423388 term193). Qed.
Lemma lem2423390 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2423391 : term1119 = term1113.
Proof. exact (MK_COMB (@lem2423390) (@lem2423389)). Qed.
Lemma lem2423392 : term1118 = term604.
Proof. exact (MK_COMB (@lem2423391) (@lem2423386)). Qed.
Lemma lem2423394 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423395 : term604 = term605.
Proof. exact (@lem2423394 (NUMERAL 0) term193). Qed.
Lemma lem2423396 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423397 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423398 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423397 h1) (fun h1 : term605 = True => @lem2423396)). Qed.
Lemma lem2423399 : term605 = True.
Proof. exact (EQ_MP (@lem2423398) (@lem2423396)). Qed.
Lemma lem2423400 : term604 = True.
Proof. exact (TRANS (@lem2423395) (@lem2423399)). Qed.
Lemma lem2423401 : term1118 = True.
Proof. exact (TRANS (@lem2423392) (@lem2423400)). Qed.
Lemma lem2423402 : term1115 = True.
Proof. exact (TRANS (@lem2423378) (@lem2423401)). Qed.
Lemma lem2423403 : term604 = True.
Proof. exact (TRANS (@lem2423355) (@lem2423402)). Qed.
Lemma lem2423404 : term1112 = True.
Proof. exact (TRANS (@lem2423346) (@lem2423403)). Qed.
Lemma lem2423405 : True = term1112.
Proof. exact (SYM (@lem2423404)). Qed.
Lemma lem2423406 : term1112.
Proof. exact (EQ_MP (@lem2423405) (@lem0)). Qed.
Lemma lem2423407 (y : int) (z : int) (h1 : term1163 y z) : term1120 y z.
Proof. exact (conj (@lem2423406) (@lem2423343 y z h1)). Qed.
Lemma lem2423409 (x : real) (y : real) : term1121 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2423410 (y : int) (z : int) : term1122 y z.
Proof. exact (@lem2423409 term192 (term656 y z)). Qed.
Lemma lem2423411 (y : int) (z : int) (h1 : term1163 y z) : term1123 y z.
Proof. exact (@lem2423410 y z (@lem2423407 y z h1)). Qed.
Lemma lem2423412 (y : int) (z : int) : (term1124 y z) = (term656 y z).
Proof. exact (@lem1982733 (term656 y z)). Qed.
Lemma lem2423413 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2423414 (y : int) (z : int) : (term1125 y z) = (term659 y z).
Proof. exact (MK_COMB (@lem2423413) (@lem2423412 y z)). Qed.
Lemma lem2423415 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2423416 (y : int) (z : int) : (term1123 y z) = (term660 y z).
Proof. exact (MK_COMB (@lem2423414 y z) (@lem2423415)). Qed.
Lemma lem2423417 (y : int) (z : int) (h1 : term1163 y z) : term660 y z.
Proof. exact (EQ_MP (@lem2423416 y z) (@lem2423411 y z h1)). Qed.
Lemma lem2423419 (y : real) : term1126 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2423420 (y : int) (z : int) : term1127 y z.
Proof. exact (@lem2423419 (term620 y z)). Qed.
Lemma lem2423421 (y : int) (z : int) (h1 : term1163 y z) : term1128 y z.
Proof. exact (@lem2423420 y z (@lem2423342 y z h1)). Qed.
Lemma lem2423422 (y : int) (z : int) (h1 : term1163 y z) : term1129 y z.
Proof. exact (@lem2423421 y z h1 term192). Qed.
Lemma lem2423423 (y : int) (z : int) : (term1129 y z) = ((term1130 y z) = term182).
Proof. exact (eq_refl (term1129 y z)). Qed.
Lemma lem2423424 (y : int) (z : int) (h1 : term1163 y z) : (term1130 y z) = term182.
Proof. exact (EQ_MP (@lem2423423 y z) (@lem2423422 y z h1)). Qed.
Lemma lem2423425 (y : int) (z : int) : (term1130 y z) = (term620 y z).
Proof. exact (@lem1982733 (term620 y z)). Qed.
Lemma lem2423426 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2423427 (y : int) (z : int) : (term1131 y z) = (term629 y z).
Proof. exact (MK_COMB (@lem2423426) (@lem2423425 y z)). Qed.
Lemma lem2423428 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2423429 (y : int) (z : int) : ((term1130 y z) = term182) = ((term620 y z) = term182).
Proof. exact (MK_COMB (@lem2423427 y z) (@lem2423428)). Qed.
Lemma lem2423430 (y : int) (z : int) (h1 : term1163 y z) : (term620 y z) = term182.
Proof. exact (EQ_MP (@lem2423429 y z) (@lem2423424 y z h1)). Qed.
Lemma lem2423431 (y : int) (z : int) (h1 : term1163 y z) : term1111 y z.
Proof. exact (conj (@lem2423430 y z h1) (@lem2423417 y z h1)). Qed.
Lemma lem2423433 (x : real) (y : real) : term1132 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2423434 (y : int) (z : int) : term1133 y z.
Proof. exact (@lem2423433 (term620 y z) (term656 y z)). Qed.
Lemma lem2423435 (y : int) (z : int) (h1 : term1163 y z) : term1134 y z.
Proof. exact (@lem2423434 y z (@lem2423431 y z h1)). Qed.
Lemma lem2423436 (y : int) (z : int) : (term1135 y z) = (term1136 y z).
Proof. exact (@lem1982753 (real_of_int y) (term595 y) (term595 z) (term654 z)). Qed.
Lemma lem2423437 (y : int) : (term596 y) = (term597 y).
Proof. exact (@lem1982715 term546 (real_of_int y)). Qed.
Lemma lem2423439 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2423440 : term192 = term567.
Proof. exact (@lem2423439 term193). Qed.
Lemma lem2423442 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2423443 : term546 = term547.
Proof. exact (@lem2423442 term193). Qed.
Lemma lem2423444 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423445 : term598 = term599.
Proof. exact (MK_COMB (@lem2423444) (@lem2423443)). Qed.
Lemma lem2423446 : term600 = term601.
Proof. exact (MK_COMB (@lem2423445) (@lem2423440)). Qed.
Lemma lem2423447 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2423449 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423450 : term604 = term605.
Proof. exact (@lem2423449 (NUMERAL 0) term193). Qed.
Lemma lem2423451 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423452 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423453 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423452 h1) (fun h1 : term605 = True => @lem2423451)). Qed.
Lemma lem2423454 : term605 = True.
Proof. exact (EQ_MP (@lem2423453) (@lem2423451)). Qed.
Lemma lem2423455 : term604 = True.
Proof. exact (TRANS (@lem2423450) (@lem2423454)). Qed.
Lemma lem2423456 : True = term604.
Proof. exact (SYM (@lem2423455)). Qed.
Lemma lem2423457 : term604.
Proof. exact (EQ_MP (@lem2423456) (@lem0)). Qed.
Lemma lem2423458 : term607.
Proof. exact (@lem2423447 (@lem2423457)). Qed.
Lemma lem2423460 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423461 : term604 = term605.
Proof. exact (@lem2423460 (NUMERAL 0) term193). Qed.
Lemma lem2423462 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423463 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423464 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423463 h1) (fun h1 : term605 = True => @lem2423462)). Qed.
Lemma lem2423465 : term605 = True.
Proof. exact (EQ_MP (@lem2423464) (@lem2423462)). Qed.
Lemma lem2423466 : term604 = True.
Proof. exact (TRANS (@lem2423461) (@lem2423465)). Qed.
Lemma lem2423467 : True = term604.
Proof. exact (SYM (@lem2423466)). Qed.
Lemma lem2423468 : term604.
Proof. exact (EQ_MP (@lem2423467) (@lem0)). Qed.
Lemma lem2423469 : term608.
Proof. exact (@lem2423458 (@lem2423468)). Qed.
Lemma lem2423471 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423472 : term604 = term605.
Proof. exact (@lem2423471 (NUMERAL 0) term193). Qed.
Lemma lem2423473 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423474 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423475 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423474 h1) (fun h1 : term605 = True => @lem2423473)). Qed.
Lemma lem2423476 : term605 = True.
Proof. exact (EQ_MP (@lem2423475) (@lem2423473)). Qed.
Lemma lem2423477 : term604 = True.
Proof. exact (TRANS (@lem2423472) (@lem2423476)). Qed.
Lemma lem2423478 : True = term604.
Proof. exact (SYM (@lem2423477)). Qed.
Lemma lem2423479 : term604.
Proof. exact (EQ_MP (@lem2423478) (@lem0)). Qed.
Lemma lem2423480 : term609.
Proof. exact (@lem2423469 (@lem2423479)). Qed.
Lemma lem2423482 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423483 : term555 = term556.
Proof. exact (@lem2423482 term193 term193). Qed.
Lemma lem2423484 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423485 : term558 = term193.
Proof. exact (EQ_MP (@lem2423484) (@lem940073)). Qed.
Lemma lem2423486 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423487 : term556 = term192.
Proof. exact (MK_COMB (@lem2423486) (@lem2423485)). Qed.
Lemma lem2423488 : term555 = term192.
Proof. exact (TRANS (@lem2423483) (@lem2423487)). Qed.
Lemma lem2423490 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2423491 : term568 = term573.
Proof. exact (@lem2423490 term193 term193). Qed.
Lemma lem2423492 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423493 : term558 = term193.
Proof. exact (EQ_MP (@lem2423492) (@lem940073)). Qed.
Lemma lem2423494 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423495 : term556 = term192.
Proof. exact (MK_COMB (@lem2423494) (@lem2423493)). Qed.
Lemma lem2423496 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2423497 : term573 = term546.
Proof. exact (MK_COMB (@lem2423496) (@lem2423495)). Qed.
Lemma lem2423498 : term568 = term546.
Proof. exact (TRANS (@lem2423491) (@lem2423497)). Qed.
Lemma lem2423499 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423500 : term610 = term598.
Proof. exact (MK_COMB (@lem2423499) (@lem2423498)). Qed.
Lemma lem2423501 : term611 = term600.
Proof. exact (MK_COMB (@lem2423500) (@lem2423488)). Qed.
Lemma lem2423503 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2423504 : term600 = term182.
Proof. exact (@lem2423503 term193). Qed.
Lemma lem2423505 : term611 = term182.
Proof. exact (TRANS (@lem2423501) (@lem2423504)). Qed.
Lemma lem2423506 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423507 : term613 = term184.
Proof. exact (MK_COMB (@lem2423506) (@lem2423505)). Qed.
Lemma lem2423508 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2423509 : term614 = term615.
Proof. exact (MK_COMB (@lem2423507) (@lem2423508)). Qed.
Lemma lem2423511 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423512 : term615 = term182.
Proof. exact (@lem2423511 term193). Qed.
Lemma lem2423513 : term614 = term182.
Proof. exact (TRANS (@lem2423509) (@lem2423512)). Qed.
Lemma lem2423515 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423516 : term555 = term556.
Proof. exact (@lem2423515 term193 term193). Qed.
Lemma lem2423517 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423518 : term558 = term193.
Proof. exact (EQ_MP (@lem2423517) (@lem940073)). Qed.
Lemma lem2423519 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423520 : term556 = term192.
Proof. exact (MK_COMB (@lem2423519) (@lem2423518)). Qed.
Lemma lem2423521 : term555 = term192.
Proof. exact (TRANS (@lem2423516) (@lem2423520)). Qed.
Lemma lem2423522 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2423523 : term617 = term615.
Proof. exact (MK_COMB (@lem2423522) (@lem2423521)). Qed.
Lemma lem2423525 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423526 : term615 = term182.
Proof. exact (@lem2423525 term193). Qed.
Lemma lem2423527 : term617 = term182.
Proof. exact (TRANS (@lem2423523) (@lem2423526)). Qed.
Lemma lem2423528 : term182 = term617.
Proof. exact (SYM (@lem2423527)). Qed.
Lemma lem2423529 : term614 = term617.
Proof. exact (TRANS (@lem2423513) (@lem2423528)). Qed.
Lemma lem2423530 : term601 = term543.
Proof. exact (@lem2423480 (@lem2423529)). Qed.
Lemma lem2423531 : term600 = term543.
Proof. exact (TRANS (@lem2423446) (@lem2423530)). Qed.
Lemma lem2423533 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2423534 : term543 = term182.
Proof. exact (@lem2423533 term182). Qed.
Lemma lem2423535 : term600 = term182.
Proof. exact (TRANS (@lem2423531) (@lem2423534)). Qed.
Lemma lem2423536 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423537 : term618 = term184.
Proof. exact (MK_COMB (@lem2423536) (@lem2423535)). Qed.
Lemma lem2423538 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2423539 (y : int) : (term597 y) = (term185 y).
Proof. exact (MK_COMB (@lem2423537) (@lem2423538 y)). Qed.
Lemma lem2423540 (y : int) : (term596 y) = (term185 y).
Proof. exact (TRANS (@lem2423437 y) (@lem2423539 y)). Qed.
Lemma lem2423541 (y : int) : (term185 y) = term182.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2423542 (y : int) : (term596 y) = term182.
Proof. exact (TRANS (@lem2423540 y) (@lem2423541 y)). Qed.
Lemma lem2423543 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423544 (y : int) : (term619 y) = term206.
Proof. exact (MK_COMB (@lem2423543) (@lem2423542 y)). Qed.
Lemma lem2423545 (z : int) : (term1137 z) = (term1138 z).
Proof. exact (@lem1982763 (term595 z) (real_of_int z) term546). Qed.
Lemma lem2423546 (z : int) : (term1139 z) = (term597 z).
Proof. exact (@lem1982713 term546 (real_of_int z)). Qed.
Lemma lem2423548 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2423549 : term192 = term567.
Proof. exact (@lem2423548 term193). Qed.
Lemma lem2423551 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2423552 : term546 = term547.
Proof. exact (@lem2423551 term193). Qed.
Lemma lem2423553 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423554 : term598 = term599.
Proof. exact (MK_COMB (@lem2423553) (@lem2423552)). Qed.
Lemma lem2423555 : term600 = term601.
Proof. exact (MK_COMB (@lem2423554) (@lem2423549)). Qed.
Lemma lem2423556 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2423558 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423559 : term604 = term605.
Proof. exact (@lem2423558 (NUMERAL 0) term193). Qed.
Lemma lem2423560 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423561 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423562 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423561 h1) (fun h1 : term605 = True => @lem2423560)). Qed.
Lemma lem2423563 : term605 = True.
Proof. exact (EQ_MP (@lem2423562) (@lem2423560)). Qed.
Lemma lem2423564 : term604 = True.
Proof. exact (TRANS (@lem2423559) (@lem2423563)). Qed.
Lemma lem2423565 : True = term604.
Proof. exact (SYM (@lem2423564)). Qed.
Lemma lem2423566 : term604.
Proof. exact (EQ_MP (@lem2423565) (@lem0)). Qed.
Lemma lem2423567 : term607.
Proof. exact (@lem2423556 (@lem2423566)). Qed.
Lemma lem2423569 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423570 : term604 = term605.
Proof. exact (@lem2423569 (NUMERAL 0) term193). Qed.
Lemma lem2423571 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423572 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423573 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423572 h1) (fun h1 : term605 = True => @lem2423571)). Qed.
Lemma lem2423574 : term605 = True.
Proof. exact (EQ_MP (@lem2423573) (@lem2423571)). Qed.
Lemma lem2423575 : term604 = True.
Proof. exact (TRANS (@lem2423570) (@lem2423574)). Qed.
Lemma lem2423576 : True = term604.
Proof. exact (SYM (@lem2423575)). Qed.
Lemma lem2423577 : term604.
Proof. exact (EQ_MP (@lem2423576) (@lem0)). Qed.
Lemma lem2423578 : term608.
Proof. exact (@lem2423567 (@lem2423577)). Qed.
Lemma lem2423580 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423581 : term604 = term605.
Proof. exact (@lem2423580 (NUMERAL 0) term193). Qed.
Lemma lem2423582 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423583 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423584 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423583 h1) (fun h1 : term605 = True => @lem2423582)). Qed.
Lemma lem2423585 : term605 = True.
Proof. exact (EQ_MP (@lem2423584) (@lem2423582)). Qed.
Lemma lem2423586 : term604 = True.
Proof. exact (TRANS (@lem2423581) (@lem2423585)). Qed.
Lemma lem2423587 : True = term604.
Proof. exact (SYM (@lem2423586)). Qed.
Lemma lem2423588 : term604.
Proof. exact (EQ_MP (@lem2423587) (@lem0)). Qed.
Lemma lem2423589 : term609.
Proof. exact (@lem2423578 (@lem2423588)). Qed.
Lemma lem2423591 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423592 : term555 = term556.
Proof. exact (@lem2423591 term193 term193). Qed.
Lemma lem2423593 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423594 : term558 = term193.
Proof. exact (EQ_MP (@lem2423593) (@lem940073)). Qed.
Lemma lem2423595 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423596 : term556 = term192.
Proof. exact (MK_COMB (@lem2423595) (@lem2423594)). Qed.
Lemma lem2423597 : term555 = term192.
Proof. exact (TRANS (@lem2423592) (@lem2423596)). Qed.
Lemma lem2423599 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2423600 : term568 = term573.
Proof. exact (@lem2423599 term193 term193). Qed.
Lemma lem2423601 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423602 : term558 = term193.
Proof. exact (EQ_MP (@lem2423601) (@lem940073)). Qed.
Lemma lem2423603 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423604 : term556 = term192.
Proof. exact (MK_COMB (@lem2423603) (@lem2423602)). Qed.
Lemma lem2423605 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2423606 : term573 = term546.
Proof. exact (MK_COMB (@lem2423605) (@lem2423604)). Qed.
Lemma lem2423607 : term568 = term546.
Proof. exact (TRANS (@lem2423600) (@lem2423606)). Qed.
Lemma lem2423608 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423609 : term610 = term598.
Proof. exact (MK_COMB (@lem2423608) (@lem2423607)). Qed.
Lemma lem2423610 : term611 = term600.
Proof. exact (MK_COMB (@lem2423609) (@lem2423597)). Qed.
Lemma lem2423612 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2423613 : term600 = term182.
Proof. exact (@lem2423612 term193). Qed.
Lemma lem2423614 : term611 = term182.
Proof. exact (TRANS (@lem2423610) (@lem2423613)). Qed.
Lemma lem2423615 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423616 : term613 = term184.
Proof. exact (MK_COMB (@lem2423615) (@lem2423614)). Qed.
Lemma lem2423617 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2423618 : term614 = term615.
Proof. exact (MK_COMB (@lem2423616) (@lem2423617)). Qed.
Lemma lem2423620 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423621 : term615 = term182.
Proof. exact (@lem2423620 term193). Qed.
Lemma lem2423622 : term614 = term182.
Proof. exact (TRANS (@lem2423618) (@lem2423621)). Qed.
Lemma lem2423624 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423625 : term555 = term556.
Proof. exact (@lem2423624 term193 term193). Qed.
Lemma lem2423626 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423627 : term558 = term193.
Proof. exact (EQ_MP (@lem2423626) (@lem940073)). Qed.
Lemma lem2423628 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423629 : term556 = term192.
Proof. exact (MK_COMB (@lem2423628) (@lem2423627)). Qed.
Lemma lem2423630 : term555 = term192.
Proof. exact (TRANS (@lem2423625) (@lem2423629)). Qed.
Lemma lem2423631 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2423632 : term617 = term615.
Proof. exact (MK_COMB (@lem2423631) (@lem2423630)). Qed.
Lemma lem2423634 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423635 : term615 = term182.
Proof. exact (@lem2423634 term193). Qed.
Lemma lem2423636 : term617 = term182.
Proof. exact (TRANS (@lem2423632) (@lem2423635)). Qed.
Lemma lem2423637 : term182 = term617.
Proof. exact (SYM (@lem2423636)). Qed.
Lemma lem2423638 : term614 = term617.
Proof. exact (TRANS (@lem2423622) (@lem2423637)). Qed.
Lemma lem2423639 : term601 = term543.
Proof. exact (@lem2423589 (@lem2423638)). Qed.
Lemma lem2423640 : term600 = term543.
Proof. exact (TRANS (@lem2423555) (@lem2423639)). Qed.
Lemma lem2423642 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2423643 : term543 = term182.
Proof. exact (@lem2423642 term182). Qed.
Lemma lem2423644 : term600 = term182.
Proof. exact (TRANS (@lem2423640) (@lem2423643)). Qed.
Lemma lem2423645 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423646 : term618 = term184.
Proof. exact (MK_COMB (@lem2423645) (@lem2423644)). Qed.
Lemma lem2423647 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2423648 (z : int) : (term597 z) = (term185 z).
Proof. exact (MK_COMB (@lem2423646) (@lem2423647 z)). Qed.
Lemma lem2423649 (z : int) : (term1139 z) = (term185 z).
Proof. exact (TRANS (@lem2423546 z) (@lem2423648 z)). Qed.
Lemma lem2423650 (z : int) : (term185 z) = term182.
Proof. exact (@lem1982719 (real_of_int z)). Qed.
Lemma lem2423651 (z : int) : (term1139 z) = term182.
Proof. exact (TRANS (@lem2423649 z) (@lem2423650 z)). Qed.
Lemma lem2423652 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423653 (z : int) : (term1140 z) = term206.
Proof. exact (MK_COMB (@lem2423652) (@lem2423651 z)). Qed.
Lemma lem2423654 : term546 = term546.
Proof. exact (eq_refl term546). Qed.
Lemma lem2423655 (z : int) : (term1138 z) = term576.
Proof. exact (MK_COMB (@lem2423653 z) (@lem2423654)). Qed.
Lemma lem2423656 (z : int) : (term1137 z) = term576.
Proof. exact (TRANS (@lem2423545 z) (@lem2423655 z)). Qed.
Lemma lem2423657 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2423658 (z : int) : (term1137 z) = term546.
Proof. exact (TRANS (@lem2423656 z) (@lem2423657)). Qed.
Lemma lem2423659 (y : int) (z : int) : (term1136 y z) = term576.
Proof. exact (MK_COMB (@lem2423544 y) (@lem2423658 z)). Qed.
Lemma lem2423660 (y : int) (z : int) : (term1135 y z) = term576.
Proof. exact (TRANS (@lem2423436 y z) (@lem2423659 y z)). Qed.
Lemma lem2423661 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2423662 (y : int) (z : int) : (term1135 y z) = term546.
Proof. exact (TRANS (@lem2423660 y z) (@lem2423661)). Qed.
Lemma lem2423663 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2423664 (y : int) (z : int) : (term1141 y z) = term578.
Proof. exact (MK_COMB (@lem2423663) (@lem2423662 y z)). Qed.
Lemma lem2423665 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2423666 (y : int) (z : int) : (term1134 y z) = term579.
Proof. exact (MK_COMB (@lem2423664 y z) (@lem2423665)). Qed.
Lemma lem2423667 (y : int) (z : int) (h1 : term1163 y z) : term579.
Proof. exact (EQ_MP (@lem2423666 y z) (@lem2423435 y z h1)). Qed.
Lemma lem2423669 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2423670 : term579 = term1099.
Proof. exact (@lem2423669 term182 term546). Qed.
Lemma lem2423672 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2423673 : term546 = term547.
Proof. exact (@lem2423672 term193). Qed.
Lemma lem2423675 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2423676 : term182 = term543.
Proof. exact (@lem2423675 (NUMERAL 0)). Qed.
Lemma lem2423677 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2423678 : term1100 = term1101.
Proof. exact (MK_COMB (@lem2423677) (@lem2423676)). Qed.
Lemma lem2423679 : term1099 = term1102.
Proof. exact (MK_COMB (@lem2423678) (@lem2423673)). Qed.
Lemma lem2423680 : term1103.
Proof. exact (@lem1980026 term182 term192 term546 term192). Qed.
Lemma lem2423682 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423683 : term604 = term605.
Proof. exact (@lem2423682 (NUMERAL 0) term193). Qed.
Lemma lem2423684 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423685 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423686 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423685 h1) (fun h1 : term605 = True => @lem2423684)). Qed.
Lemma lem2423687 : term605 = True.
Proof. exact (EQ_MP (@lem2423686) (@lem2423684)). Qed.
Lemma lem2423688 : term604 = True.
Proof. exact (TRANS (@lem2423683) (@lem2423687)). Qed.
Lemma lem2423689 : True = term604.
Proof. exact (SYM (@lem2423688)). Qed.
Lemma lem2423690 : term604.
Proof. exact (EQ_MP (@lem2423689) (@lem0)). Qed.
Lemma lem2423691 : term1104.
Proof. exact (@lem2423680 (@lem2423690)). Qed.
Lemma lem2423693 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423694 : term604 = term605.
Proof. exact (@lem2423693 (NUMERAL 0) term193). Qed.
Lemma lem2423695 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423696 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423697 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423696 h1) (fun h1 : term605 = True => @lem2423695)). Qed.
Lemma lem2423698 : term605 = True.
Proof. exact (EQ_MP (@lem2423697) (@lem2423695)). Qed.
Lemma lem2423699 : term604 = True.
Proof. exact (TRANS (@lem2423694) (@lem2423698)). Qed.
Lemma lem2423700 : True = term604.
Proof. exact (SYM (@lem2423699)). Qed.
Lemma lem2423701 : term604.
Proof. exact (EQ_MP (@lem2423700) (@lem0)). Qed.
Lemma lem2423702 : term1102 = term1105.
Proof. exact (@lem2423691 (@lem2423701)). Qed.
Lemma lem2423704 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2423705 : term568 = term573.
Proof. exact (@lem2423704 term193 term193). Qed.
Lemma lem2423706 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423707 : term558 = term193.
Proof. exact (EQ_MP (@lem2423706) (@lem940073)). Qed.
Lemma lem2423708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423709 : term556 = term192.
Proof. exact (MK_COMB (@lem2423708) (@lem2423707)). Qed.
Lemma lem2423710 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2423711 : term573 = term546.
Proof. exact (MK_COMB (@lem2423710) (@lem2423709)). Qed.
Lemma lem2423712 : term568 = term546.
Proof. exact (TRANS (@lem2423705) (@lem2423711)). Qed.
Lemma lem2423714 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423715 : term615 = term182.
Proof. exact (@lem2423714 term193). Qed.
Lemma lem2423716 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2423717 : term1106 = term1100.
Proof. exact (MK_COMB (@lem2423716) (@lem2423715)). Qed.
Lemma lem2423718 : term1105 = term1099.
Proof. exact (MK_COMB (@lem2423717) (@lem2423712)). Qed.
Lemma lem2423720 (m : nat) (n : nat) : (term1107 m n) = (term1108 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2423721 : term1099 = term1109.
Proof. exact (@lem2423720 (NUMERAL 0) term193). Qed.
Lemma lem2423722 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423723 (h1 : term606 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2423724 : (term606 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423723 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem2423722)). Qed.
Lemma lem2423725 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2423724) (@lem2423722)). Qed.
Lemma lem2423726 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2423727 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2423728 : term1110 = (and True).
Proof. exact (MK_COMB (@lem2423727) (@lem2423726)). Qed.
Lemma lem2423729 : term1109 = (True /\ False).
Proof. exact (MK_COMB (@lem2423728) (@lem2423725)). Qed.
Lemma lem2423731 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2423732 : term1109 = False.
Proof. exact (TRANS (@lem2423729) (@lem2423731)). Qed.
Lemma lem2423733 : term1099 = False.
Proof. exact (TRANS (@lem2423721) (@lem2423732)). Qed.
Lemma lem2423734 : term1105 = False.
Proof. exact (TRANS (@lem2423718) (@lem2423733)). Qed.
Lemma lem2423735 : term1102 = False.
Proof. exact (TRANS (@lem2423702) (@lem2423734)). Qed.
Lemma lem2423736 : term1099 = False.
Proof. exact (TRANS (@lem2423679) (@lem2423735)). Qed.
Lemma lem2423737 : term579 = False.
Proof. exact (TRANS (@lem2423670) (@lem2423736)). Qed.
Lemma lem2423738 (y : int) (z : int) (h1 : term1163 y z) : False.
Proof. exact (EQ_MP (@lem2423737) (@lem2423667 y z h1)). Qed.
Lemma lem2423739 (y : int) (z : int) (h1 : term1164 y z) : term1164 y z.
Proof. exact (h1). Qed.
Lemma lem2423740 (y : int) (z : int) (h1 : term1164 y z) : (term620 y z) = term182.
Proof. exact (proj2 (@lem2423739 y z h1)). Qed.
Lemma lem2423741 (y : int) (z : int) (h1 : term1164 y z) : term670 y z.
Proof. exact (proj1 (@lem2423739 y z h1)). Qed.
Lemma lem2423743 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2423744 : term1112 = term604.
Proof. exact (@lem2423743 term182 term192). Qed.
Lemma lem2423746 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2423747 : term192 = term567.
Proof. exact (@lem2423746 term193). Qed.
Lemma lem2423749 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2423750 : term182 = term543.
Proof. exact (@lem2423749 (NUMERAL 0)). Qed.
Lemma lem2423751 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2423752 : term1113 = term1114.
Proof. exact (MK_COMB (@lem2423751) (@lem2423750)). Qed.
Lemma lem2423753 : term604 = term1115.
Proof. exact (MK_COMB (@lem2423752) (@lem2423747)). Qed.
Lemma lem2423754 : term1116.
Proof. exact (@lem1980255 term182 term192 term192 term192). Qed.
Lemma lem2423756 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423757 : term604 = term605.
Proof. exact (@lem2423756 (NUMERAL 0) term193). Qed.
Lemma lem2423758 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423759 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423760 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423759 h1) (fun h1 : term605 = True => @lem2423758)). Qed.
Lemma lem2423761 : term605 = True.
Proof. exact (EQ_MP (@lem2423760) (@lem2423758)). Qed.
Lemma lem2423762 : term604 = True.
Proof. exact (TRANS (@lem2423757) (@lem2423761)). Qed.
Lemma lem2423763 : True = term604.
Proof. exact (SYM (@lem2423762)). Qed.
Lemma lem2423764 : term604.
Proof. exact (EQ_MP (@lem2423763) (@lem0)). Qed.
Lemma lem2423765 : term1117.
Proof. exact (@lem2423754 (@lem2423764)). Qed.
Lemma lem2423767 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423768 : term604 = term605.
Proof. exact (@lem2423767 (NUMERAL 0) term193). Qed.
Lemma lem2423769 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423770 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423771 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423770 h1) (fun h1 : term605 = True => @lem2423769)). Qed.
Lemma lem2423772 : term605 = True.
Proof. exact (EQ_MP (@lem2423771) (@lem2423769)). Qed.
Lemma lem2423773 : term604 = True.
Proof. exact (TRANS (@lem2423768) (@lem2423772)). Qed.
Lemma lem2423774 : True = term604.
Proof. exact (SYM (@lem2423773)). Qed.
Lemma lem2423775 : term604.
Proof. exact (EQ_MP (@lem2423774) (@lem0)). Qed.
Lemma lem2423776 : term1115 = term1118.
Proof. exact (@lem2423765 (@lem2423775)). Qed.
Lemma lem2423778 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423779 : term555 = term556.
Proof. exact (@lem2423778 term193 term193). Qed.
Lemma lem2423780 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423781 : term558 = term193.
Proof. exact (EQ_MP (@lem2423780) (@lem940073)). Qed.
Lemma lem2423782 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423783 : term556 = term192.
Proof. exact (MK_COMB (@lem2423782) (@lem2423781)). Qed.
Lemma lem2423784 : term555 = term192.
Proof. exact (TRANS (@lem2423779) (@lem2423783)). Qed.
Lemma lem2423786 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423787 : term615 = term182.
Proof. exact (@lem2423786 term193). Qed.
Lemma lem2423788 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2423789 : term1119 = term1113.
Proof. exact (MK_COMB (@lem2423788) (@lem2423787)). Qed.
Lemma lem2423790 : term1118 = term604.
Proof. exact (MK_COMB (@lem2423789) (@lem2423784)). Qed.
Lemma lem2423792 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423793 : term604 = term605.
Proof. exact (@lem2423792 (NUMERAL 0) term193). Qed.
Lemma lem2423794 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423795 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423796 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423795 h1) (fun h1 : term605 = True => @lem2423794)). Qed.
Lemma lem2423797 : term605 = True.
Proof. exact (EQ_MP (@lem2423796) (@lem2423794)). Qed.
Lemma lem2423798 : term604 = True.
Proof. exact (TRANS (@lem2423793) (@lem2423797)). Qed.
Lemma lem2423799 : term1118 = True.
Proof. exact (TRANS (@lem2423790) (@lem2423798)). Qed.
Lemma lem2423800 : term1115 = True.
Proof. exact (TRANS (@lem2423776) (@lem2423799)). Qed.
Lemma lem2423801 : term604 = True.
Proof. exact (TRANS (@lem2423753) (@lem2423800)). Qed.
Lemma lem2423802 : term1112 = True.
Proof. exact (TRANS (@lem2423744) (@lem2423801)). Qed.
Lemma lem2423803 : True = term1112.
Proof. exact (SYM (@lem2423802)). Qed.
Lemma lem2423804 : term1112.
Proof. exact (EQ_MP (@lem2423803) (@lem0)). Qed.
Lemma lem2423805 (y : int) (z : int) (h1 : term1164 y z) : term1143 y z.
Proof. exact (conj (@lem2423804) (@lem2423741 y z h1)). Qed.
Lemma lem2423807 (x : real) (y : real) : term1121 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2423808 (y : int) (z : int) : term1144 y z.
Proof. exact (@lem2423807 term192 (term667 y z)). Qed.
Lemma lem2423809 (y : int) (z : int) (h1 : term1164 y z) : term1145 y z.
Proof. exact (@lem2423808 y z (@lem2423805 y z h1)). Qed.
Lemma lem2423810 (y : int) (z : int) : (term1146 y z) = (term667 y z).
Proof. exact (@lem1982733 (term667 y z)). Qed.
Lemma lem2423811 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2423812 (y : int) (z : int) : (term1147 y z) = (term669 y z).
Proof. exact (MK_COMB (@lem2423811) (@lem2423810 y z)). Qed.
Lemma lem2423813 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2423814 (y : int) (z : int) : (term1145 y z) = (term670 y z).
Proof. exact (MK_COMB (@lem2423812 y z) (@lem2423813)). Qed.
Lemma lem2423815 (y : int) (z : int) (h1 : term1164 y z) : term670 y z.
Proof. exact (EQ_MP (@lem2423814 y z) (@lem2423809 y z h1)). Qed.
Lemma lem2423817 (y : real) : term1126 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2423818 (y : int) (z : int) : term1127 y z.
Proof. exact (@lem2423817 (term620 y z)). Qed.
Lemma lem2423819 (y : int) (z : int) (h1 : term1164 y z) : term1128 y z.
Proof. exact (@lem2423818 y z (@lem2423740 y z h1)). Qed.
Lemma lem2423820 (y : int) (z : int) (h1 : term1164 y z) : term1148 y z.
Proof. exact (@lem2423819 y z h1 term546). Qed.
Lemma lem2423821 (y : int) (z : int) : (term1148 y z) = ((term1149 y z) = term182).
Proof. exact (eq_refl (term1148 y z)). Qed.
Lemma lem2423822 (y : int) (z : int) (h1 : term1164 y z) : (term1149 y z) = term182.
Proof. exact (EQ_MP (@lem2423821 y z) (@lem2423820 y z h1)). Qed.
Lemma lem2423823 (y : int) (z : int) : (term1149 y z) = (term1150 y z).
Proof. exact (@lem1982781 (real_of_int y) term546 (term595 z)). Qed.
Lemma lem2423824 (z : int) : (term641 z) = (term642 z).
Proof. exact (@lem1982749 term546 term546 (real_of_int z)). Qed.
Lemma lem2423826 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2423827 : term546 = term547.
Proof. exact (@lem2423826 term193). Qed.
Lemma lem2423829 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2423830 : term546 = term547.
Proof. exact (@lem2423829 term193). Qed.
Lemma lem2423831 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423832 : term548 = term549.
Proof. exact (MK_COMB (@lem2423831) (@lem2423830)). Qed.
Lemma lem2423833 : term643 = term644.
Proof. exact (MK_COMB (@lem2423832) (@lem2423827)). Qed.
Lemma lem2423834 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2423836 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423837 : term555 = term556.
Proof. exact (@lem2423836 term193 term193). Qed.
Lemma lem2423838 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423839 : term558 = term193.
Proof. exact (EQ_MP (@lem2423838) (@lem940073)). Qed.
Lemma lem2423840 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423841 : term556 = term192.
Proof. exact (MK_COMB (@lem2423840) (@lem2423839)). Qed.
Lemma lem2423842 : term555 = term192.
Proof. exact (TRANS (@lem2423837) (@lem2423841)). Qed.
Lemma lem2423844 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2423845 : term643 = term556.
Proof. exact (@lem2423844 term193 term193). Qed.
Lemma lem2423846 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423847 : term558 = term193.
Proof. exact (EQ_MP (@lem2423846) (@lem940073)). Qed.
Lemma lem2423848 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423849 : term556 = term192.
Proof. exact (MK_COMB (@lem2423848) (@lem2423847)). Qed.
Lemma lem2423850 : term643 = term192.
Proof. exact (TRANS (@lem2423845) (@lem2423849)). Qed.
Lemma lem2423851 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2423852 : term647 = term648.
Proof. exact (MK_COMB (@lem2423851) (@lem2423850)). Qed.
Lemma lem2423853 : term645 = term567.
Proof. exact (MK_COMB (@lem2423852) (@lem2423842)). Qed.
Lemma lem2423854 : term644 = term567.
Proof. exact (TRANS (@lem2423834) (@lem2423853)). Qed.
Lemma lem2423855 : term643 = term567.
Proof. exact (TRANS (@lem2423833) (@lem2423854)). Qed.
Lemma lem2423857 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2423858 : term567 = term192.
Proof. exact (@lem2423857 term192). Qed.
Lemma lem2423859 : term643 = term192.
Proof. exact (TRANS (@lem2423855) (@lem2423858)). Qed.
Lemma lem2423860 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423861 : term649 = term650.
Proof. exact (MK_COMB (@lem2423860) (@lem2423859)). Qed.
Lemma lem2423862 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2423863 (z : int) : (term642 z) = (term651 z).
Proof. exact (MK_COMB (@lem2423861) (@lem2423862 z)). Qed.
Lemma lem2423864 (z : int) : (term641 z) = (term651 z).
Proof. exact (TRANS (@lem2423824 z) (@lem2423863 z)). Qed.
Lemma lem2423865 (z : int) : (term651 z) = (real_of_int z).
Proof. exact (@lem1982709 (real_of_int z)). Qed.
Lemma lem2423866 (z : int) : (term641 z) = (real_of_int z).
Proof. exact (TRANS (@lem2423864 z) (@lem2423865 z)). Qed.
Lemma lem2423869 (y : int) : (term655 y) = (term655 y).
Proof. exact (eq_refl (term655 y)). Qed.
Lemma lem2423870 (y : int) (z : int) : (term1150 y z) = (term1151 y z).
Proof. exact (MK_COMB (@lem2423869 y) (@lem2423866 z)). Qed.
Lemma lem2423871 (y : int) (z : int) : (term1149 y z) = (term1151 y z).
Proof. exact (TRANS (@lem2423823 y z) (@lem2423870 y z)). Qed.
Lemma lem2423872 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2423873 (y : int) (z : int) : (term1152 y z) = (term1153 y z).
Proof. exact (MK_COMB (@lem2423872) (@lem2423871 y z)). Qed.
Lemma lem2423874 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2423875 (y : int) (z : int) : ((term1149 y z) = term182) = ((term1151 y z) = term182).
Proof. exact (MK_COMB (@lem2423873 y z) (@lem2423874)). Qed.
Lemma lem2423876 (y : int) (z : int) (h1 : term1164 y z) : (term1151 y z) = term182.
Proof. exact (EQ_MP (@lem2423875 y z) (@lem2423822 y z h1)). Qed.
Lemma lem2423877 (y : int) (z : int) (h1 : term1164 y z) : term1154 y z.
Proof. exact (conj (@lem2423876 y z h1) (@lem2423815 y z h1)). Qed.
Lemma lem2423879 (x : real) (y : real) : term1132 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2423880 (y : int) (z : int) : term1155 y z.
Proof. exact (@lem2423879 (term1151 y z) (term667 y z)). Qed.
Lemma lem2423881 (y : int) (z : int) (h1 : term1164 y z) : term1156 y z.
Proof. exact (@lem2423880 y z (@lem2423877 y z h1)). Qed.
Lemma lem2423882 (y : int) (z : int) : (term1157 y z) = (term1158 y z).
Proof. exact (@lem1982753 (term595 y) (real_of_int y) (real_of_int z) (term1159 z)). Qed.
Lemma lem2423883 (y : int) : (term1139 y) = (term597 y).
Proof. exact (@lem1982713 term546 (real_of_int y)). Qed.
Lemma lem2423885 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2423886 : term192 = term567.
Proof. exact (@lem2423885 term193). Qed.
Lemma lem2423888 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2423889 : term546 = term547.
Proof. exact (@lem2423888 term193). Qed.
Lemma lem2423890 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423891 : term598 = term599.
Proof. exact (MK_COMB (@lem2423890) (@lem2423889)). Qed.
Lemma lem2423892 : term600 = term601.
Proof. exact (MK_COMB (@lem2423891) (@lem2423886)). Qed.
Lemma lem2423893 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2423895 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423896 : term604 = term605.
Proof. exact (@lem2423895 (NUMERAL 0) term193). Qed.
Lemma lem2423897 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423898 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423899 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423898 h1) (fun h1 : term605 = True => @lem2423897)). Qed.
Lemma lem2423900 : term605 = True.
Proof. exact (EQ_MP (@lem2423899) (@lem2423897)). Qed.
Lemma lem2423901 : term604 = True.
Proof. exact (TRANS (@lem2423896) (@lem2423900)). Qed.
Lemma lem2423902 : True = term604.
Proof. exact (SYM (@lem2423901)). Qed.
Lemma lem2423903 : term604.
Proof. exact (EQ_MP (@lem2423902) (@lem0)). Qed.
Lemma lem2423904 : term607.
Proof. exact (@lem2423893 (@lem2423903)). Qed.
Lemma lem2423906 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423907 : term604 = term605.
Proof. exact (@lem2423906 (NUMERAL 0) term193). Qed.
Lemma lem2423908 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423909 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423910 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423909 h1) (fun h1 : term605 = True => @lem2423908)). Qed.
Lemma lem2423911 : term605 = True.
Proof. exact (EQ_MP (@lem2423910) (@lem2423908)). Qed.
Lemma lem2423912 : term604 = True.
Proof. exact (TRANS (@lem2423907) (@lem2423911)). Qed.
Lemma lem2423913 : True = term604.
Proof. exact (SYM (@lem2423912)). Qed.
Lemma lem2423914 : term604.
Proof. exact (EQ_MP (@lem2423913) (@lem0)). Qed.
Lemma lem2423915 : term608.
Proof. exact (@lem2423904 (@lem2423914)). Qed.
Lemma lem2423917 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2423918 : term604 = term605.
Proof. exact (@lem2423917 (NUMERAL 0) term193). Qed.
Lemma lem2423919 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2423920 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2423921 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2423920 h1) (fun h1 : term605 = True => @lem2423919)). Qed.
Lemma lem2423922 : term605 = True.
Proof. exact (EQ_MP (@lem2423921) (@lem2423919)). Qed.
Lemma lem2423923 : term604 = True.
Proof. exact (TRANS (@lem2423918) (@lem2423922)). Qed.
Lemma lem2423924 : True = term604.
Proof. exact (SYM (@lem2423923)). Qed.
Lemma lem2423925 : term604.
Proof. exact (EQ_MP (@lem2423924) (@lem0)). Qed.
Lemma lem2423926 : term609.
Proof. exact (@lem2423915 (@lem2423925)). Qed.
Lemma lem2423928 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423929 : term555 = term556.
Proof. exact (@lem2423928 term193 term193). Qed.
Lemma lem2423930 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423931 : term558 = term193.
Proof. exact (EQ_MP (@lem2423930) (@lem940073)). Qed.
Lemma lem2423932 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423933 : term556 = term192.
Proof. exact (MK_COMB (@lem2423932) (@lem2423931)). Qed.
Lemma lem2423934 : term555 = term192.
Proof. exact (TRANS (@lem2423929) (@lem2423933)). Qed.
Lemma lem2423936 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2423937 : term568 = term573.
Proof. exact (@lem2423936 term193 term193). Qed.
Lemma lem2423938 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423939 : term558 = term193.
Proof. exact (EQ_MP (@lem2423938) (@lem940073)). Qed.
Lemma lem2423940 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423941 : term556 = term192.
Proof. exact (MK_COMB (@lem2423940) (@lem2423939)). Qed.
Lemma lem2423942 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2423943 : term573 = term546.
Proof. exact (MK_COMB (@lem2423942) (@lem2423941)). Qed.
Lemma lem2423944 : term568 = term546.
Proof. exact (TRANS (@lem2423937) (@lem2423943)). Qed.
Lemma lem2423945 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423946 : term610 = term598.
Proof. exact (MK_COMB (@lem2423945) (@lem2423944)). Qed.
Lemma lem2423947 : term611 = term600.
Proof. exact (MK_COMB (@lem2423946) (@lem2423934)). Qed.
Lemma lem2423949 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2423950 : term600 = term182.
Proof. exact (@lem2423949 term193). Qed.
Lemma lem2423951 : term611 = term182.
Proof. exact (TRANS (@lem2423947) (@lem2423950)). Qed.
Lemma lem2423952 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423953 : term613 = term184.
Proof. exact (MK_COMB (@lem2423952) (@lem2423951)). Qed.
Lemma lem2423954 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2423955 : term614 = term615.
Proof. exact (MK_COMB (@lem2423953) (@lem2423954)). Qed.
Lemma lem2423957 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423958 : term615 = term182.
Proof. exact (@lem2423957 term193). Qed.
Lemma lem2423959 : term614 = term182.
Proof. exact (TRANS (@lem2423955) (@lem2423958)). Qed.
Lemma lem2423961 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2423962 : term555 = term556.
Proof. exact (@lem2423961 term193 term193). Qed.
Lemma lem2423963 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2423964 : term558 = term193.
Proof. exact (EQ_MP (@lem2423963) (@lem940073)). Qed.
Lemma lem2423965 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2423966 : term556 = term192.
Proof. exact (MK_COMB (@lem2423965) (@lem2423964)). Qed.
Lemma lem2423967 : term555 = term192.
Proof. exact (TRANS (@lem2423962) (@lem2423966)). Qed.
Lemma lem2423968 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2423969 : term617 = term615.
Proof. exact (MK_COMB (@lem2423968) (@lem2423967)). Qed.
Lemma lem2423971 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2423972 : term615 = term182.
Proof. exact (@lem2423971 term193). Qed.
Lemma lem2423973 : term617 = term182.
Proof. exact (TRANS (@lem2423969) (@lem2423972)). Qed.
Lemma lem2423974 : term182 = term617.
Proof. exact (SYM (@lem2423973)). Qed.
Lemma lem2423975 : term614 = term617.
Proof. exact (TRANS (@lem2423959) (@lem2423974)). Qed.
Lemma lem2423976 : term601 = term543.
Proof. exact (@lem2423926 (@lem2423975)). Qed.
Lemma lem2423977 : term600 = term543.
Proof. exact (TRANS (@lem2423892) (@lem2423976)). Qed.
Lemma lem2423979 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2423980 : term543 = term182.
Proof. exact (@lem2423979 term182). Qed.
Lemma lem2423981 : term600 = term182.
Proof. exact (TRANS (@lem2423977) (@lem2423980)). Qed.
Lemma lem2423982 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2423983 : term618 = term184.
Proof. exact (MK_COMB (@lem2423982) (@lem2423981)). Qed.
Lemma lem2423984 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2423985 (y : int) : (term597 y) = (term185 y).
Proof. exact (MK_COMB (@lem2423983) (@lem2423984 y)). Qed.
Lemma lem2423986 (y : int) : (term1139 y) = (term185 y).
Proof. exact (TRANS (@lem2423883 y) (@lem2423985 y)). Qed.
Lemma lem2423987 (y : int) : (term185 y) = term182.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2423988 (y : int) : (term1139 y) = term182.
Proof. exact (TRANS (@lem2423986 y) (@lem2423987 y)). Qed.
Lemma lem2423989 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2423990 (y : int) : (term1140 y) = term206.
Proof. exact (MK_COMB (@lem2423989) (@lem2423988 y)). Qed.
Lemma lem2423991 (z : int) : (term1160 z) = (term1161 z).
Proof. exact (@lem1982763 (real_of_int z) (term595 z) term546). Qed.
Lemma lem2423992 (z : int) : (term596 z) = (term597 z).
Proof. exact (@lem1982715 term546 (real_of_int z)). Qed.
Lemma lem2423994 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2423995 : term192 = term567.
Proof. exact (@lem2423994 term193). Qed.
Lemma lem2423997 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2423998 : term546 = term547.
Proof. exact (@lem2423997 term193). Qed.
Lemma lem2423999 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424000 : term598 = term599.
Proof. exact (MK_COMB (@lem2423999) (@lem2423998)). Qed.
Lemma lem2424001 : term600 = term601.
Proof. exact (MK_COMB (@lem2424000) (@lem2423995)). Qed.
Lemma lem2424002 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2424004 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424005 : term604 = term605.
Proof. exact (@lem2424004 (NUMERAL 0) term193). Qed.
Lemma lem2424006 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424007 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424008 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424007 h1) (fun h1 : term605 = True => @lem2424006)). Qed.
Lemma lem2424009 : term605 = True.
Proof. exact (EQ_MP (@lem2424008) (@lem2424006)). Qed.
Lemma lem2424010 : term604 = True.
Proof. exact (TRANS (@lem2424005) (@lem2424009)). Qed.
Lemma lem2424011 : True = term604.
Proof. exact (SYM (@lem2424010)). Qed.
Lemma lem2424012 : term604.
Proof. exact (EQ_MP (@lem2424011) (@lem0)). Qed.
Lemma lem2424013 : term607.
Proof. exact (@lem2424002 (@lem2424012)). Qed.
Lemma lem2424015 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424016 : term604 = term605.
Proof. exact (@lem2424015 (NUMERAL 0) term193). Qed.
Lemma lem2424017 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424018 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424019 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424018 h1) (fun h1 : term605 = True => @lem2424017)). Qed.
Lemma lem2424020 : term605 = True.
Proof. exact (EQ_MP (@lem2424019) (@lem2424017)). Qed.
Lemma lem2424021 : term604 = True.
Proof. exact (TRANS (@lem2424016) (@lem2424020)). Qed.
Lemma lem2424022 : True = term604.
Proof. exact (SYM (@lem2424021)). Qed.
Lemma lem2424023 : term604.
Proof. exact (EQ_MP (@lem2424022) (@lem0)). Qed.
Lemma lem2424024 : term608.
Proof. exact (@lem2424013 (@lem2424023)). Qed.
Lemma lem2424026 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424027 : term604 = term605.
Proof. exact (@lem2424026 (NUMERAL 0) term193). Qed.
Lemma lem2424028 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424029 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424030 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424029 h1) (fun h1 : term605 = True => @lem2424028)). Qed.
Lemma lem2424031 : term605 = True.
Proof. exact (EQ_MP (@lem2424030) (@lem2424028)). Qed.
Lemma lem2424032 : term604 = True.
Proof. exact (TRANS (@lem2424027) (@lem2424031)). Qed.
Lemma lem2424033 : True = term604.
Proof. exact (SYM (@lem2424032)). Qed.
Lemma lem2424034 : term604.
Proof. exact (EQ_MP (@lem2424033) (@lem0)). Qed.
Lemma lem2424035 : term609.
Proof. exact (@lem2424024 (@lem2424034)). Qed.
Lemma lem2424037 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424038 : term555 = term556.
Proof. exact (@lem2424037 term193 term193). Qed.
Lemma lem2424039 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424040 : term558 = term193.
Proof. exact (EQ_MP (@lem2424039) (@lem940073)). Qed.
Lemma lem2424041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424042 : term556 = term192.
Proof. exact (MK_COMB (@lem2424041) (@lem2424040)). Qed.
Lemma lem2424043 : term555 = term192.
Proof. exact (TRANS (@lem2424038) (@lem2424042)). Qed.
Lemma lem2424045 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2424046 : term568 = term573.
Proof. exact (@lem2424045 term193 term193). Qed.
Lemma lem2424047 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424048 : term558 = term193.
Proof. exact (EQ_MP (@lem2424047) (@lem940073)). Qed.
Lemma lem2424049 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424050 : term556 = term192.
Proof. exact (MK_COMB (@lem2424049) (@lem2424048)). Qed.
Lemma lem2424051 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2424052 : term573 = term546.
Proof. exact (MK_COMB (@lem2424051) (@lem2424050)). Qed.
Lemma lem2424053 : term568 = term546.
Proof. exact (TRANS (@lem2424046) (@lem2424052)). Qed.
Lemma lem2424054 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424055 : term610 = term598.
Proof. exact (MK_COMB (@lem2424054) (@lem2424053)). Qed.
Lemma lem2424056 : term611 = term600.
Proof. exact (MK_COMB (@lem2424055) (@lem2424043)). Qed.
Lemma lem2424058 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2424059 : term600 = term182.
Proof. exact (@lem2424058 term193). Qed.
Lemma lem2424060 : term611 = term182.
Proof. exact (TRANS (@lem2424056) (@lem2424059)). Qed.
Lemma lem2424061 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424062 : term613 = term184.
Proof. exact (MK_COMB (@lem2424061) (@lem2424060)). Qed.
Lemma lem2424063 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2424064 : term614 = term615.
Proof. exact (MK_COMB (@lem2424062) (@lem2424063)). Qed.
Lemma lem2424066 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424067 : term615 = term182.
Proof. exact (@lem2424066 term193). Qed.
Lemma lem2424068 : term614 = term182.
Proof. exact (TRANS (@lem2424064) (@lem2424067)). Qed.
Lemma lem2424070 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424071 : term555 = term556.
Proof. exact (@lem2424070 term193 term193). Qed.
Lemma lem2424072 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424073 : term558 = term193.
Proof. exact (EQ_MP (@lem2424072) (@lem940073)). Qed.
Lemma lem2424074 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424075 : term556 = term192.
Proof. exact (MK_COMB (@lem2424074) (@lem2424073)). Qed.
Lemma lem2424076 : term555 = term192.
Proof. exact (TRANS (@lem2424071) (@lem2424075)). Qed.
Lemma lem2424077 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2424078 : term617 = term615.
Proof. exact (MK_COMB (@lem2424077) (@lem2424076)). Qed.
Lemma lem2424080 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424081 : term615 = term182.
Proof. exact (@lem2424080 term193). Qed.
Lemma lem2424082 : term617 = term182.
Proof. exact (TRANS (@lem2424078) (@lem2424081)). Qed.
Lemma lem2424083 : term182 = term617.
Proof. exact (SYM (@lem2424082)). Qed.
Lemma lem2424084 : term614 = term617.
Proof. exact (TRANS (@lem2424068) (@lem2424083)). Qed.
Lemma lem2424085 : term601 = term543.
Proof. exact (@lem2424035 (@lem2424084)). Qed.
Lemma lem2424086 : term600 = term543.
Proof. exact (TRANS (@lem2424001) (@lem2424085)). Qed.
Lemma lem2424088 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2424089 : term543 = term182.
Proof. exact (@lem2424088 term182). Qed.
Lemma lem2424090 : term600 = term182.
Proof. exact (TRANS (@lem2424086) (@lem2424089)). Qed.
Lemma lem2424091 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424092 : term618 = term184.
Proof. exact (MK_COMB (@lem2424091) (@lem2424090)). Qed.
Lemma lem2424093 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2424094 (z : int) : (term597 z) = (term185 z).
Proof. exact (MK_COMB (@lem2424092) (@lem2424093 z)). Qed.
Lemma lem2424095 (z : int) : (term596 z) = (term185 z).
Proof. exact (TRANS (@lem2423992 z) (@lem2424094 z)). Qed.
Lemma lem2424096 (z : int) : (term185 z) = term182.
Proof. exact (@lem1982719 (real_of_int z)). Qed.
Lemma lem2424097 (z : int) : (term596 z) = term182.
Proof. exact (TRANS (@lem2424095 z) (@lem2424096 z)). Qed.
Lemma lem2424098 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424099 (z : int) : (term619 z) = term206.
Proof. exact (MK_COMB (@lem2424098) (@lem2424097 z)). Qed.
Lemma lem2424100 : term546 = term546.
Proof. exact (eq_refl term546). Qed.
Lemma lem2424101 (z : int) : (term1161 z) = term576.
Proof. exact (MK_COMB (@lem2424099 z) (@lem2424100)). Qed.
Lemma lem2424102 (z : int) : (term1160 z) = term576.
Proof. exact (TRANS (@lem2423991 z) (@lem2424101 z)). Qed.
Lemma lem2424103 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2424104 (z : int) : (term1160 z) = term546.
Proof. exact (TRANS (@lem2424102 z) (@lem2424103)). Qed.
Lemma lem2424105 (y : int) (z : int) : (term1158 y z) = term576.
Proof. exact (MK_COMB (@lem2423990 y) (@lem2424104 z)). Qed.
Lemma lem2424106 (y : int) (z : int) : (term1157 y z) = term576.
Proof. exact (TRANS (@lem2423882 y z) (@lem2424105 y z)). Qed.
Lemma lem2424107 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2424108 (y : int) (z : int) : (term1157 y z) = term546.
Proof. exact (TRANS (@lem2424106 y z) (@lem2424107)). Qed.
Lemma lem2424109 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2424110 (y : int) (z : int) : (term1162 y z) = term578.
Proof. exact (MK_COMB (@lem2424109) (@lem2424108 y z)). Qed.
Lemma lem2424111 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2424112 (y : int) (z : int) : (term1156 y z) = term579.
Proof. exact (MK_COMB (@lem2424110 y z) (@lem2424111)). Qed.
Lemma lem2424113 (y : int) (z : int) (h1 : term1164 y z) : term579.
Proof. exact (EQ_MP (@lem2424112 y z) (@lem2423881 y z h1)). Qed.
Lemma lem2424115 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2424116 : term579 = term1099.
Proof. exact (@lem2424115 term182 term546). Qed.
Lemma lem2424118 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2424119 : term546 = term547.
Proof. exact (@lem2424118 term193). Qed.
Lemma lem2424121 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2424122 : term182 = term543.
Proof. exact (@lem2424121 (NUMERAL 0)). Qed.
Lemma lem2424123 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2424124 : term1100 = term1101.
Proof. exact (MK_COMB (@lem2424123) (@lem2424122)). Qed.
Lemma lem2424125 : term1099 = term1102.
Proof. exact (MK_COMB (@lem2424124) (@lem2424119)). Qed.
Lemma lem2424126 : term1103.
Proof. exact (@lem1980026 term182 term192 term546 term192). Qed.
Lemma lem2424128 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424129 : term604 = term605.
Proof. exact (@lem2424128 (NUMERAL 0) term193). Qed.
Lemma lem2424130 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424131 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424132 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424131 h1) (fun h1 : term605 = True => @lem2424130)). Qed.
Lemma lem2424133 : term605 = True.
Proof. exact (EQ_MP (@lem2424132) (@lem2424130)). Qed.
Lemma lem2424134 : term604 = True.
Proof. exact (TRANS (@lem2424129) (@lem2424133)). Qed.
Lemma lem2424135 : True = term604.
Proof. exact (SYM (@lem2424134)). Qed.
Lemma lem2424136 : term604.
Proof. exact (EQ_MP (@lem2424135) (@lem0)). Qed.
Lemma lem2424137 : term1104.
Proof. exact (@lem2424126 (@lem2424136)). Qed.
Lemma lem2424139 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424140 : term604 = term605.
Proof. exact (@lem2424139 (NUMERAL 0) term193). Qed.
Lemma lem2424141 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424142 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424143 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424142 h1) (fun h1 : term605 = True => @lem2424141)). Qed.
Lemma lem2424144 : term605 = True.
Proof. exact (EQ_MP (@lem2424143) (@lem2424141)). Qed.
Lemma lem2424145 : term604 = True.
Proof. exact (TRANS (@lem2424140) (@lem2424144)). Qed.
Lemma lem2424146 : True = term604.
Proof. exact (SYM (@lem2424145)). Qed.
Lemma lem2424147 : term604.
Proof. exact (EQ_MP (@lem2424146) (@lem0)). Qed.
Lemma lem2424148 : term1102 = term1105.
Proof. exact (@lem2424137 (@lem2424147)). Qed.
Lemma lem2424150 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2424151 : term568 = term573.
Proof. exact (@lem2424150 term193 term193). Qed.
Lemma lem2424152 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424153 : term558 = term193.
Proof. exact (EQ_MP (@lem2424152) (@lem940073)). Qed.
Lemma lem2424154 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424155 : term556 = term192.
Proof. exact (MK_COMB (@lem2424154) (@lem2424153)). Qed.
Lemma lem2424156 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2424157 : term573 = term546.
Proof. exact (MK_COMB (@lem2424156) (@lem2424155)). Qed.
Lemma lem2424158 : term568 = term546.
Proof. exact (TRANS (@lem2424151) (@lem2424157)). Qed.
Lemma lem2424160 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424161 : term615 = term182.
Proof. exact (@lem2424160 term193). Qed.
Lemma lem2424162 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2424163 : term1106 = term1100.
Proof. exact (MK_COMB (@lem2424162) (@lem2424161)). Qed.
Lemma lem2424164 : term1105 = term1099.
Proof. exact (MK_COMB (@lem2424163) (@lem2424158)). Qed.
Lemma lem2424166 (m : nat) (n : nat) : (term1107 m n) = (term1108 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2424167 : term1099 = term1109.
Proof. exact (@lem2424166 (NUMERAL 0) term193). Qed.
Lemma lem2424168 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424169 (h1 : term606 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2424170 : (term606 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424169 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem2424168)). Qed.
Lemma lem2424171 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2424170) (@lem2424168)). Qed.
Lemma lem2424172 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2424173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2424174 : term1110 = (and True).
Proof. exact (MK_COMB (@lem2424173) (@lem2424172)). Qed.
Lemma lem2424175 : term1109 = (True /\ False).
Proof. exact (MK_COMB (@lem2424174) (@lem2424171)). Qed.
Lemma lem2424177 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2424178 : term1109 = False.
Proof. exact (TRANS (@lem2424175) (@lem2424177)). Qed.
Lemma lem2424179 : term1099 = False.
Proof. exact (TRANS (@lem2424167) (@lem2424178)). Qed.
Lemma lem2424180 : term1105 = False.
Proof. exact (TRANS (@lem2424164) (@lem2424179)). Qed.
Lemma lem2424181 : term1102 = False.
Proof. exact (TRANS (@lem2424148) (@lem2424180)). Qed.
Lemma lem2424182 : term1099 = False.
Proof. exact (TRANS (@lem2424125) (@lem2424181)). Qed.
Lemma lem2424183 : term579 = False.
Proof. exact (TRANS (@lem2424116) (@lem2424182)). Qed.
Lemma lem2424184 (y : int) (z : int) (h1 : term1164 y z) : False.
Proof. exact (EQ_MP (@lem2424183) (@lem2424113 y z h1)). Qed.
Lemma lem2424185 (y : int) (z : int) (h1 : term1084 y z) : False.
Proof. exact (or_elim (@lem2423340 y z h1) (fun h0 : term1163 y z => @lem2423738 y z h0) (fun h0 : term1164 y z => @lem2424184 y z h0)). Qed.
Lemma lem2424186 (y : int) (z : int) (h1 : term1087 y z) : False.
Proof. exact (or_elim (@lem2422493 y z h1) (fun h0 : term1085 y z => @lem2423339 y z h0) (fun h0 : term1084 y z => @lem2424185 y z h0)). Qed.
Lemma lem2424187 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1083 y y' z z') : term1083 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem2424188 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1081 y y' z z') : term1081 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem2424189 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : term1165 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem2424190 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : term768 y y' z z'.
Proof. exact (proj2 (@lem2424189 y y' z z' h1)). Qed.
Lemma lem2424191 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : (term713 y y' z z') = term182.
Proof. exact (proj1 (@lem2424189 y y' z z' h1)). Qed.
Lemma lem2424193 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2424194 : term1112 = term604.
Proof. exact (@lem2424193 term182 term192). Qed.
Lemma lem2424196 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2424197 : term192 = term567.
Proof. exact (@lem2424196 term193). Qed.
Lemma lem2424199 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2424200 : term182 = term543.
Proof. exact (@lem2424199 (NUMERAL 0)). Qed.
Lemma lem2424201 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2424202 : term1113 = term1114.
Proof. exact (MK_COMB (@lem2424201) (@lem2424200)). Qed.
Lemma lem2424203 : term604 = term1115.
Proof. exact (MK_COMB (@lem2424202) (@lem2424197)). Qed.
Lemma lem2424204 : term1116.
Proof. exact (@lem1980255 term182 term192 term192 term192). Qed.
Lemma lem2424206 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424207 : term604 = term605.
Proof. exact (@lem2424206 (NUMERAL 0) term193). Qed.
Lemma lem2424208 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424209 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424210 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424209 h1) (fun h1 : term605 = True => @lem2424208)). Qed.
Lemma lem2424211 : term605 = True.
Proof. exact (EQ_MP (@lem2424210) (@lem2424208)). Qed.
Lemma lem2424212 : term604 = True.
Proof. exact (TRANS (@lem2424207) (@lem2424211)). Qed.
Lemma lem2424213 : True = term604.
Proof. exact (SYM (@lem2424212)). Qed.
Lemma lem2424214 : term604.
Proof. exact (EQ_MP (@lem2424213) (@lem0)). Qed.
Lemma lem2424215 : term1117.
Proof. exact (@lem2424204 (@lem2424214)). Qed.
Lemma lem2424217 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424218 : term604 = term605.
Proof. exact (@lem2424217 (NUMERAL 0) term193). Qed.
Lemma lem2424219 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424220 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424221 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424220 h1) (fun h1 : term605 = True => @lem2424219)). Qed.
Lemma lem2424222 : term605 = True.
Proof. exact (EQ_MP (@lem2424221) (@lem2424219)). Qed.
Lemma lem2424223 : term604 = True.
Proof. exact (TRANS (@lem2424218) (@lem2424222)). Qed.
Lemma lem2424224 : True = term604.
Proof. exact (SYM (@lem2424223)). Qed.
Lemma lem2424225 : term604.
Proof. exact (EQ_MP (@lem2424224) (@lem0)). Qed.
Lemma lem2424226 : term1115 = term1118.
Proof. exact (@lem2424215 (@lem2424225)). Qed.
Lemma lem2424228 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424229 : term555 = term556.
Proof. exact (@lem2424228 term193 term193). Qed.
Lemma lem2424230 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424231 : term558 = term193.
Proof. exact (EQ_MP (@lem2424230) (@lem940073)). Qed.
Lemma lem2424232 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424233 : term556 = term192.
Proof. exact (MK_COMB (@lem2424232) (@lem2424231)). Qed.
Lemma lem2424234 : term555 = term192.
Proof. exact (TRANS (@lem2424229) (@lem2424233)). Qed.
Lemma lem2424236 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424237 : term615 = term182.
Proof. exact (@lem2424236 term193). Qed.
Lemma lem2424238 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2424239 : term1119 = term1113.
Proof. exact (MK_COMB (@lem2424238) (@lem2424237)). Qed.
Lemma lem2424240 : term1118 = term604.
Proof. exact (MK_COMB (@lem2424239) (@lem2424234)). Qed.
Lemma lem2424242 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424243 : term604 = term605.
Proof. exact (@lem2424242 (NUMERAL 0) term193). Qed.
Lemma lem2424244 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424245 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424246 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424245 h1) (fun h1 : term605 = True => @lem2424244)). Qed.
Lemma lem2424247 : term605 = True.
Proof. exact (EQ_MP (@lem2424246) (@lem2424244)). Qed.
Lemma lem2424248 : term604 = True.
Proof. exact (TRANS (@lem2424243) (@lem2424247)). Qed.
Lemma lem2424249 : term1118 = True.
Proof. exact (TRANS (@lem2424240) (@lem2424248)). Qed.
Lemma lem2424250 : term1115 = True.
Proof. exact (TRANS (@lem2424226) (@lem2424249)). Qed.
Lemma lem2424251 : term604 = True.
Proof. exact (TRANS (@lem2424203) (@lem2424250)). Qed.
Lemma lem2424252 : term1112 = True.
Proof. exact (TRANS (@lem2424194) (@lem2424251)). Qed.
Lemma lem2424253 : True = term1112.
Proof. exact (SYM (@lem2424252)). Qed.
Lemma lem2424254 : term1112.
Proof. exact (EQ_MP (@lem2424253) (@lem0)). Qed.
Lemma lem2424255 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : term1166 y y' z z'.
Proof. exact (conj (@lem2424254) (@lem2424190 y y' z z' h1)). Qed.
Lemma lem2424257 (x : real) (y : real) : term1121 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2424258 (y : int) (y' : int) (z : int) (z' : int) : term1167 y y' z z'.
Proof. exact (@lem2424257 term192 (term764 y y' z z')). Qed.
Lemma lem2424259 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : term1168 y y' z z'.
Proof. exact (@lem2424258 y y' z z' (@lem2424255 y y' z z' h1)). Qed.
Lemma lem2424260 (y : int) (y' : int) (z : int) (z' : int) : (term1169 y y' z z') = (term764 y y' z z').
Proof. exact (@lem1982733 (term764 y y' z z')). Qed.
Lemma lem2424261 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2424262 (y : int) (y' : int) (z : int) (z' : int) : (term1170 y y' z z') = (term767 y y' z z').
Proof. exact (MK_COMB (@lem2424261) (@lem2424260 y y' z z')). Qed.
Lemma lem2424263 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2424264 (y : int) (y' : int) (z : int) (z' : int) : (term1168 y y' z z') = (term768 y y' z z').
Proof. exact (MK_COMB (@lem2424262 y y' z z') (@lem2424263)). Qed.
Lemma lem2424265 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : term768 y y' z z'.
Proof. exact (EQ_MP (@lem2424264 y y' z z') (@lem2424259 y y' z z' h1)). Qed.
Lemma lem2424267 (y : real) : term1126 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2424268 (y : int) (y' : int) (z : int) (z' : int) : term1171 y y' z z'.
Proof. exact (@lem2424267 (term713 y y' z z')). Qed.
Lemma lem2424269 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : term1172 y y' z z'.
Proof. exact (@lem2424268 y y' z z' (@lem2424191 y y' z z' h1)). Qed.
Lemma lem2424270 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : term1173 y y' z z'.
Proof. exact (@lem2424269 y y' z z' h1 term192). Qed.
Lemma lem2424271 (y : int) (y' : int) (z : int) (z' : int) : (term1173 y y' z z') = ((term1174 y y' z z') = term182).
Proof. exact (eq_refl (term1173 y y' z z')). Qed.
Lemma lem2424272 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : (term1174 y y' z z') = term182.
Proof. exact (EQ_MP (@lem2424271 y y' z z') (@lem2424270 y y' z z' h1)). Qed.
Lemma lem2424273 (y : int) (y' : int) (z : int) (z' : int) : (term1174 y y' z z') = (term713 y y' z z').
Proof. exact (@lem1982733 (term713 y y' z z')). Qed.
Lemma lem2424274 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2424275 (y : int) (y' : int) (z : int) (z' : int) : (term1175 y y' z z') = (term721 y y' z z').
Proof. exact (MK_COMB (@lem2424274) (@lem2424273 y y' z z')). Qed.
Lemma lem2424276 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2424277 (y : int) (y' : int) (z : int) (z' : int) : ((term1174 y y' z z') = term182) = ((term713 y y' z z') = term182).
Proof. exact (MK_COMB (@lem2424275 y y' z z') (@lem2424276)). Qed.
Lemma lem2424278 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : (term713 y y' z z') = term182.
Proof. exact (EQ_MP (@lem2424277 y y' z z') (@lem2424272 y y' z z' h1)). Qed.
Lemma lem2424279 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : term1165 y y' z z'.
Proof. exact (conj (@lem2424278 y y' z z' h1) (@lem2424265 y y' z z' h1)). Qed.
Lemma lem2424281 (x : real) (y : real) : term1132 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2424282 (y : int) (y' : int) (z : int) (z' : int) : term1176 y y' z z'.
Proof. exact (@lem2424281 (term713 y y' z z') (term764 y y' z z')). Qed.
Lemma lem2424283 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : term1177 y y' z z'.
Proof. exact (@lem2424282 y y' z z' (@lem2424279 y y' z z' h1)). Qed.
Lemma lem2424284 (y : int) (y' : int) (z : int) (z' : int) : (term1178 y y' z z') = (term1179 y y' z z').
Proof. exact (@lem1982753 (term177 y y') (term708 y y') (term712 y y' z z') (term763 y y' z z')). Qed.
Lemma lem2424285 (y : int) (y' : int) : (term1180 y y') = (term1181 y y').
Proof. exact (@lem1982715 term546 (term177 y y')). Qed.
Lemma lem2424287 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2424288 : term192 = term567.
Proof. exact (@lem2424287 term193). Qed.
Lemma lem2424290 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2424291 : term546 = term547.
Proof. exact (@lem2424290 term193). Qed.
Lemma lem2424292 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424293 : term598 = term599.
Proof. exact (MK_COMB (@lem2424292) (@lem2424291)). Qed.
Lemma lem2424294 : term600 = term601.
Proof. exact (MK_COMB (@lem2424293) (@lem2424288)). Qed.
Lemma lem2424295 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2424297 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424298 : term604 = term605.
Proof. exact (@lem2424297 (NUMERAL 0) term193). Qed.
Lemma lem2424299 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424300 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424301 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424300 h1) (fun h1 : term605 = True => @lem2424299)). Qed.
Lemma lem2424302 : term605 = True.
Proof. exact (EQ_MP (@lem2424301) (@lem2424299)). Qed.
Lemma lem2424303 : term604 = True.
Proof. exact (TRANS (@lem2424298) (@lem2424302)). Qed.
Lemma lem2424304 : True = term604.
Proof. exact (SYM (@lem2424303)). Qed.
Lemma lem2424305 : term604.
Proof. exact (EQ_MP (@lem2424304) (@lem0)). Qed.
Lemma lem2424306 : term607.
Proof. exact (@lem2424295 (@lem2424305)). Qed.
Lemma lem2424308 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424309 : term604 = term605.
Proof. exact (@lem2424308 (NUMERAL 0) term193). Qed.
Lemma lem2424310 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424311 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424312 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424311 h1) (fun h1 : term605 = True => @lem2424310)). Qed.
Lemma lem2424313 : term605 = True.
Proof. exact (EQ_MP (@lem2424312) (@lem2424310)). Qed.
Lemma lem2424314 : term604 = True.
Proof. exact (TRANS (@lem2424309) (@lem2424313)). Qed.
Lemma lem2424315 : True = term604.
Proof. exact (SYM (@lem2424314)). Qed.
Lemma lem2424316 : term604.
Proof. exact (EQ_MP (@lem2424315) (@lem0)). Qed.
Lemma lem2424317 : term608.
Proof. exact (@lem2424306 (@lem2424316)). Qed.
Lemma lem2424319 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424320 : term604 = term605.
Proof. exact (@lem2424319 (NUMERAL 0) term193). Qed.
Lemma lem2424321 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424322 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424323 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424322 h1) (fun h1 : term605 = True => @lem2424321)). Qed.
Lemma lem2424324 : term605 = True.
Proof. exact (EQ_MP (@lem2424323) (@lem2424321)). Qed.
Lemma lem2424325 : term604 = True.
Proof. exact (TRANS (@lem2424320) (@lem2424324)). Qed.
Lemma lem2424326 : True = term604.
Proof. exact (SYM (@lem2424325)). Qed.
Lemma lem2424327 : term604.
Proof. exact (EQ_MP (@lem2424326) (@lem0)). Qed.
Lemma lem2424328 : term609.
Proof. exact (@lem2424317 (@lem2424327)). Qed.
Lemma lem2424330 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424331 : term555 = term556.
Proof. exact (@lem2424330 term193 term193). Qed.
Lemma lem2424332 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424333 : term558 = term193.
Proof. exact (EQ_MP (@lem2424332) (@lem940073)). Qed.
Lemma lem2424334 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424335 : term556 = term192.
Proof. exact (MK_COMB (@lem2424334) (@lem2424333)). Qed.
Lemma lem2424336 : term555 = term192.
Proof. exact (TRANS (@lem2424331) (@lem2424335)). Qed.
Lemma lem2424338 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2424339 : term568 = term573.
Proof. exact (@lem2424338 term193 term193). Qed.
Lemma lem2424340 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424341 : term558 = term193.
Proof. exact (EQ_MP (@lem2424340) (@lem940073)). Qed.
Lemma lem2424342 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424343 : term556 = term192.
Proof. exact (MK_COMB (@lem2424342) (@lem2424341)). Qed.
Lemma lem2424344 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2424345 : term573 = term546.
Proof. exact (MK_COMB (@lem2424344) (@lem2424343)). Qed.
Lemma lem2424346 : term568 = term546.
Proof. exact (TRANS (@lem2424339) (@lem2424345)). Qed.
Lemma lem2424347 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424348 : term610 = term598.
Proof. exact (MK_COMB (@lem2424347) (@lem2424346)). Qed.
Lemma lem2424349 : term611 = term600.
Proof. exact (MK_COMB (@lem2424348) (@lem2424336)). Qed.
Lemma lem2424351 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2424352 : term600 = term182.
Proof. exact (@lem2424351 term193). Qed.
Lemma lem2424353 : term611 = term182.
Proof. exact (TRANS (@lem2424349) (@lem2424352)). Qed.
Lemma lem2424354 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424355 : term613 = term184.
Proof. exact (MK_COMB (@lem2424354) (@lem2424353)). Qed.
Lemma lem2424356 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2424357 : term614 = term615.
Proof. exact (MK_COMB (@lem2424355) (@lem2424356)). Qed.
Lemma lem2424359 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424360 : term615 = term182.
Proof. exact (@lem2424359 term193). Qed.
Lemma lem2424361 : term614 = term182.
Proof. exact (TRANS (@lem2424357) (@lem2424360)). Qed.
Lemma lem2424363 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424364 : term555 = term556.
Proof. exact (@lem2424363 term193 term193). Qed.
Lemma lem2424365 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424366 : term558 = term193.
Proof. exact (EQ_MP (@lem2424365) (@lem940073)). Qed.
Lemma lem2424367 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424368 : term556 = term192.
Proof. exact (MK_COMB (@lem2424367) (@lem2424366)). Qed.
Lemma lem2424369 : term555 = term192.
Proof. exact (TRANS (@lem2424364) (@lem2424368)). Qed.
Lemma lem2424370 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2424371 : term617 = term615.
Proof. exact (MK_COMB (@lem2424370) (@lem2424369)). Qed.
Lemma lem2424373 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424374 : term615 = term182.
Proof. exact (@lem2424373 term193). Qed.
Lemma lem2424375 : term617 = term182.
Proof. exact (TRANS (@lem2424371) (@lem2424374)). Qed.
Lemma lem2424376 : term182 = term617.
Proof. exact (SYM (@lem2424375)). Qed.
Lemma lem2424377 : term614 = term617.
Proof. exact (TRANS (@lem2424361) (@lem2424376)). Qed.
Lemma lem2424378 : term601 = term543.
Proof. exact (@lem2424328 (@lem2424377)). Qed.
Lemma lem2424379 : term600 = term543.
Proof. exact (TRANS (@lem2424294) (@lem2424378)). Qed.
Lemma lem2424381 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2424382 : term543 = term182.
Proof. exact (@lem2424381 term182). Qed.
Lemma lem2424383 : term600 = term182.
Proof. exact (TRANS (@lem2424379) (@lem2424382)). Qed.
Lemma lem2424384 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424385 : term618 = term184.
Proof. exact (MK_COMB (@lem2424384) (@lem2424383)). Qed.
Lemma lem2424386 (y : int) (y' : int) : (term177 y y') = (term177 y y').
Proof. exact (eq_refl (term177 y y')). Qed.
Lemma lem2424387 (y : int) (y' : int) : (term1181 y y') = (term1182 y y').
Proof. exact (MK_COMB (@lem2424385) (@lem2424386 y y')). Qed.
Lemma lem2424388 (y : int) (y' : int) : (term1180 y y') = (term1182 y y').
Proof. exact (TRANS (@lem2424285 y y') (@lem2424387 y y')). Qed.
Lemma lem2424389 (y : int) (y' : int) : (term1182 y y') = term182.
Proof. exact (@lem1982719 (term177 y y')). Qed.
Lemma lem2424390 (y : int) (y' : int) : (term1180 y y') = term182.
Proof. exact (TRANS (@lem2424388 y y') (@lem2424389 y y')). Qed.
Lemma lem2424391 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424392 (y : int) (y' : int) : (term1183 y y') = term206.
Proof. exact (MK_COMB (@lem2424391) (@lem2424390 y y')). Qed.
Lemma lem2424393 (y : int) (y' : int) (z : int) (z' : int) : (term1184 y y' z z') = (term1185 y y' z z').
Proof. exact (@lem1982753 (term708 y z') (term177 y z') (term710 y' z z') (term762 y' z z')). Qed.
Lemma lem2424394 (y : int) (z' : int) : (term1186 y z') = (term1181 y z').
Proof. exact (@lem1982713 term546 (term177 y z')). Qed.
Lemma lem2424396 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2424397 : term192 = term567.
Proof. exact (@lem2424396 term193). Qed.
Lemma lem2424399 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2424400 : term546 = term547.
Proof. exact (@lem2424399 term193). Qed.
Lemma lem2424401 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424402 : term598 = term599.
Proof. exact (MK_COMB (@lem2424401) (@lem2424400)). Qed.
Lemma lem2424403 : term600 = term601.
Proof. exact (MK_COMB (@lem2424402) (@lem2424397)). Qed.
Lemma lem2424404 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2424406 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424407 : term604 = term605.
Proof. exact (@lem2424406 (NUMERAL 0) term193). Qed.
Lemma lem2424408 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424409 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424410 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424409 h1) (fun h1 : term605 = True => @lem2424408)). Qed.
Lemma lem2424411 : term605 = True.
Proof. exact (EQ_MP (@lem2424410) (@lem2424408)). Qed.
Lemma lem2424412 : term604 = True.
Proof. exact (TRANS (@lem2424407) (@lem2424411)). Qed.
Lemma lem2424413 : True = term604.
Proof. exact (SYM (@lem2424412)). Qed.
Lemma lem2424414 : term604.
Proof. exact (EQ_MP (@lem2424413) (@lem0)). Qed.
Lemma lem2424415 : term607.
Proof. exact (@lem2424404 (@lem2424414)). Qed.
Lemma lem2424417 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424418 : term604 = term605.
Proof. exact (@lem2424417 (NUMERAL 0) term193). Qed.
Lemma lem2424419 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424420 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424421 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424420 h1) (fun h1 : term605 = True => @lem2424419)). Qed.
Lemma lem2424422 : term605 = True.
Proof. exact (EQ_MP (@lem2424421) (@lem2424419)). Qed.
Lemma lem2424423 : term604 = True.
Proof. exact (TRANS (@lem2424418) (@lem2424422)). Qed.
Lemma lem2424424 : True = term604.
Proof. exact (SYM (@lem2424423)). Qed.
Lemma lem2424425 : term604.
Proof. exact (EQ_MP (@lem2424424) (@lem0)). Qed.
Lemma lem2424426 : term608.
Proof. exact (@lem2424415 (@lem2424425)). Qed.
Lemma lem2424428 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424429 : term604 = term605.
Proof. exact (@lem2424428 (NUMERAL 0) term193). Qed.
Lemma lem2424430 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424431 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424432 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424431 h1) (fun h1 : term605 = True => @lem2424430)). Qed.
Lemma lem2424433 : term605 = True.
Proof. exact (EQ_MP (@lem2424432) (@lem2424430)). Qed.
Lemma lem2424434 : term604 = True.
Proof. exact (TRANS (@lem2424429) (@lem2424433)). Qed.
Lemma lem2424435 : True = term604.
Proof. exact (SYM (@lem2424434)). Qed.
Lemma lem2424436 : term604.
Proof. exact (EQ_MP (@lem2424435) (@lem0)). Qed.
Lemma lem2424437 : term609.
Proof. exact (@lem2424426 (@lem2424436)). Qed.
Lemma lem2424439 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424440 : term555 = term556.
Proof. exact (@lem2424439 term193 term193). Qed.
Lemma lem2424441 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424442 : term558 = term193.
Proof. exact (EQ_MP (@lem2424441) (@lem940073)). Qed.
Lemma lem2424443 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424444 : term556 = term192.
Proof. exact (MK_COMB (@lem2424443) (@lem2424442)). Qed.
Lemma lem2424445 : term555 = term192.
Proof. exact (TRANS (@lem2424440) (@lem2424444)). Qed.
Lemma lem2424447 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2424448 : term568 = term573.
Proof. exact (@lem2424447 term193 term193). Qed.
Lemma lem2424449 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424450 : term558 = term193.
Proof. exact (EQ_MP (@lem2424449) (@lem940073)). Qed.
Lemma lem2424451 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424452 : term556 = term192.
Proof. exact (MK_COMB (@lem2424451) (@lem2424450)). Qed.
Lemma lem2424453 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2424454 : term573 = term546.
Proof. exact (MK_COMB (@lem2424453) (@lem2424452)). Qed.
Lemma lem2424455 : term568 = term546.
Proof. exact (TRANS (@lem2424448) (@lem2424454)). Qed.
Lemma lem2424456 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424457 : term610 = term598.
Proof. exact (MK_COMB (@lem2424456) (@lem2424455)). Qed.
Lemma lem2424458 : term611 = term600.
Proof. exact (MK_COMB (@lem2424457) (@lem2424445)). Qed.
Lemma lem2424460 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2424461 : term600 = term182.
Proof. exact (@lem2424460 term193). Qed.
Lemma lem2424462 : term611 = term182.
Proof. exact (TRANS (@lem2424458) (@lem2424461)). Qed.
Lemma lem2424463 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424464 : term613 = term184.
Proof. exact (MK_COMB (@lem2424463) (@lem2424462)). Qed.
Lemma lem2424465 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2424466 : term614 = term615.
Proof. exact (MK_COMB (@lem2424464) (@lem2424465)). Qed.
Lemma lem2424468 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424469 : term615 = term182.
Proof. exact (@lem2424468 term193). Qed.
Lemma lem2424470 : term614 = term182.
Proof. exact (TRANS (@lem2424466) (@lem2424469)). Qed.
Lemma lem2424472 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424473 : term555 = term556.
Proof. exact (@lem2424472 term193 term193). Qed.
Lemma lem2424474 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424475 : term558 = term193.
Proof. exact (EQ_MP (@lem2424474) (@lem940073)). Qed.
Lemma lem2424476 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424477 : term556 = term192.
Proof. exact (MK_COMB (@lem2424476) (@lem2424475)). Qed.
Lemma lem2424478 : term555 = term192.
Proof. exact (TRANS (@lem2424473) (@lem2424477)). Qed.
Lemma lem2424479 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2424480 : term617 = term615.
Proof. exact (MK_COMB (@lem2424479) (@lem2424478)). Qed.
Lemma lem2424482 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424483 : term615 = term182.
Proof. exact (@lem2424482 term193). Qed.
Lemma lem2424484 : term617 = term182.
Proof. exact (TRANS (@lem2424480) (@lem2424483)). Qed.
Lemma lem2424485 : term182 = term617.
Proof. exact (SYM (@lem2424484)). Qed.
Lemma lem2424486 : term614 = term617.
Proof. exact (TRANS (@lem2424470) (@lem2424485)). Qed.
Lemma lem2424487 : term601 = term543.
Proof. exact (@lem2424437 (@lem2424486)). Qed.
Lemma lem2424488 : term600 = term543.
Proof. exact (TRANS (@lem2424403) (@lem2424487)). Qed.
Lemma lem2424490 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2424491 : term543 = term182.
Proof. exact (@lem2424490 term182). Qed.
Lemma lem2424492 : term600 = term182.
Proof. exact (TRANS (@lem2424488) (@lem2424491)). Qed.
Lemma lem2424493 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424494 : term618 = term184.
Proof. exact (MK_COMB (@lem2424493) (@lem2424492)). Qed.
Lemma lem2424495 (y : int) (z' : int) : (term177 y z') = (term177 y z').
Proof. exact (eq_refl (term177 y z')). Qed.
Lemma lem2424496 (y : int) (z' : int) : (term1181 y z') = (term1182 y z').
Proof. exact (MK_COMB (@lem2424494) (@lem2424495 y z')). Qed.
Lemma lem2424497 (y : int) (z' : int) : (term1186 y z') = (term1182 y z').
Proof. exact (TRANS (@lem2424394 y z') (@lem2424496 y z')). Qed.
Lemma lem2424498 (y : int) (z' : int) : (term1182 y z') = term182.
Proof. exact (@lem1982719 (term177 y z')). Qed.
Lemma lem2424499 (y : int) (z' : int) : (term1186 y z') = term182.
Proof. exact (TRANS (@lem2424497 y z') (@lem2424498 y z')). Qed.
Lemma lem2424500 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424501 (y : int) (z' : int) : (term1187 y z') = term206.
Proof. exact (MK_COMB (@lem2424500) (@lem2424499 y z')). Qed.
Lemma lem2424502 (y' : int) (z : int) (z' : int) : (term1188 y' z z') = (term1189 y' z z').
Proof. exact (@lem1982753 (term708 z y') (term177 z y') (term177 z z') (term759 z z')). Qed.
Lemma lem2424503 (z : int) (y' : int) : (term1186 z y') = (term1181 z y').
Proof. exact (@lem1982713 term546 (term177 z y')). Qed.
Lemma lem2424505 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2424506 : term192 = term567.
Proof. exact (@lem2424505 term193). Qed.
Lemma lem2424508 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2424509 : term546 = term547.
Proof. exact (@lem2424508 term193). Qed.
Lemma lem2424510 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424511 : term598 = term599.
Proof. exact (MK_COMB (@lem2424510) (@lem2424509)). Qed.
Lemma lem2424512 : term600 = term601.
Proof. exact (MK_COMB (@lem2424511) (@lem2424506)). Qed.
Lemma lem2424513 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2424515 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424516 : term604 = term605.
Proof. exact (@lem2424515 (NUMERAL 0) term193). Qed.
Lemma lem2424517 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424518 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424519 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424518 h1) (fun h1 : term605 = True => @lem2424517)). Qed.
Lemma lem2424520 : term605 = True.
Proof. exact (EQ_MP (@lem2424519) (@lem2424517)). Qed.
Lemma lem2424521 : term604 = True.
Proof. exact (TRANS (@lem2424516) (@lem2424520)). Qed.
Lemma lem2424522 : True = term604.
Proof. exact (SYM (@lem2424521)). Qed.
Lemma lem2424523 : term604.
Proof. exact (EQ_MP (@lem2424522) (@lem0)). Qed.
Lemma lem2424524 : term607.
Proof. exact (@lem2424513 (@lem2424523)). Qed.
Lemma lem2424526 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424527 : term604 = term605.
Proof. exact (@lem2424526 (NUMERAL 0) term193). Qed.
Lemma lem2424528 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424529 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424530 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424529 h1) (fun h1 : term605 = True => @lem2424528)). Qed.
Lemma lem2424531 : term605 = True.
Proof. exact (EQ_MP (@lem2424530) (@lem2424528)). Qed.
Lemma lem2424532 : term604 = True.
Proof. exact (TRANS (@lem2424527) (@lem2424531)). Qed.
Lemma lem2424533 : True = term604.
Proof. exact (SYM (@lem2424532)). Qed.
Lemma lem2424534 : term604.
Proof. exact (EQ_MP (@lem2424533) (@lem0)). Qed.
Lemma lem2424535 : term608.
Proof. exact (@lem2424524 (@lem2424534)). Qed.
Lemma lem2424537 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424538 : term604 = term605.
Proof. exact (@lem2424537 (NUMERAL 0) term193). Qed.
Lemma lem2424539 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424540 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424541 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424540 h1) (fun h1 : term605 = True => @lem2424539)). Qed.
Lemma lem2424542 : term605 = True.
Proof. exact (EQ_MP (@lem2424541) (@lem2424539)). Qed.
Lemma lem2424543 : term604 = True.
Proof. exact (TRANS (@lem2424538) (@lem2424542)). Qed.
Lemma lem2424544 : True = term604.
Proof. exact (SYM (@lem2424543)). Qed.
Lemma lem2424545 : term604.
Proof. exact (EQ_MP (@lem2424544) (@lem0)). Qed.
Lemma lem2424546 : term609.
Proof. exact (@lem2424535 (@lem2424545)). Qed.
Lemma lem2424548 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424549 : term555 = term556.
Proof. exact (@lem2424548 term193 term193). Qed.
Lemma lem2424550 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424551 : term558 = term193.
Proof. exact (EQ_MP (@lem2424550) (@lem940073)). Qed.
Lemma lem2424552 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424553 : term556 = term192.
Proof. exact (MK_COMB (@lem2424552) (@lem2424551)). Qed.
Lemma lem2424554 : term555 = term192.
Proof. exact (TRANS (@lem2424549) (@lem2424553)). Qed.
Lemma lem2424556 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2424557 : term568 = term573.
Proof. exact (@lem2424556 term193 term193). Qed.
Lemma lem2424558 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424559 : term558 = term193.
Proof. exact (EQ_MP (@lem2424558) (@lem940073)). Qed.
Lemma lem2424560 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424561 : term556 = term192.
Proof. exact (MK_COMB (@lem2424560) (@lem2424559)). Qed.
Lemma lem2424562 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2424563 : term573 = term546.
Proof. exact (MK_COMB (@lem2424562) (@lem2424561)). Qed.
Lemma lem2424564 : term568 = term546.
Proof. exact (TRANS (@lem2424557) (@lem2424563)). Qed.
Lemma lem2424565 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424566 : term610 = term598.
Proof. exact (MK_COMB (@lem2424565) (@lem2424564)). Qed.
Lemma lem2424567 : term611 = term600.
Proof. exact (MK_COMB (@lem2424566) (@lem2424554)). Qed.
Lemma lem2424569 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2424570 : term600 = term182.
Proof. exact (@lem2424569 term193). Qed.
Lemma lem2424571 : term611 = term182.
Proof. exact (TRANS (@lem2424567) (@lem2424570)). Qed.
Lemma lem2424572 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424573 : term613 = term184.
Proof. exact (MK_COMB (@lem2424572) (@lem2424571)). Qed.
Lemma lem2424574 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2424575 : term614 = term615.
Proof. exact (MK_COMB (@lem2424573) (@lem2424574)). Qed.
Lemma lem2424577 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424578 : term615 = term182.
Proof. exact (@lem2424577 term193). Qed.
Lemma lem2424579 : term614 = term182.
Proof. exact (TRANS (@lem2424575) (@lem2424578)). Qed.
Lemma lem2424581 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424582 : term555 = term556.
Proof. exact (@lem2424581 term193 term193). Qed.
Lemma lem2424583 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424584 : term558 = term193.
Proof. exact (EQ_MP (@lem2424583) (@lem940073)). Qed.
Lemma lem2424585 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424586 : term556 = term192.
Proof. exact (MK_COMB (@lem2424585) (@lem2424584)). Qed.
Lemma lem2424587 : term555 = term192.
Proof. exact (TRANS (@lem2424582) (@lem2424586)). Qed.
Lemma lem2424588 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2424589 : term617 = term615.
Proof. exact (MK_COMB (@lem2424588) (@lem2424587)). Qed.
Lemma lem2424591 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424592 : term615 = term182.
Proof. exact (@lem2424591 term193). Qed.
Lemma lem2424593 : term617 = term182.
Proof. exact (TRANS (@lem2424589) (@lem2424592)). Qed.
Lemma lem2424594 : term182 = term617.
Proof. exact (SYM (@lem2424593)). Qed.
Lemma lem2424595 : term614 = term617.
Proof. exact (TRANS (@lem2424579) (@lem2424594)). Qed.
Lemma lem2424596 : term601 = term543.
Proof. exact (@lem2424546 (@lem2424595)). Qed.
Lemma lem2424597 : term600 = term543.
Proof. exact (TRANS (@lem2424512) (@lem2424596)). Qed.
Lemma lem2424599 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2424600 : term543 = term182.
Proof. exact (@lem2424599 term182). Qed.
Lemma lem2424601 : term600 = term182.
Proof. exact (TRANS (@lem2424597) (@lem2424600)). Qed.
Lemma lem2424602 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424603 : term618 = term184.
Proof. exact (MK_COMB (@lem2424602) (@lem2424601)). Qed.
Lemma lem2424604 (z : int) (y' : int) : (term177 z y') = (term177 z y').
Proof. exact (eq_refl (term177 z y')). Qed.
Lemma lem2424605 (z : int) (y' : int) : (term1181 z y') = (term1182 z y').
Proof. exact (MK_COMB (@lem2424603) (@lem2424604 z y')). Qed.
Lemma lem2424606 (z : int) (y' : int) : (term1186 z y') = (term1182 z y').
Proof. exact (TRANS (@lem2424503 z y') (@lem2424605 z y')). Qed.
Lemma lem2424607 (z : int) (y' : int) : (term1182 z y') = term182.
Proof. exact (@lem1982719 (term177 z y')). Qed.
Lemma lem2424608 (z : int) (y' : int) : (term1186 z y') = term182.
Proof. exact (TRANS (@lem2424606 z y') (@lem2424607 z y')). Qed.
Lemma lem2424609 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424610 (z : int) (y' : int) : (term1187 z y') = term206.
Proof. exact (MK_COMB (@lem2424609) (@lem2424608 z y')). Qed.
Lemma lem2424611 (z : int) (z' : int) : (term1190 z z') = (term1191 z z').
Proof. exact (@lem1982763 (term177 z z') (term708 z z') term546). Qed.
Lemma lem2424612 (z : int) (z' : int) : (term1180 z z') = (term1181 z z').
Proof. exact (@lem1982715 term546 (term177 z z')). Qed.
Lemma lem2424614 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2424615 : term192 = term567.
Proof. exact (@lem2424614 term193). Qed.
Lemma lem2424617 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2424618 : term546 = term547.
Proof. exact (@lem2424617 term193). Qed.
Lemma lem2424619 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424620 : term598 = term599.
Proof. exact (MK_COMB (@lem2424619) (@lem2424618)). Qed.
Lemma lem2424621 : term600 = term601.
Proof. exact (MK_COMB (@lem2424620) (@lem2424615)). Qed.
Lemma lem2424622 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2424624 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424625 : term604 = term605.
Proof. exact (@lem2424624 (NUMERAL 0) term193). Qed.
Lemma lem2424626 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424627 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424628 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424627 h1) (fun h1 : term605 = True => @lem2424626)). Qed.
Lemma lem2424629 : term605 = True.
Proof. exact (EQ_MP (@lem2424628) (@lem2424626)). Qed.
Lemma lem2424630 : term604 = True.
Proof. exact (TRANS (@lem2424625) (@lem2424629)). Qed.
Lemma lem2424631 : True = term604.
Proof. exact (SYM (@lem2424630)). Qed.
Lemma lem2424632 : term604.
Proof. exact (EQ_MP (@lem2424631) (@lem0)). Qed.
Lemma lem2424633 : term607.
Proof. exact (@lem2424622 (@lem2424632)). Qed.
Lemma lem2424635 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424636 : term604 = term605.
Proof. exact (@lem2424635 (NUMERAL 0) term193). Qed.
Lemma lem2424637 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424638 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424639 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424638 h1) (fun h1 : term605 = True => @lem2424637)). Qed.
Lemma lem2424640 : term605 = True.
Proof. exact (EQ_MP (@lem2424639) (@lem2424637)). Qed.
Lemma lem2424641 : term604 = True.
Proof. exact (TRANS (@lem2424636) (@lem2424640)). Qed.
Lemma lem2424642 : True = term604.
Proof. exact (SYM (@lem2424641)). Qed.
Lemma lem2424643 : term604.
Proof. exact (EQ_MP (@lem2424642) (@lem0)). Qed.
Lemma lem2424644 : term608.
Proof. exact (@lem2424633 (@lem2424643)). Qed.
Lemma lem2424646 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424647 : term604 = term605.
Proof. exact (@lem2424646 (NUMERAL 0) term193). Qed.
Lemma lem2424648 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424649 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424650 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424649 h1) (fun h1 : term605 = True => @lem2424648)). Qed.
Lemma lem2424651 : term605 = True.
Proof. exact (EQ_MP (@lem2424650) (@lem2424648)). Qed.
Lemma lem2424652 : term604 = True.
Proof. exact (TRANS (@lem2424647) (@lem2424651)). Qed.
Lemma lem2424653 : True = term604.
Proof. exact (SYM (@lem2424652)). Qed.
Lemma lem2424654 : term604.
Proof. exact (EQ_MP (@lem2424653) (@lem0)). Qed.
Lemma lem2424655 : term609.
Proof. exact (@lem2424644 (@lem2424654)). Qed.
Lemma lem2424657 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424658 : term555 = term556.
Proof. exact (@lem2424657 term193 term193). Qed.
Lemma lem2424659 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424660 : term558 = term193.
Proof. exact (EQ_MP (@lem2424659) (@lem940073)). Qed.
Lemma lem2424661 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424662 : term556 = term192.
Proof. exact (MK_COMB (@lem2424661) (@lem2424660)). Qed.
Lemma lem2424663 : term555 = term192.
Proof. exact (TRANS (@lem2424658) (@lem2424662)). Qed.
Lemma lem2424665 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2424666 : term568 = term573.
Proof. exact (@lem2424665 term193 term193). Qed.
Lemma lem2424667 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424668 : term558 = term193.
Proof. exact (EQ_MP (@lem2424667) (@lem940073)). Qed.
Lemma lem2424669 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424670 : term556 = term192.
Proof. exact (MK_COMB (@lem2424669) (@lem2424668)). Qed.
Lemma lem2424671 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2424672 : term573 = term546.
Proof. exact (MK_COMB (@lem2424671) (@lem2424670)). Qed.
Lemma lem2424673 : term568 = term546.
Proof. exact (TRANS (@lem2424666) (@lem2424672)). Qed.
Lemma lem2424674 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424675 : term610 = term598.
Proof. exact (MK_COMB (@lem2424674) (@lem2424673)). Qed.
Lemma lem2424676 : term611 = term600.
Proof. exact (MK_COMB (@lem2424675) (@lem2424663)). Qed.
Lemma lem2424678 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2424679 : term600 = term182.
Proof. exact (@lem2424678 term193). Qed.
Lemma lem2424680 : term611 = term182.
Proof. exact (TRANS (@lem2424676) (@lem2424679)). Qed.
Lemma lem2424681 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424682 : term613 = term184.
Proof. exact (MK_COMB (@lem2424681) (@lem2424680)). Qed.
Lemma lem2424683 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2424684 : term614 = term615.
Proof. exact (MK_COMB (@lem2424682) (@lem2424683)). Qed.
Lemma lem2424686 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424687 : term615 = term182.
Proof. exact (@lem2424686 term193). Qed.
Lemma lem2424688 : term614 = term182.
Proof. exact (TRANS (@lem2424684) (@lem2424687)). Qed.
Lemma lem2424690 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424691 : term555 = term556.
Proof. exact (@lem2424690 term193 term193). Qed.
Lemma lem2424692 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424693 : term558 = term193.
Proof. exact (EQ_MP (@lem2424692) (@lem940073)). Qed.
Lemma lem2424694 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424695 : term556 = term192.
Proof. exact (MK_COMB (@lem2424694) (@lem2424693)). Qed.
Lemma lem2424696 : term555 = term192.
Proof. exact (TRANS (@lem2424691) (@lem2424695)). Qed.
Lemma lem2424697 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2424698 : term617 = term615.
Proof. exact (MK_COMB (@lem2424697) (@lem2424696)). Qed.
Lemma lem2424700 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424701 : term615 = term182.
Proof. exact (@lem2424700 term193). Qed.
Lemma lem2424702 : term617 = term182.
Proof. exact (TRANS (@lem2424698) (@lem2424701)). Qed.
Lemma lem2424703 : term182 = term617.
Proof. exact (SYM (@lem2424702)). Qed.
Lemma lem2424704 : term614 = term617.
Proof. exact (TRANS (@lem2424688) (@lem2424703)). Qed.
Lemma lem2424705 : term601 = term543.
Proof. exact (@lem2424655 (@lem2424704)). Qed.
Lemma lem2424706 : term600 = term543.
Proof. exact (TRANS (@lem2424621) (@lem2424705)). Qed.
Lemma lem2424708 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2424709 : term543 = term182.
Proof. exact (@lem2424708 term182). Qed.
Lemma lem2424710 : term600 = term182.
Proof. exact (TRANS (@lem2424706) (@lem2424709)). Qed.
Lemma lem2424711 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424712 : term618 = term184.
Proof. exact (MK_COMB (@lem2424711) (@lem2424710)). Qed.
Lemma lem2424713 (z : int) (z' : int) : (term177 z z') = (term177 z z').
Proof. exact (eq_refl (term177 z z')). Qed.
Lemma lem2424714 (z : int) (z' : int) : (term1181 z z') = (term1182 z z').
Proof. exact (MK_COMB (@lem2424712) (@lem2424713 z z')). Qed.
Lemma lem2424715 (z : int) (z' : int) : (term1180 z z') = (term1182 z z').
Proof. exact (TRANS (@lem2424612 z z') (@lem2424714 z z')). Qed.
Lemma lem2424716 (z : int) (z' : int) : (term1182 z z') = term182.
Proof. exact (@lem1982719 (term177 z z')). Qed.
Lemma lem2424717 (z : int) (z' : int) : (term1180 z z') = term182.
Proof. exact (TRANS (@lem2424715 z z') (@lem2424716 z z')). Qed.
Lemma lem2424718 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424719 (z : int) (z' : int) : (term1183 z z') = term206.
Proof. exact (MK_COMB (@lem2424718) (@lem2424717 z z')). Qed.
Lemma lem2424720 : term546 = term546.
Proof. exact (eq_refl term546). Qed.
Lemma lem2424721 (z : int) (z' : int) : (term1191 z z') = term576.
Proof. exact (MK_COMB (@lem2424719 z z') (@lem2424720)). Qed.
Lemma lem2424722 (z : int) (z' : int) : (term1190 z z') = term576.
Proof. exact (TRANS (@lem2424611 z z') (@lem2424721 z z')). Qed.
Lemma lem2424723 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2424724 (z : int) (z' : int) : (term1190 z z') = term546.
Proof. exact (TRANS (@lem2424722 z z') (@lem2424723)). Qed.
Lemma lem2424725 (y' : int) (z : int) (z' : int) : (term1189 y' z z') = term576.
Proof. exact (MK_COMB (@lem2424610 z y') (@lem2424724 z z')). Qed.
Lemma lem2424726 (y' : int) (z : int) (z' : int) : (term1188 y' z z') = term576.
Proof. exact (TRANS (@lem2424502 y' z z') (@lem2424725 y' z z')). Qed.
Lemma lem2424727 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2424728 (y' : int) (z : int) (z' : int) : (term1188 y' z z') = term546.
Proof. exact (TRANS (@lem2424726 y' z z') (@lem2424727)). Qed.
Lemma lem2424729 (y : int) (y' : int) (z : int) (z' : int) : (term1185 y y' z z') = term576.
Proof. exact (MK_COMB (@lem2424501 y z') (@lem2424728 y' z z')). Qed.
Lemma lem2424730 (y : int) (y' : int) (z : int) (z' : int) : (term1184 y y' z z') = term576.
Proof. exact (TRANS (@lem2424393 y y' z z') (@lem2424729 y y' z z')). Qed.
Lemma lem2424731 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2424732 (y : int) (y' : int) (z : int) (z' : int) : (term1184 y y' z z') = term546.
Proof. exact (TRANS (@lem2424730 y y' z z') (@lem2424731)). Qed.
Lemma lem2424733 (y : int) (y' : int) (z : int) (z' : int) : (term1179 y y' z z') = term576.
Proof. exact (MK_COMB (@lem2424392 y y') (@lem2424732 y y' z z')). Qed.
Lemma lem2424734 (y : int) (y' : int) (z : int) (z' : int) : (term1178 y y' z z') = term576.
Proof. exact (TRANS (@lem2424284 y y' z z') (@lem2424733 y y' z z')). Qed.
Lemma lem2424735 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2424736 (y : int) (y' : int) (z : int) (z' : int) : (term1178 y y' z z') = term546.
Proof. exact (TRANS (@lem2424734 y y' z z') (@lem2424735)). Qed.
Lemma lem2424737 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2424738 (y : int) (y' : int) (z : int) (z' : int) : (term1192 y y' z z') = term578.
Proof. exact (MK_COMB (@lem2424737) (@lem2424736 y y' z z')). Qed.
Lemma lem2424739 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2424740 (y : int) (y' : int) (z : int) (z' : int) : (term1177 y y' z z') = term579.
Proof. exact (MK_COMB (@lem2424738 y y' z z') (@lem2424739)). Qed.
Lemma lem2424741 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : term579.
Proof. exact (EQ_MP (@lem2424740 y y' z z') (@lem2424283 y y' z z' h1)). Qed.
Lemma lem2424743 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2424744 : term579 = term1099.
Proof. exact (@lem2424743 term182 term546). Qed.
Lemma lem2424746 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2424747 : term546 = term547.
Proof. exact (@lem2424746 term193). Qed.
Lemma lem2424749 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2424750 : term182 = term543.
Proof. exact (@lem2424749 (NUMERAL 0)). Qed.
Lemma lem2424751 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2424752 : term1100 = term1101.
Proof. exact (MK_COMB (@lem2424751) (@lem2424750)). Qed.
Lemma lem2424753 : term1099 = term1102.
Proof. exact (MK_COMB (@lem2424752) (@lem2424747)). Qed.
Lemma lem2424754 : term1103.
Proof. exact (@lem1980026 term182 term192 term546 term192). Qed.
Lemma lem2424756 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424757 : term604 = term605.
Proof. exact (@lem2424756 (NUMERAL 0) term193). Qed.
Lemma lem2424758 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424759 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424760 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424759 h1) (fun h1 : term605 = True => @lem2424758)). Qed.
Lemma lem2424761 : term605 = True.
Proof. exact (EQ_MP (@lem2424760) (@lem2424758)). Qed.
Lemma lem2424762 : term604 = True.
Proof. exact (TRANS (@lem2424757) (@lem2424761)). Qed.
Lemma lem2424763 : True = term604.
Proof. exact (SYM (@lem2424762)). Qed.
Lemma lem2424764 : term604.
Proof. exact (EQ_MP (@lem2424763) (@lem0)). Qed.
Lemma lem2424765 : term1104.
Proof. exact (@lem2424754 (@lem2424764)). Qed.
Lemma lem2424767 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424768 : term604 = term605.
Proof. exact (@lem2424767 (NUMERAL 0) term193). Qed.
Lemma lem2424769 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424770 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424771 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424770 h1) (fun h1 : term605 = True => @lem2424769)). Qed.
Lemma lem2424772 : term605 = True.
Proof. exact (EQ_MP (@lem2424771) (@lem2424769)). Qed.
Lemma lem2424773 : term604 = True.
Proof. exact (TRANS (@lem2424768) (@lem2424772)). Qed.
Lemma lem2424774 : True = term604.
Proof. exact (SYM (@lem2424773)). Qed.
Lemma lem2424775 : term604.
Proof. exact (EQ_MP (@lem2424774) (@lem0)). Qed.
Lemma lem2424776 : term1102 = term1105.
Proof. exact (@lem2424765 (@lem2424775)). Qed.
Lemma lem2424778 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2424779 : term568 = term573.
Proof. exact (@lem2424778 term193 term193). Qed.
Lemma lem2424780 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424781 : term558 = term193.
Proof. exact (EQ_MP (@lem2424780) (@lem940073)). Qed.
Lemma lem2424782 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424783 : term556 = term192.
Proof. exact (MK_COMB (@lem2424782) (@lem2424781)). Qed.
Lemma lem2424784 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2424785 : term573 = term546.
Proof. exact (MK_COMB (@lem2424784) (@lem2424783)). Qed.
Lemma lem2424786 : term568 = term546.
Proof. exact (TRANS (@lem2424779) (@lem2424785)). Qed.
Lemma lem2424788 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424789 : term615 = term182.
Proof. exact (@lem2424788 term193). Qed.
Lemma lem2424790 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2424791 : term1106 = term1100.
Proof. exact (MK_COMB (@lem2424790) (@lem2424789)). Qed.
Lemma lem2424792 : term1105 = term1099.
Proof. exact (MK_COMB (@lem2424791) (@lem2424786)). Qed.
Lemma lem2424794 (m : nat) (n : nat) : (term1107 m n) = (term1108 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2424795 : term1099 = term1109.
Proof. exact (@lem2424794 (NUMERAL 0) term193). Qed.
Lemma lem2424796 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424797 (h1 : term606 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2424798 : (term606 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424797 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem2424796)). Qed.
Lemma lem2424799 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2424798) (@lem2424796)). Qed.
Lemma lem2424800 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2424801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2424802 : term1110 = (and True).
Proof. exact (MK_COMB (@lem2424801) (@lem2424800)). Qed.
Lemma lem2424803 : term1109 = (True /\ False).
Proof. exact (MK_COMB (@lem2424802) (@lem2424799)). Qed.
Lemma lem2424805 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2424806 : term1109 = False.
Proof. exact (TRANS (@lem2424803) (@lem2424805)). Qed.
Lemma lem2424807 : term1099 = False.
Proof. exact (TRANS (@lem2424795) (@lem2424806)). Qed.
Lemma lem2424808 : term1105 = False.
Proof. exact (TRANS (@lem2424792) (@lem2424807)). Qed.
Lemma lem2424809 : term1102 = False.
Proof. exact (TRANS (@lem2424776) (@lem2424808)). Qed.
Lemma lem2424810 : term1099 = False.
Proof. exact (TRANS (@lem2424753) (@lem2424809)). Qed.
Lemma lem2424811 : term579 = False.
Proof. exact (TRANS (@lem2424744) (@lem2424810)). Qed.
Lemma lem2424812 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1165 y y' z z') : False.
Proof. exact (EQ_MP (@lem2424811) (@lem2424741 y y' z z' h1)). Qed.
Lemma lem2424813 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : term1193 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem2424814 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : term784 y y' z z'.
Proof. exact (proj2 (@lem2424813 y y' z z' h1)). Qed.
Lemma lem2424815 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : (term713 y y' z z') = term182.
Proof. exact (proj1 (@lem2424813 y y' z z' h1)). Qed.
Lemma lem2424817 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2424818 : term1112 = term604.
Proof. exact (@lem2424817 term182 term192). Qed.
Lemma lem2424820 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2424821 : term192 = term567.
Proof. exact (@lem2424820 term193). Qed.
Lemma lem2424823 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2424824 : term182 = term543.
Proof. exact (@lem2424823 (NUMERAL 0)). Qed.
Lemma lem2424825 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2424826 : term1113 = term1114.
Proof. exact (MK_COMB (@lem2424825) (@lem2424824)). Qed.
Lemma lem2424827 : term604 = term1115.
Proof. exact (MK_COMB (@lem2424826) (@lem2424821)). Qed.
Lemma lem2424828 : term1116.
Proof. exact (@lem1980255 term182 term192 term192 term192). Qed.
Lemma lem2424830 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424831 : term604 = term605.
Proof. exact (@lem2424830 (NUMERAL 0) term193). Qed.
Lemma lem2424832 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424833 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424834 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424833 h1) (fun h1 : term605 = True => @lem2424832)). Qed.
Lemma lem2424835 : term605 = True.
Proof. exact (EQ_MP (@lem2424834) (@lem2424832)). Qed.
Lemma lem2424836 : term604 = True.
Proof. exact (TRANS (@lem2424831) (@lem2424835)). Qed.
Lemma lem2424837 : True = term604.
Proof. exact (SYM (@lem2424836)). Qed.
Lemma lem2424838 : term604.
Proof. exact (EQ_MP (@lem2424837) (@lem0)). Qed.
Lemma lem2424839 : term1117.
Proof. exact (@lem2424828 (@lem2424838)). Qed.
Lemma lem2424841 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424842 : term604 = term605.
Proof. exact (@lem2424841 (NUMERAL 0) term193). Qed.
Lemma lem2424843 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424844 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424845 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424844 h1) (fun h1 : term605 = True => @lem2424843)). Qed.
Lemma lem2424846 : term605 = True.
Proof. exact (EQ_MP (@lem2424845) (@lem2424843)). Qed.
Lemma lem2424847 : term604 = True.
Proof. exact (TRANS (@lem2424842) (@lem2424846)). Qed.
Lemma lem2424848 : True = term604.
Proof. exact (SYM (@lem2424847)). Qed.
Lemma lem2424849 : term604.
Proof. exact (EQ_MP (@lem2424848) (@lem0)). Qed.
Lemma lem2424850 : term1115 = term1118.
Proof. exact (@lem2424839 (@lem2424849)). Qed.
Lemma lem2424852 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424853 : term555 = term556.
Proof. exact (@lem2424852 term193 term193). Qed.
Lemma lem2424854 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424855 : term558 = term193.
Proof. exact (EQ_MP (@lem2424854) (@lem940073)). Qed.
Lemma lem2424856 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424857 : term556 = term192.
Proof. exact (MK_COMB (@lem2424856) (@lem2424855)). Qed.
Lemma lem2424858 : term555 = term192.
Proof. exact (TRANS (@lem2424853) (@lem2424857)). Qed.
Lemma lem2424860 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2424861 : term615 = term182.
Proof. exact (@lem2424860 term193). Qed.
Lemma lem2424862 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2424863 : term1119 = term1113.
Proof. exact (MK_COMB (@lem2424862) (@lem2424861)). Qed.
Lemma lem2424864 : term1118 = term604.
Proof. exact (MK_COMB (@lem2424863) (@lem2424858)). Qed.
Lemma lem2424866 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2424867 : term604 = term605.
Proof. exact (@lem2424866 (NUMERAL 0) term193). Qed.
Lemma lem2424868 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2424869 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2424870 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2424869 h1) (fun h1 : term605 = True => @lem2424868)). Qed.
Lemma lem2424871 : term605 = True.
Proof. exact (EQ_MP (@lem2424870) (@lem2424868)). Qed.
Lemma lem2424872 : term604 = True.
Proof. exact (TRANS (@lem2424867) (@lem2424871)). Qed.
Lemma lem2424873 : term1118 = True.
Proof. exact (TRANS (@lem2424864) (@lem2424872)). Qed.
Lemma lem2424874 : term1115 = True.
Proof. exact (TRANS (@lem2424850) (@lem2424873)). Qed.
Lemma lem2424875 : term604 = True.
Proof. exact (TRANS (@lem2424827) (@lem2424874)). Qed.
Lemma lem2424876 : term1112 = True.
Proof. exact (TRANS (@lem2424818) (@lem2424875)). Qed.
Lemma lem2424877 : True = term1112.
Proof. exact (SYM (@lem2424876)). Qed.
Lemma lem2424878 : term1112.
Proof. exact (EQ_MP (@lem2424877) (@lem0)). Qed.
Lemma lem2424879 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : term1194 y y' z z'.
Proof. exact (conj (@lem2424878) (@lem2424814 y y' z z' h1)). Qed.
Lemma lem2424881 (x : real) (y : real) : term1121 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2424882 (y : int) (y' : int) (z : int) (z' : int) : term1195 y y' z z'.
Proof. exact (@lem2424881 term192 (term781 y y' z z')). Qed.
Lemma lem2424883 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : term1196 y y' z z'.
Proof. exact (@lem2424882 y y' z z' (@lem2424879 y y' z z' h1)). Qed.
Lemma lem2424884 (y : int) (y' : int) (z : int) (z' : int) : (term1197 y y' z z') = (term781 y y' z z').
Proof. exact (@lem1982733 (term781 y y' z z')). Qed.
Lemma lem2424885 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2424886 (y : int) (y' : int) (z : int) (z' : int) : (term1198 y y' z z') = (term783 y y' z z').
Proof. exact (MK_COMB (@lem2424885) (@lem2424884 y y' z z')). Qed.
Lemma lem2424887 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2424888 (y : int) (y' : int) (z : int) (z' : int) : (term1196 y y' z z') = (term784 y y' z z').
Proof. exact (MK_COMB (@lem2424886 y y' z z') (@lem2424887)). Qed.
Lemma lem2424889 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : term784 y y' z z'.
Proof. exact (EQ_MP (@lem2424888 y y' z z') (@lem2424883 y y' z z' h1)). Qed.
Lemma lem2424891 (y : real) : term1126 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2424892 (y : int) (y' : int) (z : int) (z' : int) : term1171 y y' z z'.
Proof. exact (@lem2424891 (term713 y y' z z')). Qed.
Lemma lem2424893 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : term1172 y y' z z'.
Proof. exact (@lem2424892 y y' z z' (@lem2424815 y y' z z' h1)). Qed.
Lemma lem2424894 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : term1199 y y' z z'.
Proof. exact (@lem2424893 y y' z z' h1 term546). Qed.
Lemma lem2424895 (y : int) (y' : int) (z : int) (z' : int) : (term1199 y y' z z') = ((term1200 y y' z z') = term182).
Proof. exact (eq_refl (term1199 y y' z z')). Qed.
Lemma lem2424896 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : (term1200 y y' z z') = term182.
Proof. exact (EQ_MP (@lem2424895 y y' z z') (@lem2424894 y y' z z' h1)). Qed.
Lemma lem2424897 (y : int) (y' : int) (z : int) (z' : int) : (term1200 y y' z z') = (term1201 y y' z z').
Proof. exact (@lem1982781 (term177 y y') term546 (term712 y y' z z')). Qed.
Lemma lem2424898 (y : int) (y' : int) (z : int) (z' : int) : (term1202 y y' z z') = (term1203 y y' z z').
Proof. exact (@lem1982781 (term708 y z') term546 (term710 y' z z')). Qed.
Lemma lem2424899 (y' : int) (z : int) (z' : int) : (term1204 y' z z') = (term1205 y' z z').
Proof. exact (@lem1982781 (term708 z y') term546 (term177 z z')). Qed.
Lemma lem2424900 (z : int) (z' : int) : (term708 z z') = (term708 z z').
Proof. exact (eq_refl (term708 z z')). Qed.
Lemma lem2424901 (z : int) (y' : int) : (term760 z y') = (term734 z y').
Proof. exact (@lem1982749 term546 term546 (term177 z y')). Qed.
Lemma lem2424903 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2424904 : term546 = term547.
Proof. exact (@lem2424903 term193). Qed.
Lemma lem2424906 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2424907 : term546 = term547.
Proof. exact (@lem2424906 term193). Qed.
Lemma lem2424908 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424909 : term548 = term549.
Proof. exact (MK_COMB (@lem2424908) (@lem2424907)). Qed.
Lemma lem2424910 : term643 = term644.
Proof. exact (MK_COMB (@lem2424909) (@lem2424904)). Qed.
Lemma lem2424911 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2424913 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424914 : term555 = term556.
Proof. exact (@lem2424913 term193 term193). Qed.
Lemma lem2424915 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424916 : term558 = term193.
Proof. exact (EQ_MP (@lem2424915) (@lem940073)). Qed.
Lemma lem2424917 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424918 : term556 = term192.
Proof. exact (MK_COMB (@lem2424917) (@lem2424916)). Qed.
Lemma lem2424919 : term555 = term192.
Proof. exact (TRANS (@lem2424914) (@lem2424918)). Qed.
Lemma lem2424921 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2424922 : term643 = term556.
Proof. exact (@lem2424921 term193 term193). Qed.
Lemma lem2424923 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424924 : term558 = term193.
Proof. exact (EQ_MP (@lem2424923) (@lem940073)). Qed.
Lemma lem2424925 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424926 : term556 = term192.
Proof. exact (MK_COMB (@lem2424925) (@lem2424924)). Qed.
Lemma lem2424927 : term643 = term192.
Proof. exact (TRANS (@lem2424922) (@lem2424926)). Qed.
Lemma lem2424928 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2424929 : term647 = term648.
Proof. exact (MK_COMB (@lem2424928) (@lem2424927)). Qed.
Lemma lem2424930 : term645 = term567.
Proof. exact (MK_COMB (@lem2424929) (@lem2424919)). Qed.
Lemma lem2424931 : term644 = term567.
Proof. exact (TRANS (@lem2424911) (@lem2424930)). Qed.
Lemma lem2424932 : term643 = term567.
Proof. exact (TRANS (@lem2424910) (@lem2424931)). Qed.
Lemma lem2424934 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2424935 : term567 = term192.
Proof. exact (@lem2424934 term192). Qed.
Lemma lem2424936 : term643 = term192.
Proof. exact (TRANS (@lem2424932) (@lem2424935)). Qed.
Lemma lem2424937 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424938 : term649 = term650.
Proof. exact (MK_COMB (@lem2424937) (@lem2424936)). Qed.
Lemma lem2424939 (z : int) (y' : int) : (term177 z y') = (term177 z y').
Proof. exact (eq_refl (term177 z y')). Qed.
Lemma lem2424940 (z : int) (y' : int) : (term734 z y') = (term735 z y').
Proof. exact (MK_COMB (@lem2424938) (@lem2424939 z y')). Qed.
Lemma lem2424941 (z : int) (y' : int) : (term760 z y') = (term735 z y').
Proof. exact (TRANS (@lem2424901 z y') (@lem2424940 z y')). Qed.
Lemma lem2424942 (z : int) (y' : int) : (term735 z y') = (term177 z y').
Proof. exact (@lem1982709 (term177 z y')). Qed.
Lemma lem2424943 (z : int) (y' : int) : (term760 z y') = (term177 z y').
Proof. exact (TRANS (@lem2424941 z y') (@lem2424942 z y')). Qed.
Lemma lem2424944 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424945 (z : int) (y' : int) : (term761 z y') = (term283 z y').
Proof. exact (MK_COMB (@lem2424944) (@lem2424943 z y')). Qed.
Lemma lem2424946 (y' : int) (z : int) (z' : int) : (term1205 y' z z') = (term709 y' z z').
Proof. exact (MK_COMB (@lem2424945 z y') (@lem2424900 z z')). Qed.
Lemma lem2424947 (y' : int) (z : int) (z' : int) : (term1204 y' z z') = (term709 y' z z').
Proof. exact (TRANS (@lem2424899 y' z z') (@lem2424946 y' z z')). Qed.
Lemma lem2424948 (y : int) (z' : int) : (term760 y z') = (term734 y z').
Proof. exact (@lem1982749 term546 term546 (term177 y z')). Qed.
Lemma lem2424950 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2424951 : term546 = term547.
Proof. exact (@lem2424950 term193). Qed.
Lemma lem2424953 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2424954 : term546 = term547.
Proof. exact (@lem2424953 term193). Qed.
Lemma lem2424955 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424956 : term548 = term549.
Proof. exact (MK_COMB (@lem2424955) (@lem2424954)). Qed.
Lemma lem2424957 : term643 = term644.
Proof. exact (MK_COMB (@lem2424956) (@lem2424951)). Qed.
Lemma lem2424958 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2424960 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2424961 : term555 = term556.
Proof. exact (@lem2424960 term193 term193). Qed.
Lemma lem2424962 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424963 : term558 = term193.
Proof. exact (EQ_MP (@lem2424962) (@lem940073)). Qed.
Lemma lem2424964 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424965 : term556 = term192.
Proof. exact (MK_COMB (@lem2424964) (@lem2424963)). Qed.
Lemma lem2424966 : term555 = term192.
Proof. exact (TRANS (@lem2424961) (@lem2424965)). Qed.
Lemma lem2424968 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2424969 : term643 = term556.
Proof. exact (@lem2424968 term193 term193). Qed.
Lemma lem2424970 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2424971 : term558 = term193.
Proof. exact (EQ_MP (@lem2424970) (@lem940073)). Qed.
Lemma lem2424972 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2424973 : term556 = term192.
Proof. exact (MK_COMB (@lem2424972) (@lem2424971)). Qed.
Lemma lem2424974 : term643 = term192.
Proof. exact (TRANS (@lem2424969) (@lem2424973)). Qed.
Lemma lem2424975 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2424976 : term647 = term648.
Proof. exact (MK_COMB (@lem2424975) (@lem2424974)). Qed.
Lemma lem2424977 : term645 = term567.
Proof. exact (MK_COMB (@lem2424976) (@lem2424966)). Qed.
Lemma lem2424978 : term644 = term567.
Proof. exact (TRANS (@lem2424958) (@lem2424977)). Qed.
Lemma lem2424979 : term643 = term567.
Proof. exact (TRANS (@lem2424957) (@lem2424978)). Qed.
Lemma lem2424981 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2424982 : term567 = term192.
Proof. exact (@lem2424981 term192). Qed.
Lemma lem2424983 : term643 = term192.
Proof. exact (TRANS (@lem2424979) (@lem2424982)). Qed.
Lemma lem2424984 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2424985 : term649 = term650.
Proof. exact (MK_COMB (@lem2424984) (@lem2424983)). Qed.
Lemma lem2424986 (y : int) (z' : int) : (term177 y z') = (term177 y z').
Proof. exact (eq_refl (term177 y z')). Qed.
Lemma lem2424987 (y : int) (z' : int) : (term734 y z') = (term735 y z').
Proof. exact (MK_COMB (@lem2424985) (@lem2424986 y z')). Qed.
Lemma lem2424988 (y : int) (z' : int) : (term760 y z') = (term735 y z').
Proof. exact (TRANS (@lem2424948 y z') (@lem2424987 y z')). Qed.
Lemma lem2424989 (y : int) (z' : int) : (term735 y z') = (term177 y z').
Proof. exact (@lem1982709 (term177 y z')). Qed.
Lemma lem2424990 (y : int) (z' : int) : (term760 y z') = (term177 y z').
Proof. exact (TRANS (@lem2424988 y z') (@lem2424989 y z')). Qed.
Lemma lem2424991 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2424992 (y : int) (z' : int) : (term761 y z') = (term283 y z').
Proof. exact (MK_COMB (@lem2424991) (@lem2424990 y z')). Qed.
Lemma lem2424993 (y : int) (y' : int) (z : int) (z' : int) : (term1203 y y' z z') = (term1206 y y' z z').
Proof. exact (MK_COMB (@lem2424992 y z') (@lem2424947 y' z z')). Qed.
Lemma lem2424994 (y : int) (y' : int) (z : int) (z' : int) : (term1202 y y' z z') = (term1206 y y' z z').
Proof. exact (TRANS (@lem2424898 y y' z z') (@lem2424993 y y' z z')). Qed.
Lemma lem2424997 (y : int) (y' : int) : (term711 y y') = (term711 y y').
Proof. exact (eq_refl (term711 y y')). Qed.
Lemma lem2424998 (y : int) (y' : int) (z : int) (z' : int) : (term1201 y y' z z') = (term1207 y y' z z').
Proof. exact (MK_COMB (@lem2424997 y y') (@lem2424994 y y' z z')). Qed.
Lemma lem2424999 (y : int) (y' : int) (z : int) (z' : int) : (term1200 y y' z z') = (term1207 y y' z z').
Proof. exact (TRANS (@lem2424897 y y' z z') (@lem2424998 y y' z z')). Qed.
Lemma lem2425000 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2425001 (y : int) (y' : int) (z : int) (z' : int) : (term1208 y y' z z') = (term1209 y y' z z').
Proof. exact (MK_COMB (@lem2425000) (@lem2424999 y y' z z')). Qed.
Lemma lem2425002 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2425003 (y : int) (y' : int) (z : int) (z' : int) : ((term1200 y y' z z') = term182) = ((term1207 y y' z z') = term182).
Proof. exact (MK_COMB (@lem2425001 y y' z z') (@lem2425002)). Qed.
Lemma lem2425004 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : (term1207 y y' z z') = term182.
Proof. exact (EQ_MP (@lem2425003 y y' z z') (@lem2424896 y y' z z' h1)). Qed.
Lemma lem2425005 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : term1210 y y' z z'.
Proof. exact (conj (@lem2425004 y y' z z' h1) (@lem2424889 y y' z z' h1)). Qed.
Lemma lem2425007 (x : real) (y : real) : term1132 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2425008 (y : int) (y' : int) (z : int) (z' : int) : term1211 y y' z z'.
Proof. exact (@lem2425007 (term1207 y y' z z') (term781 y y' z z')). Qed.
Lemma lem2425009 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : term1212 y y' z z'.
Proof. exact (@lem2425008 y y' z z' (@lem2425005 y y' z z' h1)). Qed.
Lemma lem2425010 (y : int) (y' : int) (z : int) (z' : int) : (term1213 y y' z z') = (term1214 y y' z z').
Proof. exact (@lem1982753 (term708 y y') (term177 y y') (term1206 y y' z z') (term780 y y' z z')). Qed.
Lemma lem2425011 (y : int) (y' : int) : (term1186 y y') = (term1181 y y').
Proof. exact (@lem1982713 term546 (term177 y y')). Qed.
Lemma lem2425013 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2425014 : term192 = term567.
Proof. exact (@lem2425013 term193). Qed.
Lemma lem2425016 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2425017 : term546 = term547.
Proof. exact (@lem2425016 term193). Qed.
Lemma lem2425018 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425019 : term598 = term599.
Proof. exact (MK_COMB (@lem2425018) (@lem2425017)). Qed.
Lemma lem2425020 : term600 = term601.
Proof. exact (MK_COMB (@lem2425019) (@lem2425014)). Qed.
Lemma lem2425021 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2425023 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425024 : term604 = term605.
Proof. exact (@lem2425023 (NUMERAL 0) term193). Qed.
Lemma lem2425025 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425026 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425027 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425026 h1) (fun h1 : term605 = True => @lem2425025)). Qed.
Lemma lem2425028 : term605 = True.
Proof. exact (EQ_MP (@lem2425027) (@lem2425025)). Qed.
Lemma lem2425029 : term604 = True.
Proof. exact (TRANS (@lem2425024) (@lem2425028)). Qed.
Lemma lem2425030 : True = term604.
Proof. exact (SYM (@lem2425029)). Qed.
Lemma lem2425031 : term604.
Proof. exact (EQ_MP (@lem2425030) (@lem0)). Qed.
Lemma lem2425032 : term607.
Proof. exact (@lem2425021 (@lem2425031)). Qed.
Lemma lem2425034 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425035 : term604 = term605.
Proof. exact (@lem2425034 (NUMERAL 0) term193). Qed.
Lemma lem2425036 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425037 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425038 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425037 h1) (fun h1 : term605 = True => @lem2425036)). Qed.
Lemma lem2425039 : term605 = True.
Proof. exact (EQ_MP (@lem2425038) (@lem2425036)). Qed.
Lemma lem2425040 : term604 = True.
Proof. exact (TRANS (@lem2425035) (@lem2425039)). Qed.
Lemma lem2425041 : True = term604.
Proof. exact (SYM (@lem2425040)). Qed.
Lemma lem2425042 : term604.
Proof. exact (EQ_MP (@lem2425041) (@lem0)). Qed.
Lemma lem2425043 : term608.
Proof. exact (@lem2425032 (@lem2425042)). Qed.
Lemma lem2425045 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425046 : term604 = term605.
Proof. exact (@lem2425045 (NUMERAL 0) term193). Qed.
Lemma lem2425047 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425048 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425049 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425048 h1) (fun h1 : term605 = True => @lem2425047)). Qed.
Lemma lem2425050 : term605 = True.
Proof. exact (EQ_MP (@lem2425049) (@lem2425047)). Qed.
Lemma lem2425051 : term604 = True.
Proof. exact (TRANS (@lem2425046) (@lem2425050)). Qed.
Lemma lem2425052 : True = term604.
Proof. exact (SYM (@lem2425051)). Qed.
Lemma lem2425053 : term604.
Proof. exact (EQ_MP (@lem2425052) (@lem0)). Qed.
Lemma lem2425054 : term609.
Proof. exact (@lem2425043 (@lem2425053)). Qed.
Lemma lem2425056 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425057 : term555 = term556.
Proof. exact (@lem2425056 term193 term193). Qed.
Lemma lem2425058 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425059 : term558 = term193.
Proof. exact (EQ_MP (@lem2425058) (@lem940073)). Qed.
Lemma lem2425060 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425061 : term556 = term192.
Proof. exact (MK_COMB (@lem2425060) (@lem2425059)). Qed.
Lemma lem2425062 : term555 = term192.
Proof. exact (TRANS (@lem2425057) (@lem2425061)). Qed.
Lemma lem2425064 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2425065 : term568 = term573.
Proof. exact (@lem2425064 term193 term193). Qed.
Lemma lem2425066 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425067 : term558 = term193.
Proof. exact (EQ_MP (@lem2425066) (@lem940073)). Qed.
Lemma lem2425068 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425069 : term556 = term192.
Proof. exact (MK_COMB (@lem2425068) (@lem2425067)). Qed.
Lemma lem2425070 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2425071 : term573 = term546.
Proof. exact (MK_COMB (@lem2425070) (@lem2425069)). Qed.
Lemma lem2425072 : term568 = term546.
Proof. exact (TRANS (@lem2425065) (@lem2425071)). Qed.
Lemma lem2425073 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425074 : term610 = term598.
Proof. exact (MK_COMB (@lem2425073) (@lem2425072)). Qed.
Lemma lem2425075 : term611 = term600.
Proof. exact (MK_COMB (@lem2425074) (@lem2425062)). Qed.
Lemma lem2425077 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2425078 : term600 = term182.
Proof. exact (@lem2425077 term193). Qed.
Lemma lem2425079 : term611 = term182.
Proof. exact (TRANS (@lem2425075) (@lem2425078)). Qed.
Lemma lem2425080 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425081 : term613 = term184.
Proof. exact (MK_COMB (@lem2425080) (@lem2425079)). Qed.
Lemma lem2425082 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2425083 : term614 = term615.
Proof. exact (MK_COMB (@lem2425081) (@lem2425082)). Qed.
Lemma lem2425085 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425086 : term615 = term182.
Proof. exact (@lem2425085 term193). Qed.
Lemma lem2425087 : term614 = term182.
Proof. exact (TRANS (@lem2425083) (@lem2425086)). Qed.
Lemma lem2425089 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425090 : term555 = term556.
Proof. exact (@lem2425089 term193 term193). Qed.
Lemma lem2425091 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425092 : term558 = term193.
Proof. exact (EQ_MP (@lem2425091) (@lem940073)). Qed.
Lemma lem2425093 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425094 : term556 = term192.
Proof. exact (MK_COMB (@lem2425093) (@lem2425092)). Qed.
Lemma lem2425095 : term555 = term192.
Proof. exact (TRANS (@lem2425090) (@lem2425094)). Qed.
Lemma lem2425096 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2425097 : term617 = term615.
Proof. exact (MK_COMB (@lem2425096) (@lem2425095)). Qed.
Lemma lem2425099 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425100 : term615 = term182.
Proof. exact (@lem2425099 term193). Qed.
Lemma lem2425101 : term617 = term182.
Proof. exact (TRANS (@lem2425097) (@lem2425100)). Qed.
Lemma lem2425102 : term182 = term617.
Proof. exact (SYM (@lem2425101)). Qed.
Lemma lem2425103 : term614 = term617.
Proof. exact (TRANS (@lem2425087) (@lem2425102)). Qed.
Lemma lem2425104 : term601 = term543.
Proof. exact (@lem2425054 (@lem2425103)). Qed.
Lemma lem2425105 : term600 = term543.
Proof. exact (TRANS (@lem2425020) (@lem2425104)). Qed.
Lemma lem2425107 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2425108 : term543 = term182.
Proof. exact (@lem2425107 term182). Qed.
Lemma lem2425109 : term600 = term182.
Proof. exact (TRANS (@lem2425105) (@lem2425108)). Qed.
Lemma lem2425110 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425111 : term618 = term184.
Proof. exact (MK_COMB (@lem2425110) (@lem2425109)). Qed.
Lemma lem2425112 (y : int) (y' : int) : (term177 y y') = (term177 y y').
Proof. exact (eq_refl (term177 y y')). Qed.
Lemma lem2425113 (y : int) (y' : int) : (term1181 y y') = (term1182 y y').
Proof. exact (MK_COMB (@lem2425111) (@lem2425112 y y')). Qed.
Lemma lem2425114 (y : int) (y' : int) : (term1186 y y') = (term1182 y y').
Proof. exact (TRANS (@lem2425011 y y') (@lem2425113 y y')). Qed.
Lemma lem2425115 (y : int) (y' : int) : (term1182 y y') = term182.
Proof. exact (@lem1982719 (term177 y y')). Qed.
Lemma lem2425116 (y : int) (y' : int) : (term1186 y y') = term182.
Proof. exact (TRANS (@lem2425114 y y') (@lem2425115 y y')). Qed.
Lemma lem2425117 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425118 (y : int) (y' : int) : (term1187 y y') = term206.
Proof. exact (MK_COMB (@lem2425117) (@lem2425116 y y')). Qed.
Lemma lem2425119 (y : int) (y' : int) (z : int) (z' : int) : (term1215 y y' z z') = (term1216 y y' z z').
Proof. exact (@lem1982753 (term177 y z') (term708 y z') (term709 y' z z') (term779 y' z z')). Qed.
Lemma lem2425120 (y : int) (z' : int) : (term1180 y z') = (term1181 y z').
Proof. exact (@lem1982715 term546 (term177 y z')). Qed.
Lemma lem2425122 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2425123 : term192 = term567.
Proof. exact (@lem2425122 term193). Qed.
Lemma lem2425125 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2425126 : term546 = term547.
Proof. exact (@lem2425125 term193). Qed.
Lemma lem2425127 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425128 : term598 = term599.
Proof. exact (MK_COMB (@lem2425127) (@lem2425126)). Qed.
Lemma lem2425129 : term600 = term601.
Proof. exact (MK_COMB (@lem2425128) (@lem2425123)). Qed.
Lemma lem2425130 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2425132 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425133 : term604 = term605.
Proof. exact (@lem2425132 (NUMERAL 0) term193). Qed.
Lemma lem2425134 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425135 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425136 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425135 h1) (fun h1 : term605 = True => @lem2425134)). Qed.
Lemma lem2425137 : term605 = True.
Proof. exact (EQ_MP (@lem2425136) (@lem2425134)). Qed.
Lemma lem2425138 : term604 = True.
Proof. exact (TRANS (@lem2425133) (@lem2425137)). Qed.
Lemma lem2425139 : True = term604.
Proof. exact (SYM (@lem2425138)). Qed.
Lemma lem2425140 : term604.
Proof. exact (EQ_MP (@lem2425139) (@lem0)). Qed.
Lemma lem2425141 : term607.
Proof. exact (@lem2425130 (@lem2425140)). Qed.
Lemma lem2425143 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425144 : term604 = term605.
Proof. exact (@lem2425143 (NUMERAL 0) term193). Qed.
Lemma lem2425145 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425146 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425147 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425146 h1) (fun h1 : term605 = True => @lem2425145)). Qed.
Lemma lem2425148 : term605 = True.
Proof. exact (EQ_MP (@lem2425147) (@lem2425145)). Qed.
Lemma lem2425149 : term604 = True.
Proof. exact (TRANS (@lem2425144) (@lem2425148)). Qed.
Lemma lem2425150 : True = term604.
Proof. exact (SYM (@lem2425149)). Qed.
Lemma lem2425151 : term604.
Proof. exact (EQ_MP (@lem2425150) (@lem0)). Qed.
Lemma lem2425152 : term608.
Proof. exact (@lem2425141 (@lem2425151)). Qed.
Lemma lem2425154 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425155 : term604 = term605.
Proof. exact (@lem2425154 (NUMERAL 0) term193). Qed.
Lemma lem2425156 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425157 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425158 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425157 h1) (fun h1 : term605 = True => @lem2425156)). Qed.
Lemma lem2425159 : term605 = True.
Proof. exact (EQ_MP (@lem2425158) (@lem2425156)). Qed.
Lemma lem2425160 : term604 = True.
Proof. exact (TRANS (@lem2425155) (@lem2425159)). Qed.
Lemma lem2425161 : True = term604.
Proof. exact (SYM (@lem2425160)). Qed.
Lemma lem2425162 : term604.
Proof. exact (EQ_MP (@lem2425161) (@lem0)). Qed.
Lemma lem2425163 : term609.
Proof. exact (@lem2425152 (@lem2425162)). Qed.
Lemma lem2425165 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425166 : term555 = term556.
Proof. exact (@lem2425165 term193 term193). Qed.
Lemma lem2425167 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425168 : term558 = term193.
Proof. exact (EQ_MP (@lem2425167) (@lem940073)). Qed.
Lemma lem2425169 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425170 : term556 = term192.
Proof. exact (MK_COMB (@lem2425169) (@lem2425168)). Qed.
Lemma lem2425171 : term555 = term192.
Proof. exact (TRANS (@lem2425166) (@lem2425170)). Qed.
Lemma lem2425173 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2425174 : term568 = term573.
Proof. exact (@lem2425173 term193 term193). Qed.
Lemma lem2425175 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425176 : term558 = term193.
Proof. exact (EQ_MP (@lem2425175) (@lem940073)). Qed.
Lemma lem2425177 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425178 : term556 = term192.
Proof. exact (MK_COMB (@lem2425177) (@lem2425176)). Qed.
Lemma lem2425179 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2425180 : term573 = term546.
Proof. exact (MK_COMB (@lem2425179) (@lem2425178)). Qed.
Lemma lem2425181 : term568 = term546.
Proof. exact (TRANS (@lem2425174) (@lem2425180)). Qed.
Lemma lem2425182 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425183 : term610 = term598.
Proof. exact (MK_COMB (@lem2425182) (@lem2425181)). Qed.
Lemma lem2425184 : term611 = term600.
Proof. exact (MK_COMB (@lem2425183) (@lem2425171)). Qed.
Lemma lem2425186 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2425187 : term600 = term182.
Proof. exact (@lem2425186 term193). Qed.
Lemma lem2425188 : term611 = term182.
Proof. exact (TRANS (@lem2425184) (@lem2425187)). Qed.
Lemma lem2425189 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425190 : term613 = term184.
Proof. exact (MK_COMB (@lem2425189) (@lem2425188)). Qed.
Lemma lem2425191 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2425192 : term614 = term615.
Proof. exact (MK_COMB (@lem2425190) (@lem2425191)). Qed.
Lemma lem2425194 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425195 : term615 = term182.
Proof. exact (@lem2425194 term193). Qed.
Lemma lem2425196 : term614 = term182.
Proof. exact (TRANS (@lem2425192) (@lem2425195)). Qed.
Lemma lem2425198 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425199 : term555 = term556.
Proof. exact (@lem2425198 term193 term193). Qed.
Lemma lem2425200 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425201 : term558 = term193.
Proof. exact (EQ_MP (@lem2425200) (@lem940073)). Qed.
Lemma lem2425202 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425203 : term556 = term192.
Proof. exact (MK_COMB (@lem2425202) (@lem2425201)). Qed.
Lemma lem2425204 : term555 = term192.
Proof. exact (TRANS (@lem2425199) (@lem2425203)). Qed.
Lemma lem2425205 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2425206 : term617 = term615.
Proof. exact (MK_COMB (@lem2425205) (@lem2425204)). Qed.
Lemma lem2425208 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425209 : term615 = term182.
Proof. exact (@lem2425208 term193). Qed.
Lemma lem2425210 : term617 = term182.
Proof. exact (TRANS (@lem2425206) (@lem2425209)). Qed.
Lemma lem2425211 : term182 = term617.
Proof. exact (SYM (@lem2425210)). Qed.
Lemma lem2425212 : term614 = term617.
Proof. exact (TRANS (@lem2425196) (@lem2425211)). Qed.
Lemma lem2425213 : term601 = term543.
Proof. exact (@lem2425163 (@lem2425212)). Qed.
Lemma lem2425214 : term600 = term543.
Proof. exact (TRANS (@lem2425129) (@lem2425213)). Qed.
Lemma lem2425216 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2425217 : term543 = term182.
Proof. exact (@lem2425216 term182). Qed.
Lemma lem2425218 : term600 = term182.
Proof. exact (TRANS (@lem2425214) (@lem2425217)). Qed.
Lemma lem2425219 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425220 : term618 = term184.
Proof. exact (MK_COMB (@lem2425219) (@lem2425218)). Qed.
Lemma lem2425221 (y : int) (z' : int) : (term177 y z') = (term177 y z').
Proof. exact (eq_refl (term177 y z')). Qed.
Lemma lem2425222 (y : int) (z' : int) : (term1181 y z') = (term1182 y z').
Proof. exact (MK_COMB (@lem2425220) (@lem2425221 y z')). Qed.
Lemma lem2425223 (y : int) (z' : int) : (term1180 y z') = (term1182 y z').
Proof. exact (TRANS (@lem2425120 y z') (@lem2425222 y z')). Qed.
Lemma lem2425224 (y : int) (z' : int) : (term1182 y z') = term182.
Proof. exact (@lem1982719 (term177 y z')). Qed.
Lemma lem2425225 (y : int) (z' : int) : (term1180 y z') = term182.
Proof. exact (TRANS (@lem2425223 y z') (@lem2425224 y z')). Qed.
Lemma lem2425226 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425227 (y : int) (z' : int) : (term1183 y z') = term206.
Proof. exact (MK_COMB (@lem2425226) (@lem2425225 y z')). Qed.
Lemma lem2425228 (y' : int) (z : int) (z' : int) : (term1217 y' z z') = (term1218 y' z z').
Proof. exact (@lem1982753 (term177 z y') (term708 z y') (term708 z z') (term1219 z z')). Qed.
Lemma lem2425229 (z : int) (y' : int) : (term1180 z y') = (term1181 z y').
Proof. exact (@lem1982715 term546 (term177 z y')). Qed.
Lemma lem2425231 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2425232 : term192 = term567.
Proof. exact (@lem2425231 term193). Qed.
Lemma lem2425234 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2425235 : term546 = term547.
Proof. exact (@lem2425234 term193). Qed.
Lemma lem2425236 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425237 : term598 = term599.
Proof. exact (MK_COMB (@lem2425236) (@lem2425235)). Qed.
Lemma lem2425238 : term600 = term601.
Proof. exact (MK_COMB (@lem2425237) (@lem2425232)). Qed.
Lemma lem2425239 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2425241 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425242 : term604 = term605.
Proof. exact (@lem2425241 (NUMERAL 0) term193). Qed.
Lemma lem2425243 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425244 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425245 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425244 h1) (fun h1 : term605 = True => @lem2425243)). Qed.
Lemma lem2425246 : term605 = True.
Proof. exact (EQ_MP (@lem2425245) (@lem2425243)). Qed.
Lemma lem2425247 : term604 = True.
Proof. exact (TRANS (@lem2425242) (@lem2425246)). Qed.
Lemma lem2425248 : True = term604.
Proof. exact (SYM (@lem2425247)). Qed.
Lemma lem2425249 : term604.
Proof. exact (EQ_MP (@lem2425248) (@lem0)). Qed.
Lemma lem2425250 : term607.
Proof. exact (@lem2425239 (@lem2425249)). Qed.
Lemma lem2425252 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425253 : term604 = term605.
Proof. exact (@lem2425252 (NUMERAL 0) term193). Qed.
Lemma lem2425254 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425255 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425256 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425255 h1) (fun h1 : term605 = True => @lem2425254)). Qed.
Lemma lem2425257 : term605 = True.
Proof. exact (EQ_MP (@lem2425256) (@lem2425254)). Qed.
Lemma lem2425258 : term604 = True.
Proof. exact (TRANS (@lem2425253) (@lem2425257)). Qed.
Lemma lem2425259 : True = term604.
Proof. exact (SYM (@lem2425258)). Qed.
Lemma lem2425260 : term604.
Proof. exact (EQ_MP (@lem2425259) (@lem0)). Qed.
Lemma lem2425261 : term608.
Proof. exact (@lem2425250 (@lem2425260)). Qed.
Lemma lem2425263 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425264 : term604 = term605.
Proof. exact (@lem2425263 (NUMERAL 0) term193). Qed.
Lemma lem2425265 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425266 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425267 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425266 h1) (fun h1 : term605 = True => @lem2425265)). Qed.
Lemma lem2425268 : term605 = True.
Proof. exact (EQ_MP (@lem2425267) (@lem2425265)). Qed.
Lemma lem2425269 : term604 = True.
Proof. exact (TRANS (@lem2425264) (@lem2425268)). Qed.
Lemma lem2425270 : True = term604.
Proof. exact (SYM (@lem2425269)). Qed.
Lemma lem2425271 : term604.
Proof. exact (EQ_MP (@lem2425270) (@lem0)). Qed.
Lemma lem2425272 : term609.
Proof. exact (@lem2425261 (@lem2425271)). Qed.
Lemma lem2425274 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425275 : term555 = term556.
Proof. exact (@lem2425274 term193 term193). Qed.
Lemma lem2425276 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425277 : term558 = term193.
Proof. exact (EQ_MP (@lem2425276) (@lem940073)). Qed.
Lemma lem2425278 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425279 : term556 = term192.
Proof. exact (MK_COMB (@lem2425278) (@lem2425277)). Qed.
Lemma lem2425280 : term555 = term192.
Proof. exact (TRANS (@lem2425275) (@lem2425279)). Qed.
Lemma lem2425282 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2425283 : term568 = term573.
Proof. exact (@lem2425282 term193 term193). Qed.
Lemma lem2425284 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425285 : term558 = term193.
Proof. exact (EQ_MP (@lem2425284) (@lem940073)). Qed.
Lemma lem2425286 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425287 : term556 = term192.
Proof. exact (MK_COMB (@lem2425286) (@lem2425285)). Qed.
Lemma lem2425288 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2425289 : term573 = term546.
Proof. exact (MK_COMB (@lem2425288) (@lem2425287)). Qed.
Lemma lem2425290 : term568 = term546.
Proof. exact (TRANS (@lem2425283) (@lem2425289)). Qed.
Lemma lem2425291 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425292 : term610 = term598.
Proof. exact (MK_COMB (@lem2425291) (@lem2425290)). Qed.
Lemma lem2425293 : term611 = term600.
Proof. exact (MK_COMB (@lem2425292) (@lem2425280)). Qed.
Lemma lem2425295 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2425296 : term600 = term182.
Proof. exact (@lem2425295 term193). Qed.
Lemma lem2425297 : term611 = term182.
Proof. exact (TRANS (@lem2425293) (@lem2425296)). Qed.
Lemma lem2425298 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425299 : term613 = term184.
Proof. exact (MK_COMB (@lem2425298) (@lem2425297)). Qed.
Lemma lem2425300 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2425301 : term614 = term615.
Proof. exact (MK_COMB (@lem2425299) (@lem2425300)). Qed.
Lemma lem2425303 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425304 : term615 = term182.
Proof. exact (@lem2425303 term193). Qed.
Lemma lem2425305 : term614 = term182.
Proof. exact (TRANS (@lem2425301) (@lem2425304)). Qed.
Lemma lem2425307 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425308 : term555 = term556.
Proof. exact (@lem2425307 term193 term193). Qed.
Lemma lem2425309 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425310 : term558 = term193.
Proof. exact (EQ_MP (@lem2425309) (@lem940073)). Qed.
Lemma lem2425311 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425312 : term556 = term192.
Proof. exact (MK_COMB (@lem2425311) (@lem2425310)). Qed.
Lemma lem2425313 : term555 = term192.
Proof. exact (TRANS (@lem2425308) (@lem2425312)). Qed.
Lemma lem2425314 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2425315 : term617 = term615.
Proof. exact (MK_COMB (@lem2425314) (@lem2425313)). Qed.
Lemma lem2425317 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425318 : term615 = term182.
Proof. exact (@lem2425317 term193). Qed.
Lemma lem2425319 : term617 = term182.
Proof. exact (TRANS (@lem2425315) (@lem2425318)). Qed.
Lemma lem2425320 : term182 = term617.
Proof. exact (SYM (@lem2425319)). Qed.
Lemma lem2425321 : term614 = term617.
Proof. exact (TRANS (@lem2425305) (@lem2425320)). Qed.
Lemma lem2425322 : term601 = term543.
Proof. exact (@lem2425272 (@lem2425321)). Qed.
Lemma lem2425323 : term600 = term543.
Proof. exact (TRANS (@lem2425238) (@lem2425322)). Qed.
Lemma lem2425325 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2425326 : term543 = term182.
Proof. exact (@lem2425325 term182). Qed.
Lemma lem2425327 : term600 = term182.
Proof. exact (TRANS (@lem2425323) (@lem2425326)). Qed.
Lemma lem2425328 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425329 : term618 = term184.
Proof. exact (MK_COMB (@lem2425328) (@lem2425327)). Qed.
Lemma lem2425330 (z : int) (y' : int) : (term177 z y') = (term177 z y').
Proof. exact (eq_refl (term177 z y')). Qed.
Lemma lem2425331 (z : int) (y' : int) : (term1181 z y') = (term1182 z y').
Proof. exact (MK_COMB (@lem2425329) (@lem2425330 z y')). Qed.
Lemma lem2425332 (z : int) (y' : int) : (term1180 z y') = (term1182 z y').
Proof. exact (TRANS (@lem2425229 z y') (@lem2425331 z y')). Qed.
Lemma lem2425333 (z : int) (y' : int) : (term1182 z y') = term182.
Proof. exact (@lem1982719 (term177 z y')). Qed.
Lemma lem2425334 (z : int) (y' : int) : (term1180 z y') = term182.
Proof. exact (TRANS (@lem2425332 z y') (@lem2425333 z y')). Qed.
Lemma lem2425335 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425336 (z : int) (y' : int) : (term1183 z y') = term206.
Proof. exact (MK_COMB (@lem2425335) (@lem2425334 z y')). Qed.
Lemma lem2425337 (z : int) (z' : int) : (term1220 z z') = (term1221 z z').
Proof. exact (@lem1982763 (term708 z z') (term177 z z') term546). Qed.
Lemma lem2425338 (z : int) (z' : int) : (term1186 z z') = (term1181 z z').
Proof. exact (@lem1982713 term546 (term177 z z')). Qed.
Lemma lem2425340 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2425341 : term192 = term567.
Proof. exact (@lem2425340 term193). Qed.
Lemma lem2425343 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2425344 : term546 = term547.
Proof. exact (@lem2425343 term193). Qed.
Lemma lem2425345 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425346 : term598 = term599.
Proof. exact (MK_COMB (@lem2425345) (@lem2425344)). Qed.
Lemma lem2425347 : term600 = term601.
Proof. exact (MK_COMB (@lem2425346) (@lem2425341)). Qed.
Lemma lem2425348 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2425350 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425351 : term604 = term605.
Proof. exact (@lem2425350 (NUMERAL 0) term193). Qed.
Lemma lem2425352 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425353 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425354 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425353 h1) (fun h1 : term605 = True => @lem2425352)). Qed.
Lemma lem2425355 : term605 = True.
Proof. exact (EQ_MP (@lem2425354) (@lem2425352)). Qed.
Lemma lem2425356 : term604 = True.
Proof. exact (TRANS (@lem2425351) (@lem2425355)). Qed.
Lemma lem2425357 : True = term604.
Proof. exact (SYM (@lem2425356)). Qed.
Lemma lem2425358 : term604.
Proof. exact (EQ_MP (@lem2425357) (@lem0)). Qed.
Lemma lem2425359 : term607.
Proof. exact (@lem2425348 (@lem2425358)). Qed.
Lemma lem2425361 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425362 : term604 = term605.
Proof. exact (@lem2425361 (NUMERAL 0) term193). Qed.
Lemma lem2425363 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425364 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425365 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425364 h1) (fun h1 : term605 = True => @lem2425363)). Qed.
Lemma lem2425366 : term605 = True.
Proof. exact (EQ_MP (@lem2425365) (@lem2425363)). Qed.
Lemma lem2425367 : term604 = True.
Proof. exact (TRANS (@lem2425362) (@lem2425366)). Qed.
Lemma lem2425368 : True = term604.
Proof. exact (SYM (@lem2425367)). Qed.
Lemma lem2425369 : term604.
Proof. exact (EQ_MP (@lem2425368) (@lem0)). Qed.
Lemma lem2425370 : term608.
Proof. exact (@lem2425359 (@lem2425369)). Qed.
Lemma lem2425372 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425373 : term604 = term605.
Proof. exact (@lem2425372 (NUMERAL 0) term193). Qed.
Lemma lem2425374 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425375 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425376 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425375 h1) (fun h1 : term605 = True => @lem2425374)). Qed.
Lemma lem2425377 : term605 = True.
Proof. exact (EQ_MP (@lem2425376) (@lem2425374)). Qed.
Lemma lem2425378 : term604 = True.
Proof. exact (TRANS (@lem2425373) (@lem2425377)). Qed.
Lemma lem2425379 : True = term604.
Proof. exact (SYM (@lem2425378)). Qed.
Lemma lem2425380 : term604.
Proof. exact (EQ_MP (@lem2425379) (@lem0)). Qed.
Lemma lem2425381 : term609.
Proof. exact (@lem2425370 (@lem2425380)). Qed.
Lemma lem2425383 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425384 : term555 = term556.
Proof. exact (@lem2425383 term193 term193). Qed.
Lemma lem2425385 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425386 : term558 = term193.
Proof. exact (EQ_MP (@lem2425385) (@lem940073)). Qed.
Lemma lem2425387 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425388 : term556 = term192.
Proof. exact (MK_COMB (@lem2425387) (@lem2425386)). Qed.
Lemma lem2425389 : term555 = term192.
Proof. exact (TRANS (@lem2425384) (@lem2425388)). Qed.
Lemma lem2425391 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2425392 : term568 = term573.
Proof. exact (@lem2425391 term193 term193). Qed.
Lemma lem2425393 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425394 : term558 = term193.
Proof. exact (EQ_MP (@lem2425393) (@lem940073)). Qed.
Lemma lem2425395 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425396 : term556 = term192.
Proof. exact (MK_COMB (@lem2425395) (@lem2425394)). Qed.
Lemma lem2425397 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2425398 : term573 = term546.
Proof. exact (MK_COMB (@lem2425397) (@lem2425396)). Qed.
Lemma lem2425399 : term568 = term546.
Proof. exact (TRANS (@lem2425392) (@lem2425398)). Qed.
Lemma lem2425400 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425401 : term610 = term598.
Proof. exact (MK_COMB (@lem2425400) (@lem2425399)). Qed.
Lemma lem2425402 : term611 = term600.
Proof. exact (MK_COMB (@lem2425401) (@lem2425389)). Qed.
Lemma lem2425404 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2425405 : term600 = term182.
Proof. exact (@lem2425404 term193). Qed.
Lemma lem2425406 : term611 = term182.
Proof. exact (TRANS (@lem2425402) (@lem2425405)). Qed.
Lemma lem2425407 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425408 : term613 = term184.
Proof. exact (MK_COMB (@lem2425407) (@lem2425406)). Qed.
Lemma lem2425409 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2425410 : term614 = term615.
Proof. exact (MK_COMB (@lem2425408) (@lem2425409)). Qed.
Lemma lem2425412 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425413 : term615 = term182.
Proof. exact (@lem2425412 term193). Qed.
Lemma lem2425414 : term614 = term182.
Proof. exact (TRANS (@lem2425410) (@lem2425413)). Qed.
Lemma lem2425416 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425417 : term555 = term556.
Proof. exact (@lem2425416 term193 term193). Qed.
Lemma lem2425418 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425419 : term558 = term193.
Proof. exact (EQ_MP (@lem2425418) (@lem940073)). Qed.
Lemma lem2425420 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425421 : term556 = term192.
Proof. exact (MK_COMB (@lem2425420) (@lem2425419)). Qed.
Lemma lem2425422 : term555 = term192.
Proof. exact (TRANS (@lem2425417) (@lem2425421)). Qed.
Lemma lem2425423 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2425424 : term617 = term615.
Proof. exact (MK_COMB (@lem2425423) (@lem2425422)). Qed.
Lemma lem2425426 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425427 : term615 = term182.
Proof. exact (@lem2425426 term193). Qed.
Lemma lem2425428 : term617 = term182.
Proof. exact (TRANS (@lem2425424) (@lem2425427)). Qed.
Lemma lem2425429 : term182 = term617.
Proof. exact (SYM (@lem2425428)). Qed.
Lemma lem2425430 : term614 = term617.
Proof. exact (TRANS (@lem2425414) (@lem2425429)). Qed.
Lemma lem2425431 : term601 = term543.
Proof. exact (@lem2425381 (@lem2425430)). Qed.
Lemma lem2425432 : term600 = term543.
Proof. exact (TRANS (@lem2425347) (@lem2425431)). Qed.
Lemma lem2425434 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2425435 : term543 = term182.
Proof. exact (@lem2425434 term182). Qed.
Lemma lem2425436 : term600 = term182.
Proof. exact (TRANS (@lem2425432) (@lem2425435)). Qed.
Lemma lem2425437 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425438 : term618 = term184.
Proof. exact (MK_COMB (@lem2425437) (@lem2425436)). Qed.
Lemma lem2425439 (z : int) (z' : int) : (term177 z z') = (term177 z z').
Proof. exact (eq_refl (term177 z z')). Qed.
Lemma lem2425440 (z : int) (z' : int) : (term1181 z z') = (term1182 z z').
Proof. exact (MK_COMB (@lem2425438) (@lem2425439 z z')). Qed.
Lemma lem2425441 (z : int) (z' : int) : (term1186 z z') = (term1182 z z').
Proof. exact (TRANS (@lem2425338 z z') (@lem2425440 z z')). Qed.
Lemma lem2425442 (z : int) (z' : int) : (term1182 z z') = term182.
Proof. exact (@lem1982719 (term177 z z')). Qed.
Lemma lem2425443 (z : int) (z' : int) : (term1186 z z') = term182.
Proof. exact (TRANS (@lem2425441 z z') (@lem2425442 z z')). Qed.
Lemma lem2425444 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425445 (z : int) (z' : int) : (term1187 z z') = term206.
Proof. exact (MK_COMB (@lem2425444) (@lem2425443 z z')). Qed.
Lemma lem2425446 : term546 = term546.
Proof. exact (eq_refl term546). Qed.
Lemma lem2425447 (z : int) (z' : int) : (term1221 z z') = term576.
Proof. exact (MK_COMB (@lem2425445 z z') (@lem2425446)). Qed.
Lemma lem2425448 (z : int) (z' : int) : (term1220 z z') = term576.
Proof. exact (TRANS (@lem2425337 z z') (@lem2425447 z z')). Qed.
Lemma lem2425449 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2425450 (z : int) (z' : int) : (term1220 z z') = term546.
Proof. exact (TRANS (@lem2425448 z z') (@lem2425449)). Qed.
Lemma lem2425451 (y' : int) (z : int) (z' : int) : (term1218 y' z z') = term576.
Proof. exact (MK_COMB (@lem2425336 z y') (@lem2425450 z z')). Qed.
Lemma lem2425452 (y' : int) (z : int) (z' : int) : (term1217 y' z z') = term576.
Proof. exact (TRANS (@lem2425228 y' z z') (@lem2425451 y' z z')). Qed.
Lemma lem2425453 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2425454 (y' : int) (z : int) (z' : int) : (term1217 y' z z') = term546.
Proof. exact (TRANS (@lem2425452 y' z z') (@lem2425453)). Qed.
Lemma lem2425455 (y : int) (y' : int) (z : int) (z' : int) : (term1216 y y' z z') = term576.
Proof. exact (MK_COMB (@lem2425227 y z') (@lem2425454 y' z z')). Qed.
Lemma lem2425456 (y : int) (y' : int) (z : int) (z' : int) : (term1215 y y' z z') = term576.
Proof. exact (TRANS (@lem2425119 y y' z z') (@lem2425455 y y' z z')). Qed.
Lemma lem2425457 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2425458 (y : int) (y' : int) (z : int) (z' : int) : (term1215 y y' z z') = term546.
Proof. exact (TRANS (@lem2425456 y y' z z') (@lem2425457)). Qed.
Lemma lem2425459 (y : int) (y' : int) (z : int) (z' : int) : (term1214 y y' z z') = term576.
Proof. exact (MK_COMB (@lem2425118 y y') (@lem2425458 y y' z z')). Qed.
Lemma lem2425460 (y : int) (y' : int) (z : int) (z' : int) : (term1213 y y' z z') = term576.
Proof. exact (TRANS (@lem2425010 y y' z z') (@lem2425459 y y' z z')). Qed.
Lemma lem2425461 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2425462 (y : int) (y' : int) (z : int) (z' : int) : (term1213 y y' z z') = term546.
Proof. exact (TRANS (@lem2425460 y y' z z') (@lem2425461)). Qed.
Lemma lem2425463 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2425464 (y : int) (y' : int) (z : int) (z' : int) : (term1222 y y' z z') = term578.
Proof. exact (MK_COMB (@lem2425463) (@lem2425462 y y' z z')). Qed.
Lemma lem2425465 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2425466 (y : int) (y' : int) (z : int) (z' : int) : (term1212 y y' z z') = term579.
Proof. exact (MK_COMB (@lem2425464 y y' z z') (@lem2425465)). Qed.
Lemma lem2425467 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : term579.
Proof. exact (EQ_MP (@lem2425466 y y' z z') (@lem2425009 y y' z z' h1)). Qed.
Lemma lem2425469 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2425470 : term579 = term1099.
Proof. exact (@lem2425469 term182 term546). Qed.
Lemma lem2425472 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2425473 : term546 = term547.
Proof. exact (@lem2425472 term193). Qed.
Lemma lem2425475 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2425476 : term182 = term543.
Proof. exact (@lem2425475 (NUMERAL 0)). Qed.
Lemma lem2425477 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2425478 : term1100 = term1101.
Proof. exact (MK_COMB (@lem2425477) (@lem2425476)). Qed.
Lemma lem2425479 : term1099 = term1102.
Proof. exact (MK_COMB (@lem2425478) (@lem2425473)). Qed.
Lemma lem2425480 : term1103.
Proof. exact (@lem1980026 term182 term192 term546 term192). Qed.
Lemma lem2425482 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425483 : term604 = term605.
Proof. exact (@lem2425482 (NUMERAL 0) term193). Qed.
Lemma lem2425484 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425485 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425486 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425485 h1) (fun h1 : term605 = True => @lem2425484)). Qed.
Lemma lem2425487 : term605 = True.
Proof. exact (EQ_MP (@lem2425486) (@lem2425484)). Qed.
Lemma lem2425488 : term604 = True.
Proof. exact (TRANS (@lem2425483) (@lem2425487)). Qed.
Lemma lem2425489 : True = term604.
Proof. exact (SYM (@lem2425488)). Qed.
Lemma lem2425490 : term604.
Proof. exact (EQ_MP (@lem2425489) (@lem0)). Qed.
Lemma lem2425491 : term1104.
Proof. exact (@lem2425480 (@lem2425490)). Qed.
Lemma lem2425493 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425494 : term604 = term605.
Proof. exact (@lem2425493 (NUMERAL 0) term193). Qed.
Lemma lem2425495 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425496 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425497 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425496 h1) (fun h1 : term605 = True => @lem2425495)). Qed.
Lemma lem2425498 : term605 = True.
Proof. exact (EQ_MP (@lem2425497) (@lem2425495)). Qed.
Lemma lem2425499 : term604 = True.
Proof. exact (TRANS (@lem2425494) (@lem2425498)). Qed.
Lemma lem2425500 : True = term604.
Proof. exact (SYM (@lem2425499)). Qed.
Lemma lem2425501 : term604.
Proof. exact (EQ_MP (@lem2425500) (@lem0)). Qed.
Lemma lem2425502 : term1102 = term1105.
Proof. exact (@lem2425491 (@lem2425501)). Qed.
Lemma lem2425504 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2425505 : term568 = term573.
Proof. exact (@lem2425504 term193 term193). Qed.
Lemma lem2425506 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425507 : term558 = term193.
Proof. exact (EQ_MP (@lem2425506) (@lem940073)). Qed.
Lemma lem2425508 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425509 : term556 = term192.
Proof. exact (MK_COMB (@lem2425508) (@lem2425507)). Qed.
Lemma lem2425510 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2425511 : term573 = term546.
Proof. exact (MK_COMB (@lem2425510) (@lem2425509)). Qed.
Lemma lem2425512 : term568 = term546.
Proof. exact (TRANS (@lem2425505) (@lem2425511)). Qed.
Lemma lem2425514 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425515 : term615 = term182.
Proof. exact (@lem2425514 term193). Qed.
Lemma lem2425516 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2425517 : term1106 = term1100.
Proof. exact (MK_COMB (@lem2425516) (@lem2425515)). Qed.
Lemma lem2425518 : term1105 = term1099.
Proof. exact (MK_COMB (@lem2425517) (@lem2425512)). Qed.
Lemma lem2425520 (m : nat) (n : nat) : (term1107 m n) = (term1108 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2425521 : term1099 = term1109.
Proof. exact (@lem2425520 (NUMERAL 0) term193). Qed.
Lemma lem2425522 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425523 (h1 : term606 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2425524 : (term606 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425523 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem2425522)). Qed.
Lemma lem2425525 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2425524) (@lem2425522)). Qed.
Lemma lem2425526 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2425527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2425528 : term1110 = (and True).
Proof. exact (MK_COMB (@lem2425527) (@lem2425526)). Qed.
Lemma lem2425529 : term1109 = (True /\ False).
Proof. exact (MK_COMB (@lem2425528) (@lem2425525)). Qed.
Lemma lem2425531 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2425532 : term1109 = False.
Proof. exact (TRANS (@lem2425529) (@lem2425531)). Qed.
Lemma lem2425533 : term1099 = False.
Proof. exact (TRANS (@lem2425521) (@lem2425532)). Qed.
Lemma lem2425534 : term1105 = False.
Proof. exact (TRANS (@lem2425518) (@lem2425533)). Qed.
Lemma lem2425535 : term1102 = False.
Proof. exact (TRANS (@lem2425502) (@lem2425534)). Qed.
Lemma lem2425536 : term1099 = False.
Proof. exact (TRANS (@lem2425479) (@lem2425535)). Qed.
Lemma lem2425537 : term579 = False.
Proof. exact (TRANS (@lem2425470) (@lem2425536)). Qed.
Lemma lem2425538 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1193 y y' z z') : False.
Proof. exact (EQ_MP (@lem2425537) (@lem2425467 y y' z z' h1)). Qed.
Lemma lem2425539 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1081 y y' z z') : False.
Proof. exact (or_elim (@lem2424188 y y' z z' h1) (fun h0 : term1165 y y' z z' => @lem2424812 y y' z z' h0) (fun h0 : term1193 y y' z z' => @lem2425538 y y' z z' h0)). Qed.
Lemma lem2425540 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1080 y y' z z') : term1080 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem2425541 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : term1223 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem2425542 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : (term713 y y' z z') = term182.
Proof. exact (proj2 (@lem2425541 y y' z z' h1)). Qed.
Lemma lem2425543 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : term768 y y' z z'.
Proof. exact (proj1 (@lem2425541 y y' z z' h1)). Qed.
Lemma lem2425545 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2425546 : term1112 = term604.
Proof. exact (@lem2425545 term182 term192). Qed.
Lemma lem2425548 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2425549 : term192 = term567.
Proof. exact (@lem2425548 term193). Qed.
Lemma lem2425551 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2425552 : term182 = term543.
Proof. exact (@lem2425551 (NUMERAL 0)). Qed.
Lemma lem2425553 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2425554 : term1113 = term1114.
Proof. exact (MK_COMB (@lem2425553) (@lem2425552)). Qed.
Lemma lem2425555 : term604 = term1115.
Proof. exact (MK_COMB (@lem2425554) (@lem2425549)). Qed.
Lemma lem2425556 : term1116.
Proof. exact (@lem1980255 term182 term192 term192 term192). Qed.
Lemma lem2425558 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425559 : term604 = term605.
Proof. exact (@lem2425558 (NUMERAL 0) term193). Qed.
Lemma lem2425560 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425561 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425562 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425561 h1) (fun h1 : term605 = True => @lem2425560)). Qed.
Lemma lem2425563 : term605 = True.
Proof. exact (EQ_MP (@lem2425562) (@lem2425560)). Qed.
Lemma lem2425564 : term604 = True.
Proof. exact (TRANS (@lem2425559) (@lem2425563)). Qed.
Lemma lem2425565 : True = term604.
Proof. exact (SYM (@lem2425564)). Qed.
Lemma lem2425566 : term604.
Proof. exact (EQ_MP (@lem2425565) (@lem0)). Qed.
Lemma lem2425567 : term1117.
Proof. exact (@lem2425556 (@lem2425566)). Qed.
Lemma lem2425569 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425570 : term604 = term605.
Proof. exact (@lem2425569 (NUMERAL 0) term193). Qed.
Lemma lem2425571 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425572 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425573 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425572 h1) (fun h1 : term605 = True => @lem2425571)). Qed.
Lemma lem2425574 : term605 = True.
Proof. exact (EQ_MP (@lem2425573) (@lem2425571)). Qed.
Lemma lem2425575 : term604 = True.
Proof. exact (TRANS (@lem2425570) (@lem2425574)). Qed.
Lemma lem2425576 : True = term604.
Proof. exact (SYM (@lem2425575)). Qed.
Lemma lem2425577 : term604.
Proof. exact (EQ_MP (@lem2425576) (@lem0)). Qed.
Lemma lem2425578 : term1115 = term1118.
Proof. exact (@lem2425567 (@lem2425577)). Qed.
Lemma lem2425580 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425581 : term555 = term556.
Proof. exact (@lem2425580 term193 term193). Qed.
Lemma lem2425582 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425583 : term558 = term193.
Proof. exact (EQ_MP (@lem2425582) (@lem940073)). Qed.
Lemma lem2425584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425585 : term556 = term192.
Proof. exact (MK_COMB (@lem2425584) (@lem2425583)). Qed.
Lemma lem2425586 : term555 = term192.
Proof. exact (TRANS (@lem2425581) (@lem2425585)). Qed.
Lemma lem2425588 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425589 : term615 = term182.
Proof. exact (@lem2425588 term193). Qed.
Lemma lem2425590 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2425591 : term1119 = term1113.
Proof. exact (MK_COMB (@lem2425590) (@lem2425589)). Qed.
Lemma lem2425592 : term1118 = term604.
Proof. exact (MK_COMB (@lem2425591) (@lem2425586)). Qed.
Lemma lem2425594 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425595 : term604 = term605.
Proof. exact (@lem2425594 (NUMERAL 0) term193). Qed.
Lemma lem2425596 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425597 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425598 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425597 h1) (fun h1 : term605 = True => @lem2425596)). Qed.
Lemma lem2425599 : term605 = True.
Proof. exact (EQ_MP (@lem2425598) (@lem2425596)). Qed.
Lemma lem2425600 : term604 = True.
Proof. exact (TRANS (@lem2425595) (@lem2425599)). Qed.
Lemma lem2425601 : term1118 = True.
Proof. exact (TRANS (@lem2425592) (@lem2425600)). Qed.
Lemma lem2425602 : term1115 = True.
Proof. exact (TRANS (@lem2425578) (@lem2425601)). Qed.
Lemma lem2425603 : term604 = True.
Proof. exact (TRANS (@lem2425555) (@lem2425602)). Qed.
Lemma lem2425604 : term1112 = True.
Proof. exact (TRANS (@lem2425546) (@lem2425603)). Qed.
Lemma lem2425605 : True = term1112.
Proof. exact (SYM (@lem2425604)). Qed.
Lemma lem2425606 : term1112.
Proof. exact (EQ_MP (@lem2425605) (@lem0)). Qed.
Lemma lem2425607 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : term1166 y y' z z'.
Proof. exact (conj (@lem2425606) (@lem2425543 y y' z z' h1)). Qed.
Lemma lem2425609 (x : real) (y : real) : term1121 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2425610 (y : int) (y' : int) (z : int) (z' : int) : term1167 y y' z z'.
Proof. exact (@lem2425609 term192 (term764 y y' z z')). Qed.
Lemma lem2425611 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : term1168 y y' z z'.
Proof. exact (@lem2425610 y y' z z' (@lem2425607 y y' z z' h1)). Qed.
Lemma lem2425612 (y : int) (y' : int) (z : int) (z' : int) : (term1169 y y' z z') = (term764 y y' z z').
Proof. exact (@lem1982733 (term764 y y' z z')). Qed.
Lemma lem2425613 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2425614 (y : int) (y' : int) (z : int) (z' : int) : (term1170 y y' z z') = (term767 y y' z z').
Proof. exact (MK_COMB (@lem2425613) (@lem2425612 y y' z z')). Qed.
Lemma lem2425615 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2425616 (y : int) (y' : int) (z : int) (z' : int) : (term1168 y y' z z') = (term768 y y' z z').
Proof. exact (MK_COMB (@lem2425614 y y' z z') (@lem2425615)). Qed.
Lemma lem2425617 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : term768 y y' z z'.
Proof. exact (EQ_MP (@lem2425616 y y' z z') (@lem2425611 y y' z z' h1)). Qed.
Lemma lem2425619 (y : real) : term1126 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2425620 (y : int) (y' : int) (z : int) (z' : int) : term1171 y y' z z'.
Proof. exact (@lem2425619 (term713 y y' z z')). Qed.
Lemma lem2425621 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : term1172 y y' z z'.
Proof. exact (@lem2425620 y y' z z' (@lem2425542 y y' z z' h1)). Qed.
Lemma lem2425622 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : term1173 y y' z z'.
Proof. exact (@lem2425621 y y' z z' h1 term192). Qed.
Lemma lem2425623 (y : int) (y' : int) (z : int) (z' : int) : (term1173 y y' z z') = ((term1174 y y' z z') = term182).
Proof. exact (eq_refl (term1173 y y' z z')). Qed.
Lemma lem2425624 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : (term1174 y y' z z') = term182.
Proof. exact (EQ_MP (@lem2425623 y y' z z') (@lem2425622 y y' z z' h1)). Qed.
Lemma lem2425625 (y : int) (y' : int) (z : int) (z' : int) : (term1174 y y' z z') = (term713 y y' z z').
Proof. exact (@lem1982733 (term713 y y' z z')). Qed.
Lemma lem2425626 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2425627 (y : int) (y' : int) (z : int) (z' : int) : (term1175 y y' z z') = (term721 y y' z z').
Proof. exact (MK_COMB (@lem2425626) (@lem2425625 y y' z z')). Qed.
Lemma lem2425628 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2425629 (y : int) (y' : int) (z : int) (z' : int) : ((term1174 y y' z z') = term182) = ((term713 y y' z z') = term182).
Proof. exact (MK_COMB (@lem2425627 y y' z z') (@lem2425628)). Qed.
Lemma lem2425630 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : (term713 y y' z z') = term182.
Proof. exact (EQ_MP (@lem2425629 y y' z z') (@lem2425624 y y' z z' h1)). Qed.
Lemma lem2425631 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : term1165 y y' z z'.
Proof. exact (conj (@lem2425630 y y' z z' h1) (@lem2425617 y y' z z' h1)). Qed.
Lemma lem2425633 (x : real) (y : real) : term1132 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2425634 (y : int) (y' : int) (z : int) (z' : int) : term1176 y y' z z'.
Proof. exact (@lem2425633 (term713 y y' z z') (term764 y y' z z')). Qed.
Lemma lem2425635 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : term1177 y y' z z'.
Proof. exact (@lem2425634 y y' z z' (@lem2425631 y y' z z' h1)). Qed.
Lemma lem2425636 (y : int) (y' : int) (z : int) (z' : int) : (term1178 y y' z z') = (term1179 y y' z z').
Proof. exact (@lem1982753 (term177 y y') (term708 y y') (term712 y y' z z') (term763 y y' z z')). Qed.
Lemma lem2425637 (y : int) (y' : int) : (term1180 y y') = (term1181 y y').
Proof. exact (@lem1982715 term546 (term177 y y')). Qed.
Lemma lem2425639 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2425640 : term192 = term567.
Proof. exact (@lem2425639 term193). Qed.
Lemma lem2425642 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2425643 : term546 = term547.
Proof. exact (@lem2425642 term193). Qed.
Lemma lem2425644 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425645 : term598 = term599.
Proof. exact (MK_COMB (@lem2425644) (@lem2425643)). Qed.
Lemma lem2425646 : term600 = term601.
Proof. exact (MK_COMB (@lem2425645) (@lem2425640)). Qed.
Lemma lem2425647 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2425649 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425650 : term604 = term605.
Proof. exact (@lem2425649 (NUMERAL 0) term193). Qed.
Lemma lem2425651 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425652 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425653 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425652 h1) (fun h1 : term605 = True => @lem2425651)). Qed.
Lemma lem2425654 : term605 = True.
Proof. exact (EQ_MP (@lem2425653) (@lem2425651)). Qed.
Lemma lem2425655 : term604 = True.
Proof. exact (TRANS (@lem2425650) (@lem2425654)). Qed.
Lemma lem2425656 : True = term604.
Proof. exact (SYM (@lem2425655)). Qed.
Lemma lem2425657 : term604.
Proof. exact (EQ_MP (@lem2425656) (@lem0)). Qed.
Lemma lem2425658 : term607.
Proof. exact (@lem2425647 (@lem2425657)). Qed.
Lemma lem2425660 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425661 : term604 = term605.
Proof. exact (@lem2425660 (NUMERAL 0) term193). Qed.
Lemma lem2425662 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425663 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425664 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425663 h1) (fun h1 : term605 = True => @lem2425662)). Qed.
Lemma lem2425665 : term605 = True.
Proof. exact (EQ_MP (@lem2425664) (@lem2425662)). Qed.
Lemma lem2425666 : term604 = True.
Proof. exact (TRANS (@lem2425661) (@lem2425665)). Qed.
Lemma lem2425667 : True = term604.
Proof. exact (SYM (@lem2425666)). Qed.
Lemma lem2425668 : term604.
Proof. exact (EQ_MP (@lem2425667) (@lem0)). Qed.
Lemma lem2425669 : term608.
Proof. exact (@lem2425658 (@lem2425668)). Qed.
Lemma lem2425671 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425672 : term604 = term605.
Proof. exact (@lem2425671 (NUMERAL 0) term193). Qed.
Lemma lem2425673 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425674 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425675 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425674 h1) (fun h1 : term605 = True => @lem2425673)). Qed.
Lemma lem2425676 : term605 = True.
Proof. exact (EQ_MP (@lem2425675) (@lem2425673)). Qed.
Lemma lem2425677 : term604 = True.
Proof. exact (TRANS (@lem2425672) (@lem2425676)). Qed.
Lemma lem2425678 : True = term604.
Proof. exact (SYM (@lem2425677)). Qed.
Lemma lem2425679 : term604.
Proof. exact (EQ_MP (@lem2425678) (@lem0)). Qed.
Lemma lem2425680 : term609.
Proof. exact (@lem2425669 (@lem2425679)). Qed.
Lemma lem2425682 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425683 : term555 = term556.
Proof. exact (@lem2425682 term193 term193). Qed.
Lemma lem2425684 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425685 : term558 = term193.
Proof. exact (EQ_MP (@lem2425684) (@lem940073)). Qed.
Lemma lem2425686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425687 : term556 = term192.
Proof. exact (MK_COMB (@lem2425686) (@lem2425685)). Qed.
Lemma lem2425688 : term555 = term192.
Proof. exact (TRANS (@lem2425683) (@lem2425687)). Qed.
Lemma lem2425690 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2425691 : term568 = term573.
Proof. exact (@lem2425690 term193 term193). Qed.
Lemma lem2425692 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425693 : term558 = term193.
Proof. exact (EQ_MP (@lem2425692) (@lem940073)). Qed.
Lemma lem2425694 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425695 : term556 = term192.
Proof. exact (MK_COMB (@lem2425694) (@lem2425693)). Qed.
Lemma lem2425696 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2425697 : term573 = term546.
Proof. exact (MK_COMB (@lem2425696) (@lem2425695)). Qed.
Lemma lem2425698 : term568 = term546.
Proof. exact (TRANS (@lem2425691) (@lem2425697)). Qed.
Lemma lem2425699 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425700 : term610 = term598.
Proof. exact (MK_COMB (@lem2425699) (@lem2425698)). Qed.
Lemma lem2425701 : term611 = term600.
Proof. exact (MK_COMB (@lem2425700) (@lem2425688)). Qed.
Lemma lem2425703 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2425704 : term600 = term182.
Proof. exact (@lem2425703 term193). Qed.
Lemma lem2425705 : term611 = term182.
Proof. exact (TRANS (@lem2425701) (@lem2425704)). Qed.
Lemma lem2425706 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425707 : term613 = term184.
Proof. exact (MK_COMB (@lem2425706) (@lem2425705)). Qed.
Lemma lem2425708 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2425709 : term614 = term615.
Proof. exact (MK_COMB (@lem2425707) (@lem2425708)). Qed.
Lemma lem2425711 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425712 : term615 = term182.
Proof. exact (@lem2425711 term193). Qed.
Lemma lem2425713 : term614 = term182.
Proof. exact (TRANS (@lem2425709) (@lem2425712)). Qed.
Lemma lem2425715 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425716 : term555 = term556.
Proof. exact (@lem2425715 term193 term193). Qed.
Lemma lem2425717 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425718 : term558 = term193.
Proof. exact (EQ_MP (@lem2425717) (@lem940073)). Qed.
Lemma lem2425719 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425720 : term556 = term192.
Proof. exact (MK_COMB (@lem2425719) (@lem2425718)). Qed.
Lemma lem2425721 : term555 = term192.
Proof. exact (TRANS (@lem2425716) (@lem2425720)). Qed.
Lemma lem2425722 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2425723 : term617 = term615.
Proof. exact (MK_COMB (@lem2425722) (@lem2425721)). Qed.
Lemma lem2425725 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425726 : term615 = term182.
Proof. exact (@lem2425725 term193). Qed.
Lemma lem2425727 : term617 = term182.
Proof. exact (TRANS (@lem2425723) (@lem2425726)). Qed.
Lemma lem2425728 : term182 = term617.
Proof. exact (SYM (@lem2425727)). Qed.
Lemma lem2425729 : term614 = term617.
Proof. exact (TRANS (@lem2425713) (@lem2425728)). Qed.
Lemma lem2425730 : term601 = term543.
Proof. exact (@lem2425680 (@lem2425729)). Qed.
Lemma lem2425731 : term600 = term543.
Proof. exact (TRANS (@lem2425646) (@lem2425730)). Qed.
Lemma lem2425733 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2425734 : term543 = term182.
Proof. exact (@lem2425733 term182). Qed.
Lemma lem2425735 : term600 = term182.
Proof. exact (TRANS (@lem2425731) (@lem2425734)). Qed.
Lemma lem2425736 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425737 : term618 = term184.
Proof. exact (MK_COMB (@lem2425736) (@lem2425735)). Qed.
Lemma lem2425738 (y : int) (y' : int) : (term177 y y') = (term177 y y').
Proof. exact (eq_refl (term177 y y')). Qed.
Lemma lem2425739 (y : int) (y' : int) : (term1181 y y') = (term1182 y y').
Proof. exact (MK_COMB (@lem2425737) (@lem2425738 y y')). Qed.
Lemma lem2425740 (y : int) (y' : int) : (term1180 y y') = (term1182 y y').
Proof. exact (TRANS (@lem2425637 y y') (@lem2425739 y y')). Qed.
Lemma lem2425741 (y : int) (y' : int) : (term1182 y y') = term182.
Proof. exact (@lem1982719 (term177 y y')). Qed.
Lemma lem2425742 (y : int) (y' : int) : (term1180 y y') = term182.
Proof. exact (TRANS (@lem2425740 y y') (@lem2425741 y y')). Qed.
Lemma lem2425743 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425744 (y : int) (y' : int) : (term1183 y y') = term206.
Proof. exact (MK_COMB (@lem2425743) (@lem2425742 y y')). Qed.
Lemma lem2425745 (y : int) (y' : int) (z : int) (z' : int) : (term1184 y y' z z') = (term1185 y y' z z').
Proof. exact (@lem1982753 (term708 y z') (term177 y z') (term710 y' z z') (term762 y' z z')). Qed.
Lemma lem2425746 (y : int) (z' : int) : (term1186 y z') = (term1181 y z').
Proof. exact (@lem1982713 term546 (term177 y z')). Qed.
Lemma lem2425748 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2425749 : term192 = term567.
Proof. exact (@lem2425748 term193). Qed.
Lemma lem2425751 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2425752 : term546 = term547.
Proof. exact (@lem2425751 term193). Qed.
Lemma lem2425753 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425754 : term598 = term599.
Proof. exact (MK_COMB (@lem2425753) (@lem2425752)). Qed.
Lemma lem2425755 : term600 = term601.
Proof. exact (MK_COMB (@lem2425754) (@lem2425749)). Qed.
Lemma lem2425756 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2425758 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425759 : term604 = term605.
Proof. exact (@lem2425758 (NUMERAL 0) term193). Qed.
Lemma lem2425760 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425761 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425762 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425761 h1) (fun h1 : term605 = True => @lem2425760)). Qed.
Lemma lem2425763 : term605 = True.
Proof. exact (EQ_MP (@lem2425762) (@lem2425760)). Qed.
Lemma lem2425764 : term604 = True.
Proof. exact (TRANS (@lem2425759) (@lem2425763)). Qed.
Lemma lem2425765 : True = term604.
Proof. exact (SYM (@lem2425764)). Qed.
Lemma lem2425766 : term604.
Proof. exact (EQ_MP (@lem2425765) (@lem0)). Qed.
Lemma lem2425767 : term607.
Proof. exact (@lem2425756 (@lem2425766)). Qed.
Lemma lem2425769 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425770 : term604 = term605.
Proof. exact (@lem2425769 (NUMERAL 0) term193). Qed.
Lemma lem2425771 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425772 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425773 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425772 h1) (fun h1 : term605 = True => @lem2425771)). Qed.
Lemma lem2425774 : term605 = True.
Proof. exact (EQ_MP (@lem2425773) (@lem2425771)). Qed.
Lemma lem2425775 : term604 = True.
Proof. exact (TRANS (@lem2425770) (@lem2425774)). Qed.
Lemma lem2425776 : True = term604.
Proof. exact (SYM (@lem2425775)). Qed.
Lemma lem2425777 : term604.
Proof. exact (EQ_MP (@lem2425776) (@lem0)). Qed.
Lemma lem2425778 : term608.
Proof. exact (@lem2425767 (@lem2425777)). Qed.
Lemma lem2425780 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425781 : term604 = term605.
Proof. exact (@lem2425780 (NUMERAL 0) term193). Qed.
Lemma lem2425782 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425783 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425784 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425783 h1) (fun h1 : term605 = True => @lem2425782)). Qed.
Lemma lem2425785 : term605 = True.
Proof. exact (EQ_MP (@lem2425784) (@lem2425782)). Qed.
Lemma lem2425786 : term604 = True.
Proof. exact (TRANS (@lem2425781) (@lem2425785)). Qed.
Lemma lem2425787 : True = term604.
Proof. exact (SYM (@lem2425786)). Qed.
Lemma lem2425788 : term604.
Proof. exact (EQ_MP (@lem2425787) (@lem0)). Qed.
Lemma lem2425789 : term609.
Proof. exact (@lem2425778 (@lem2425788)). Qed.
Lemma lem2425791 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425792 : term555 = term556.
Proof. exact (@lem2425791 term193 term193). Qed.
Lemma lem2425793 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425794 : term558 = term193.
Proof. exact (EQ_MP (@lem2425793) (@lem940073)). Qed.
Lemma lem2425795 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425796 : term556 = term192.
Proof. exact (MK_COMB (@lem2425795) (@lem2425794)). Qed.
Lemma lem2425797 : term555 = term192.
Proof. exact (TRANS (@lem2425792) (@lem2425796)). Qed.
Lemma lem2425799 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2425800 : term568 = term573.
Proof. exact (@lem2425799 term193 term193). Qed.
Lemma lem2425801 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425802 : term558 = term193.
Proof. exact (EQ_MP (@lem2425801) (@lem940073)). Qed.
Lemma lem2425803 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425804 : term556 = term192.
Proof. exact (MK_COMB (@lem2425803) (@lem2425802)). Qed.
Lemma lem2425805 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2425806 : term573 = term546.
Proof. exact (MK_COMB (@lem2425805) (@lem2425804)). Qed.
Lemma lem2425807 : term568 = term546.
Proof. exact (TRANS (@lem2425800) (@lem2425806)). Qed.
Lemma lem2425808 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425809 : term610 = term598.
Proof. exact (MK_COMB (@lem2425808) (@lem2425807)). Qed.
Lemma lem2425810 : term611 = term600.
Proof. exact (MK_COMB (@lem2425809) (@lem2425797)). Qed.
Lemma lem2425812 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2425813 : term600 = term182.
Proof. exact (@lem2425812 term193). Qed.
Lemma lem2425814 : term611 = term182.
Proof. exact (TRANS (@lem2425810) (@lem2425813)). Qed.
Lemma lem2425815 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425816 : term613 = term184.
Proof. exact (MK_COMB (@lem2425815) (@lem2425814)). Qed.
Lemma lem2425817 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2425818 : term614 = term615.
Proof. exact (MK_COMB (@lem2425816) (@lem2425817)). Qed.
Lemma lem2425820 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425821 : term615 = term182.
Proof. exact (@lem2425820 term193). Qed.
Lemma lem2425822 : term614 = term182.
Proof. exact (TRANS (@lem2425818) (@lem2425821)). Qed.
Lemma lem2425824 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425825 : term555 = term556.
Proof. exact (@lem2425824 term193 term193). Qed.
Lemma lem2425826 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425827 : term558 = term193.
Proof. exact (EQ_MP (@lem2425826) (@lem940073)). Qed.
Lemma lem2425828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425829 : term556 = term192.
Proof. exact (MK_COMB (@lem2425828) (@lem2425827)). Qed.
Lemma lem2425830 : term555 = term192.
Proof. exact (TRANS (@lem2425825) (@lem2425829)). Qed.
Lemma lem2425831 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2425832 : term617 = term615.
Proof. exact (MK_COMB (@lem2425831) (@lem2425830)). Qed.
Lemma lem2425834 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425835 : term615 = term182.
Proof. exact (@lem2425834 term193). Qed.
Lemma lem2425836 : term617 = term182.
Proof. exact (TRANS (@lem2425832) (@lem2425835)). Qed.
Lemma lem2425837 : term182 = term617.
Proof. exact (SYM (@lem2425836)). Qed.
Lemma lem2425838 : term614 = term617.
Proof. exact (TRANS (@lem2425822) (@lem2425837)). Qed.
Lemma lem2425839 : term601 = term543.
Proof. exact (@lem2425789 (@lem2425838)). Qed.
Lemma lem2425840 : term600 = term543.
Proof. exact (TRANS (@lem2425755) (@lem2425839)). Qed.
Lemma lem2425842 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2425843 : term543 = term182.
Proof. exact (@lem2425842 term182). Qed.
Lemma lem2425844 : term600 = term182.
Proof. exact (TRANS (@lem2425840) (@lem2425843)). Qed.
Lemma lem2425845 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425846 : term618 = term184.
Proof. exact (MK_COMB (@lem2425845) (@lem2425844)). Qed.
Lemma lem2425847 (y : int) (z' : int) : (term177 y z') = (term177 y z').
Proof. exact (eq_refl (term177 y z')). Qed.
Lemma lem2425848 (y : int) (z' : int) : (term1181 y z') = (term1182 y z').
Proof. exact (MK_COMB (@lem2425846) (@lem2425847 y z')). Qed.
Lemma lem2425849 (y : int) (z' : int) : (term1186 y z') = (term1182 y z').
Proof. exact (TRANS (@lem2425746 y z') (@lem2425848 y z')). Qed.
Lemma lem2425850 (y : int) (z' : int) : (term1182 y z') = term182.
Proof. exact (@lem1982719 (term177 y z')). Qed.
Lemma lem2425851 (y : int) (z' : int) : (term1186 y z') = term182.
Proof. exact (TRANS (@lem2425849 y z') (@lem2425850 y z')). Qed.
Lemma lem2425852 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425853 (y : int) (z' : int) : (term1187 y z') = term206.
Proof. exact (MK_COMB (@lem2425852) (@lem2425851 y z')). Qed.
Lemma lem2425854 (y' : int) (z : int) (z' : int) : (term1188 y' z z') = (term1189 y' z z').
Proof. exact (@lem1982753 (term708 z y') (term177 z y') (term177 z z') (term759 z z')). Qed.
Lemma lem2425855 (z : int) (y' : int) : (term1186 z y') = (term1181 z y').
Proof. exact (@lem1982713 term546 (term177 z y')). Qed.
Lemma lem2425857 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2425858 : term192 = term567.
Proof. exact (@lem2425857 term193). Qed.
Lemma lem2425860 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2425861 : term546 = term547.
Proof. exact (@lem2425860 term193). Qed.
Lemma lem2425862 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425863 : term598 = term599.
Proof. exact (MK_COMB (@lem2425862) (@lem2425861)). Qed.
Lemma lem2425864 : term600 = term601.
Proof. exact (MK_COMB (@lem2425863) (@lem2425858)). Qed.
Lemma lem2425865 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2425867 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425868 : term604 = term605.
Proof. exact (@lem2425867 (NUMERAL 0) term193). Qed.
Lemma lem2425869 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425870 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425871 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425870 h1) (fun h1 : term605 = True => @lem2425869)). Qed.
Lemma lem2425872 : term605 = True.
Proof. exact (EQ_MP (@lem2425871) (@lem2425869)). Qed.
Lemma lem2425873 : term604 = True.
Proof. exact (TRANS (@lem2425868) (@lem2425872)). Qed.
Lemma lem2425874 : True = term604.
Proof. exact (SYM (@lem2425873)). Qed.
Lemma lem2425875 : term604.
Proof. exact (EQ_MP (@lem2425874) (@lem0)). Qed.
Lemma lem2425876 : term607.
Proof. exact (@lem2425865 (@lem2425875)). Qed.
Lemma lem2425878 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425879 : term604 = term605.
Proof. exact (@lem2425878 (NUMERAL 0) term193). Qed.
Lemma lem2425880 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425881 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425882 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425881 h1) (fun h1 : term605 = True => @lem2425880)). Qed.
Lemma lem2425883 : term605 = True.
Proof. exact (EQ_MP (@lem2425882) (@lem2425880)). Qed.
Lemma lem2425884 : term604 = True.
Proof. exact (TRANS (@lem2425879) (@lem2425883)). Qed.
Lemma lem2425885 : True = term604.
Proof. exact (SYM (@lem2425884)). Qed.
Lemma lem2425886 : term604.
Proof. exact (EQ_MP (@lem2425885) (@lem0)). Qed.
Lemma lem2425887 : term608.
Proof. exact (@lem2425876 (@lem2425886)). Qed.
Lemma lem2425889 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425890 : term604 = term605.
Proof. exact (@lem2425889 (NUMERAL 0) term193). Qed.
Lemma lem2425891 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425892 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425893 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425892 h1) (fun h1 : term605 = True => @lem2425891)). Qed.
Lemma lem2425894 : term605 = True.
Proof. exact (EQ_MP (@lem2425893) (@lem2425891)). Qed.
Lemma lem2425895 : term604 = True.
Proof. exact (TRANS (@lem2425890) (@lem2425894)). Qed.
Lemma lem2425896 : True = term604.
Proof. exact (SYM (@lem2425895)). Qed.
Lemma lem2425897 : term604.
Proof. exact (EQ_MP (@lem2425896) (@lem0)). Qed.
Lemma lem2425898 : term609.
Proof. exact (@lem2425887 (@lem2425897)). Qed.
Lemma lem2425900 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425901 : term555 = term556.
Proof. exact (@lem2425900 term193 term193). Qed.
Lemma lem2425902 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425903 : term558 = term193.
Proof. exact (EQ_MP (@lem2425902) (@lem940073)). Qed.
Lemma lem2425904 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425905 : term556 = term192.
Proof. exact (MK_COMB (@lem2425904) (@lem2425903)). Qed.
Lemma lem2425906 : term555 = term192.
Proof. exact (TRANS (@lem2425901) (@lem2425905)). Qed.
Lemma lem2425908 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2425909 : term568 = term573.
Proof. exact (@lem2425908 term193 term193). Qed.
Lemma lem2425910 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425911 : term558 = term193.
Proof. exact (EQ_MP (@lem2425910) (@lem940073)). Qed.
Lemma lem2425912 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425913 : term556 = term192.
Proof. exact (MK_COMB (@lem2425912) (@lem2425911)). Qed.
Lemma lem2425914 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2425915 : term573 = term546.
Proof. exact (MK_COMB (@lem2425914) (@lem2425913)). Qed.
Lemma lem2425916 : term568 = term546.
Proof. exact (TRANS (@lem2425909) (@lem2425915)). Qed.
Lemma lem2425917 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425918 : term610 = term598.
Proof. exact (MK_COMB (@lem2425917) (@lem2425916)). Qed.
Lemma lem2425919 : term611 = term600.
Proof. exact (MK_COMB (@lem2425918) (@lem2425906)). Qed.
Lemma lem2425921 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2425922 : term600 = term182.
Proof. exact (@lem2425921 term193). Qed.
Lemma lem2425923 : term611 = term182.
Proof. exact (TRANS (@lem2425919) (@lem2425922)). Qed.
Lemma lem2425924 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425925 : term613 = term184.
Proof. exact (MK_COMB (@lem2425924) (@lem2425923)). Qed.
Lemma lem2425926 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2425927 : term614 = term615.
Proof. exact (MK_COMB (@lem2425925) (@lem2425926)). Qed.
Lemma lem2425929 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425930 : term615 = term182.
Proof. exact (@lem2425929 term193). Qed.
Lemma lem2425931 : term614 = term182.
Proof. exact (TRANS (@lem2425927) (@lem2425930)). Qed.
Lemma lem2425933 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2425934 : term555 = term556.
Proof. exact (@lem2425933 term193 term193). Qed.
Lemma lem2425935 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2425936 : term558 = term193.
Proof. exact (EQ_MP (@lem2425935) (@lem940073)). Qed.
Lemma lem2425937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2425938 : term556 = term192.
Proof. exact (MK_COMB (@lem2425937) (@lem2425936)). Qed.
Lemma lem2425939 : term555 = term192.
Proof. exact (TRANS (@lem2425934) (@lem2425938)). Qed.
Lemma lem2425940 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2425941 : term617 = term615.
Proof. exact (MK_COMB (@lem2425940) (@lem2425939)). Qed.
Lemma lem2425943 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2425944 : term615 = term182.
Proof. exact (@lem2425943 term193). Qed.
Lemma lem2425945 : term617 = term182.
Proof. exact (TRANS (@lem2425941) (@lem2425944)). Qed.
Lemma lem2425946 : term182 = term617.
Proof. exact (SYM (@lem2425945)). Qed.
Lemma lem2425947 : term614 = term617.
Proof. exact (TRANS (@lem2425931) (@lem2425946)). Qed.
Lemma lem2425948 : term601 = term543.
Proof. exact (@lem2425898 (@lem2425947)). Qed.
Lemma lem2425949 : term600 = term543.
Proof. exact (TRANS (@lem2425864) (@lem2425948)). Qed.
Lemma lem2425951 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2425952 : term543 = term182.
Proof. exact (@lem2425951 term182). Qed.
Lemma lem2425953 : term600 = term182.
Proof. exact (TRANS (@lem2425949) (@lem2425952)). Qed.
Lemma lem2425954 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2425955 : term618 = term184.
Proof. exact (MK_COMB (@lem2425954) (@lem2425953)). Qed.
Lemma lem2425956 (z : int) (y' : int) : (term177 z y') = (term177 z y').
Proof. exact (eq_refl (term177 z y')). Qed.
Lemma lem2425957 (z : int) (y' : int) : (term1181 z y') = (term1182 z y').
Proof. exact (MK_COMB (@lem2425955) (@lem2425956 z y')). Qed.
Lemma lem2425958 (z : int) (y' : int) : (term1186 z y') = (term1182 z y').
Proof. exact (TRANS (@lem2425855 z y') (@lem2425957 z y')). Qed.
Lemma lem2425959 (z : int) (y' : int) : (term1182 z y') = term182.
Proof. exact (@lem1982719 (term177 z y')). Qed.
Lemma lem2425960 (z : int) (y' : int) : (term1186 z y') = term182.
Proof. exact (TRANS (@lem2425958 z y') (@lem2425959 z y')). Qed.
Lemma lem2425961 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425962 (z : int) (y' : int) : (term1187 z y') = term206.
Proof. exact (MK_COMB (@lem2425961) (@lem2425960 z y')). Qed.
Lemma lem2425963 (z : int) (z' : int) : (term1190 z z') = (term1191 z z').
Proof. exact (@lem1982763 (term177 z z') (term708 z z') term546). Qed.
Lemma lem2425964 (z : int) (z' : int) : (term1180 z z') = (term1181 z z').
Proof. exact (@lem1982715 term546 (term177 z z')). Qed.
Lemma lem2425966 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2425967 : term192 = term567.
Proof. exact (@lem2425966 term193). Qed.
Lemma lem2425969 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2425970 : term546 = term547.
Proof. exact (@lem2425969 term193). Qed.
Lemma lem2425971 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2425972 : term598 = term599.
Proof. exact (MK_COMB (@lem2425971) (@lem2425970)). Qed.
Lemma lem2425973 : term600 = term601.
Proof. exact (MK_COMB (@lem2425972) (@lem2425967)). Qed.
Lemma lem2425974 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2425976 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425977 : term604 = term605.
Proof. exact (@lem2425976 (NUMERAL 0) term193). Qed.
Lemma lem2425978 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425979 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425980 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425979 h1) (fun h1 : term605 = True => @lem2425978)). Qed.
Lemma lem2425981 : term605 = True.
Proof. exact (EQ_MP (@lem2425980) (@lem2425978)). Qed.
Lemma lem2425982 : term604 = True.
Proof. exact (TRANS (@lem2425977) (@lem2425981)). Qed.
Lemma lem2425983 : True = term604.
Proof. exact (SYM (@lem2425982)). Qed.
Lemma lem2425984 : term604.
Proof. exact (EQ_MP (@lem2425983) (@lem0)). Qed.
Lemma lem2425985 : term607.
Proof. exact (@lem2425974 (@lem2425984)). Qed.
Lemma lem2425987 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425988 : term604 = term605.
Proof. exact (@lem2425987 (NUMERAL 0) term193). Qed.
Lemma lem2425989 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2425990 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2425991 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2425990 h1) (fun h1 : term605 = True => @lem2425989)). Qed.
Lemma lem2425992 : term605 = True.
Proof. exact (EQ_MP (@lem2425991) (@lem2425989)). Qed.
Lemma lem2425993 : term604 = True.
Proof. exact (TRANS (@lem2425988) (@lem2425992)). Qed.
Lemma lem2425994 : True = term604.
Proof. exact (SYM (@lem2425993)). Qed.
Lemma lem2425995 : term604.
Proof. exact (EQ_MP (@lem2425994) (@lem0)). Qed.
Lemma lem2425996 : term608.
Proof. exact (@lem2425985 (@lem2425995)). Qed.
Lemma lem2425998 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2425999 : term604 = term605.
Proof. exact (@lem2425998 (NUMERAL 0) term193). Qed.
Lemma lem2426000 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426001 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426002 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426001 h1) (fun h1 : term605 = True => @lem2426000)). Qed.
Lemma lem2426003 : term605 = True.
Proof. exact (EQ_MP (@lem2426002) (@lem2426000)). Qed.
Lemma lem2426004 : term604 = True.
Proof. exact (TRANS (@lem2425999) (@lem2426003)). Qed.
Lemma lem2426005 : True = term604.
Proof. exact (SYM (@lem2426004)). Qed.
Lemma lem2426006 : term604.
Proof. exact (EQ_MP (@lem2426005) (@lem0)). Qed.
Lemma lem2426007 : term609.
Proof. exact (@lem2425996 (@lem2426006)). Qed.
Lemma lem2426009 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426010 : term555 = term556.
Proof. exact (@lem2426009 term193 term193). Qed.
Lemma lem2426011 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426012 : term558 = term193.
Proof. exact (EQ_MP (@lem2426011) (@lem940073)). Qed.
Lemma lem2426013 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426014 : term556 = term192.
Proof. exact (MK_COMB (@lem2426013) (@lem2426012)). Qed.
Lemma lem2426015 : term555 = term192.
Proof. exact (TRANS (@lem2426010) (@lem2426014)). Qed.
Lemma lem2426017 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2426018 : term568 = term573.
Proof. exact (@lem2426017 term193 term193). Qed.
Lemma lem2426019 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426020 : term558 = term193.
Proof. exact (EQ_MP (@lem2426019) (@lem940073)). Qed.
Lemma lem2426021 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426022 : term556 = term192.
Proof. exact (MK_COMB (@lem2426021) (@lem2426020)). Qed.
Lemma lem2426023 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2426024 : term573 = term546.
Proof. exact (MK_COMB (@lem2426023) (@lem2426022)). Qed.
Lemma lem2426025 : term568 = term546.
Proof. exact (TRANS (@lem2426018) (@lem2426024)). Qed.
Lemma lem2426026 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426027 : term610 = term598.
Proof. exact (MK_COMB (@lem2426026) (@lem2426025)). Qed.
Lemma lem2426028 : term611 = term600.
Proof. exact (MK_COMB (@lem2426027) (@lem2426015)). Qed.
Lemma lem2426030 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2426031 : term600 = term182.
Proof. exact (@lem2426030 term193). Qed.
Lemma lem2426032 : term611 = term182.
Proof. exact (TRANS (@lem2426028) (@lem2426031)). Qed.
Lemma lem2426033 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426034 : term613 = term184.
Proof. exact (MK_COMB (@lem2426033) (@lem2426032)). Qed.
Lemma lem2426035 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2426036 : term614 = term615.
Proof. exact (MK_COMB (@lem2426034) (@lem2426035)). Qed.
Lemma lem2426038 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426039 : term615 = term182.
Proof. exact (@lem2426038 term193). Qed.
Lemma lem2426040 : term614 = term182.
Proof. exact (TRANS (@lem2426036) (@lem2426039)). Qed.
Lemma lem2426042 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426043 : term555 = term556.
Proof. exact (@lem2426042 term193 term193). Qed.
Lemma lem2426044 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426045 : term558 = term193.
Proof. exact (EQ_MP (@lem2426044) (@lem940073)). Qed.
Lemma lem2426046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426047 : term556 = term192.
Proof. exact (MK_COMB (@lem2426046) (@lem2426045)). Qed.
Lemma lem2426048 : term555 = term192.
Proof. exact (TRANS (@lem2426043) (@lem2426047)). Qed.
Lemma lem2426049 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2426050 : term617 = term615.
Proof. exact (MK_COMB (@lem2426049) (@lem2426048)). Qed.
Lemma lem2426052 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426053 : term615 = term182.
Proof. exact (@lem2426052 term193). Qed.
Lemma lem2426054 : term617 = term182.
Proof. exact (TRANS (@lem2426050) (@lem2426053)). Qed.
Lemma lem2426055 : term182 = term617.
Proof. exact (SYM (@lem2426054)). Qed.
Lemma lem2426056 : term614 = term617.
Proof. exact (TRANS (@lem2426040) (@lem2426055)). Qed.
Lemma lem2426057 : term601 = term543.
Proof. exact (@lem2426007 (@lem2426056)). Qed.
Lemma lem2426058 : term600 = term543.
Proof. exact (TRANS (@lem2425973) (@lem2426057)). Qed.
Lemma lem2426060 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2426061 : term543 = term182.
Proof. exact (@lem2426060 term182). Qed.
Lemma lem2426062 : term600 = term182.
Proof. exact (TRANS (@lem2426058) (@lem2426061)). Qed.
Lemma lem2426063 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426064 : term618 = term184.
Proof. exact (MK_COMB (@lem2426063) (@lem2426062)). Qed.
Lemma lem2426065 (z : int) (z' : int) : (term177 z z') = (term177 z z').
Proof. exact (eq_refl (term177 z z')). Qed.
Lemma lem2426066 (z : int) (z' : int) : (term1181 z z') = (term1182 z z').
Proof. exact (MK_COMB (@lem2426064) (@lem2426065 z z')). Qed.
Lemma lem2426067 (z : int) (z' : int) : (term1180 z z') = (term1182 z z').
Proof. exact (TRANS (@lem2425964 z z') (@lem2426066 z z')). Qed.
Lemma lem2426068 (z : int) (z' : int) : (term1182 z z') = term182.
Proof. exact (@lem1982719 (term177 z z')). Qed.
Lemma lem2426069 (z : int) (z' : int) : (term1180 z z') = term182.
Proof. exact (TRANS (@lem2426067 z z') (@lem2426068 z z')). Qed.
Lemma lem2426070 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426071 (z : int) (z' : int) : (term1183 z z') = term206.
Proof. exact (MK_COMB (@lem2426070) (@lem2426069 z z')). Qed.
Lemma lem2426072 : term546 = term546.
Proof. exact (eq_refl term546). Qed.
Lemma lem2426073 (z : int) (z' : int) : (term1191 z z') = term576.
Proof. exact (MK_COMB (@lem2426071 z z') (@lem2426072)). Qed.
Lemma lem2426074 (z : int) (z' : int) : (term1190 z z') = term576.
Proof. exact (TRANS (@lem2425963 z z') (@lem2426073 z z')). Qed.
Lemma lem2426075 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2426076 (z : int) (z' : int) : (term1190 z z') = term546.
Proof. exact (TRANS (@lem2426074 z z') (@lem2426075)). Qed.
Lemma lem2426077 (y' : int) (z : int) (z' : int) : (term1189 y' z z') = term576.
Proof. exact (MK_COMB (@lem2425962 z y') (@lem2426076 z z')). Qed.
Lemma lem2426078 (y' : int) (z : int) (z' : int) : (term1188 y' z z') = term576.
Proof. exact (TRANS (@lem2425854 y' z z') (@lem2426077 y' z z')). Qed.
Lemma lem2426079 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2426080 (y' : int) (z : int) (z' : int) : (term1188 y' z z') = term546.
Proof. exact (TRANS (@lem2426078 y' z z') (@lem2426079)). Qed.
Lemma lem2426081 (y : int) (y' : int) (z : int) (z' : int) : (term1185 y y' z z') = term576.
Proof. exact (MK_COMB (@lem2425853 y z') (@lem2426080 y' z z')). Qed.
Lemma lem2426082 (y : int) (y' : int) (z : int) (z' : int) : (term1184 y y' z z') = term576.
Proof. exact (TRANS (@lem2425745 y y' z z') (@lem2426081 y y' z z')). Qed.
Lemma lem2426083 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2426084 (y : int) (y' : int) (z : int) (z' : int) : (term1184 y y' z z') = term546.
Proof. exact (TRANS (@lem2426082 y y' z z') (@lem2426083)). Qed.
Lemma lem2426085 (y : int) (y' : int) (z : int) (z' : int) : (term1179 y y' z z') = term576.
Proof. exact (MK_COMB (@lem2425744 y y') (@lem2426084 y y' z z')). Qed.
Lemma lem2426086 (y : int) (y' : int) (z : int) (z' : int) : (term1178 y y' z z') = term576.
Proof. exact (TRANS (@lem2425636 y y' z z') (@lem2426085 y y' z z')). Qed.
Lemma lem2426087 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2426088 (y : int) (y' : int) (z : int) (z' : int) : (term1178 y y' z z') = term546.
Proof. exact (TRANS (@lem2426086 y y' z z') (@lem2426087)). Qed.
Lemma lem2426089 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2426090 (y : int) (y' : int) (z : int) (z' : int) : (term1192 y y' z z') = term578.
Proof. exact (MK_COMB (@lem2426089) (@lem2426088 y y' z z')). Qed.
Lemma lem2426091 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2426092 (y : int) (y' : int) (z : int) (z' : int) : (term1177 y y' z z') = term579.
Proof. exact (MK_COMB (@lem2426090 y y' z z') (@lem2426091)). Qed.
Lemma lem2426093 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : term579.
Proof. exact (EQ_MP (@lem2426092 y y' z z') (@lem2425635 y y' z z' h1)). Qed.
Lemma lem2426095 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2426096 : term579 = term1099.
Proof. exact (@lem2426095 term182 term546). Qed.
Lemma lem2426098 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2426099 : term546 = term547.
Proof. exact (@lem2426098 term193). Qed.
Lemma lem2426101 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2426102 : term182 = term543.
Proof. exact (@lem2426101 (NUMERAL 0)). Qed.
Lemma lem2426103 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2426104 : term1100 = term1101.
Proof. exact (MK_COMB (@lem2426103) (@lem2426102)). Qed.
Lemma lem2426105 : term1099 = term1102.
Proof. exact (MK_COMB (@lem2426104) (@lem2426099)). Qed.
Lemma lem2426106 : term1103.
Proof. exact (@lem1980026 term182 term192 term546 term192). Qed.
Lemma lem2426108 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426109 : term604 = term605.
Proof. exact (@lem2426108 (NUMERAL 0) term193). Qed.
Lemma lem2426110 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426111 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426112 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426111 h1) (fun h1 : term605 = True => @lem2426110)). Qed.
Lemma lem2426113 : term605 = True.
Proof. exact (EQ_MP (@lem2426112) (@lem2426110)). Qed.
Lemma lem2426114 : term604 = True.
Proof. exact (TRANS (@lem2426109) (@lem2426113)). Qed.
Lemma lem2426115 : True = term604.
Proof. exact (SYM (@lem2426114)). Qed.
Lemma lem2426116 : term604.
Proof. exact (EQ_MP (@lem2426115) (@lem0)). Qed.
Lemma lem2426117 : term1104.
Proof. exact (@lem2426106 (@lem2426116)). Qed.
Lemma lem2426119 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426120 : term604 = term605.
Proof. exact (@lem2426119 (NUMERAL 0) term193). Qed.
Lemma lem2426121 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426122 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426123 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426122 h1) (fun h1 : term605 = True => @lem2426121)). Qed.
Lemma lem2426124 : term605 = True.
Proof. exact (EQ_MP (@lem2426123) (@lem2426121)). Qed.
Lemma lem2426125 : term604 = True.
Proof. exact (TRANS (@lem2426120) (@lem2426124)). Qed.
Lemma lem2426126 : True = term604.
Proof. exact (SYM (@lem2426125)). Qed.
Lemma lem2426127 : term604.
Proof. exact (EQ_MP (@lem2426126) (@lem0)). Qed.
Lemma lem2426128 : term1102 = term1105.
Proof. exact (@lem2426117 (@lem2426127)). Qed.
Lemma lem2426130 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2426131 : term568 = term573.
Proof. exact (@lem2426130 term193 term193). Qed.
Lemma lem2426132 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426133 : term558 = term193.
Proof. exact (EQ_MP (@lem2426132) (@lem940073)). Qed.
Lemma lem2426134 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426135 : term556 = term192.
Proof. exact (MK_COMB (@lem2426134) (@lem2426133)). Qed.
Lemma lem2426136 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2426137 : term573 = term546.
Proof. exact (MK_COMB (@lem2426136) (@lem2426135)). Qed.
Lemma lem2426138 : term568 = term546.
Proof. exact (TRANS (@lem2426131) (@lem2426137)). Qed.
Lemma lem2426140 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426141 : term615 = term182.
Proof. exact (@lem2426140 term193). Qed.
Lemma lem2426142 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2426143 : term1106 = term1100.
Proof. exact (MK_COMB (@lem2426142) (@lem2426141)). Qed.
Lemma lem2426144 : term1105 = term1099.
Proof. exact (MK_COMB (@lem2426143) (@lem2426138)). Qed.
Lemma lem2426146 (m : nat) (n : nat) : (term1107 m n) = (term1108 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2426147 : term1099 = term1109.
Proof. exact (@lem2426146 (NUMERAL 0) term193). Qed.
Lemma lem2426148 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426149 (h1 : term606 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2426150 : (term606 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426149 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem2426148)). Qed.
Lemma lem2426151 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2426150) (@lem2426148)). Qed.
Lemma lem2426152 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2426153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2426154 : term1110 = (and True).
Proof. exact (MK_COMB (@lem2426153) (@lem2426152)). Qed.
Lemma lem2426155 : term1109 = (True /\ False).
Proof. exact (MK_COMB (@lem2426154) (@lem2426151)). Qed.
Lemma lem2426157 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2426158 : term1109 = False.
Proof. exact (TRANS (@lem2426155) (@lem2426157)). Qed.
Lemma lem2426159 : term1099 = False.
Proof. exact (TRANS (@lem2426147) (@lem2426158)). Qed.
Lemma lem2426160 : term1105 = False.
Proof. exact (TRANS (@lem2426144) (@lem2426159)). Qed.
Lemma lem2426161 : term1102 = False.
Proof. exact (TRANS (@lem2426128) (@lem2426160)). Qed.
Lemma lem2426162 : term1099 = False.
Proof. exact (TRANS (@lem2426105) (@lem2426161)). Qed.
Lemma lem2426163 : term579 = False.
Proof. exact (TRANS (@lem2426096) (@lem2426162)). Qed.
Lemma lem2426164 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1223 y y' z z') : False.
Proof. exact (EQ_MP (@lem2426163) (@lem2426093 y y' z z' h1)). Qed.
Lemma lem2426165 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : term1224 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem2426166 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : (term713 y y' z z') = term182.
Proof. exact (proj2 (@lem2426165 y y' z z' h1)). Qed.
Lemma lem2426167 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : term784 y y' z z'.
Proof. exact (proj1 (@lem2426165 y y' z z' h1)). Qed.
Lemma lem2426169 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2426170 : term1112 = term604.
Proof. exact (@lem2426169 term182 term192). Qed.
Lemma lem2426172 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2426173 : term192 = term567.
Proof. exact (@lem2426172 term193). Qed.
Lemma lem2426175 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2426176 : term182 = term543.
Proof. exact (@lem2426175 (NUMERAL 0)). Qed.
Lemma lem2426177 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2426178 : term1113 = term1114.
Proof. exact (MK_COMB (@lem2426177) (@lem2426176)). Qed.
Lemma lem2426179 : term604 = term1115.
Proof. exact (MK_COMB (@lem2426178) (@lem2426173)). Qed.
Lemma lem2426180 : term1116.
Proof. exact (@lem1980255 term182 term192 term192 term192). Qed.
Lemma lem2426182 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426183 : term604 = term605.
Proof. exact (@lem2426182 (NUMERAL 0) term193). Qed.
Lemma lem2426184 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426185 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426186 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426185 h1) (fun h1 : term605 = True => @lem2426184)). Qed.
Lemma lem2426187 : term605 = True.
Proof. exact (EQ_MP (@lem2426186) (@lem2426184)). Qed.
Lemma lem2426188 : term604 = True.
Proof. exact (TRANS (@lem2426183) (@lem2426187)). Qed.
Lemma lem2426189 : True = term604.
Proof. exact (SYM (@lem2426188)). Qed.
Lemma lem2426190 : term604.
Proof. exact (EQ_MP (@lem2426189) (@lem0)). Qed.
Lemma lem2426191 : term1117.
Proof. exact (@lem2426180 (@lem2426190)). Qed.
Lemma lem2426193 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426194 : term604 = term605.
Proof. exact (@lem2426193 (NUMERAL 0) term193). Qed.
Lemma lem2426195 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426196 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426197 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426196 h1) (fun h1 : term605 = True => @lem2426195)). Qed.
Lemma lem2426198 : term605 = True.
Proof. exact (EQ_MP (@lem2426197) (@lem2426195)). Qed.
Lemma lem2426199 : term604 = True.
Proof. exact (TRANS (@lem2426194) (@lem2426198)). Qed.
Lemma lem2426200 : True = term604.
Proof. exact (SYM (@lem2426199)). Qed.
Lemma lem2426201 : term604.
Proof. exact (EQ_MP (@lem2426200) (@lem0)). Qed.
Lemma lem2426202 : term1115 = term1118.
Proof. exact (@lem2426191 (@lem2426201)). Qed.
Lemma lem2426204 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426205 : term555 = term556.
Proof. exact (@lem2426204 term193 term193). Qed.
Lemma lem2426206 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426207 : term558 = term193.
Proof. exact (EQ_MP (@lem2426206) (@lem940073)). Qed.
Lemma lem2426208 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426209 : term556 = term192.
Proof. exact (MK_COMB (@lem2426208) (@lem2426207)). Qed.
Lemma lem2426210 : term555 = term192.
Proof. exact (TRANS (@lem2426205) (@lem2426209)). Qed.
Lemma lem2426212 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426213 : term615 = term182.
Proof. exact (@lem2426212 term193). Qed.
Lemma lem2426214 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2426215 : term1119 = term1113.
Proof. exact (MK_COMB (@lem2426214) (@lem2426213)). Qed.
Lemma lem2426216 : term1118 = term604.
Proof. exact (MK_COMB (@lem2426215) (@lem2426210)). Qed.
Lemma lem2426218 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426219 : term604 = term605.
Proof. exact (@lem2426218 (NUMERAL 0) term193). Qed.
Lemma lem2426220 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426221 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426222 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426221 h1) (fun h1 : term605 = True => @lem2426220)). Qed.
Lemma lem2426223 : term605 = True.
Proof. exact (EQ_MP (@lem2426222) (@lem2426220)). Qed.
Lemma lem2426224 : term604 = True.
Proof. exact (TRANS (@lem2426219) (@lem2426223)). Qed.
Lemma lem2426225 : term1118 = True.
Proof. exact (TRANS (@lem2426216) (@lem2426224)). Qed.
Lemma lem2426226 : term1115 = True.
Proof. exact (TRANS (@lem2426202) (@lem2426225)). Qed.
Lemma lem2426227 : term604 = True.
Proof. exact (TRANS (@lem2426179) (@lem2426226)). Qed.
Lemma lem2426228 : term1112 = True.
Proof. exact (TRANS (@lem2426170) (@lem2426227)). Qed.
Lemma lem2426229 : True = term1112.
Proof. exact (SYM (@lem2426228)). Qed.
Lemma lem2426230 : term1112.
Proof. exact (EQ_MP (@lem2426229) (@lem0)). Qed.
Lemma lem2426231 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : term1194 y y' z z'.
Proof. exact (conj (@lem2426230) (@lem2426167 y y' z z' h1)). Qed.
Lemma lem2426233 (x : real) (y : real) : term1121 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2426234 (y : int) (y' : int) (z : int) (z' : int) : term1195 y y' z z'.
Proof. exact (@lem2426233 term192 (term781 y y' z z')). Qed.
Lemma lem2426235 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : term1196 y y' z z'.
Proof. exact (@lem2426234 y y' z z' (@lem2426231 y y' z z' h1)). Qed.
Lemma lem2426236 (y : int) (y' : int) (z : int) (z' : int) : (term1197 y y' z z') = (term781 y y' z z').
Proof. exact (@lem1982733 (term781 y y' z z')). Qed.
Lemma lem2426237 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2426238 (y : int) (y' : int) (z : int) (z' : int) : (term1198 y y' z z') = (term783 y y' z z').
Proof. exact (MK_COMB (@lem2426237) (@lem2426236 y y' z z')). Qed.
Lemma lem2426239 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2426240 (y : int) (y' : int) (z : int) (z' : int) : (term1196 y y' z z') = (term784 y y' z z').
Proof. exact (MK_COMB (@lem2426238 y y' z z') (@lem2426239)). Qed.
Lemma lem2426241 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : term784 y y' z z'.
Proof. exact (EQ_MP (@lem2426240 y y' z z') (@lem2426235 y y' z z' h1)). Qed.
Lemma lem2426243 (y : real) : term1126 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2426244 (y : int) (y' : int) (z : int) (z' : int) : term1171 y y' z z'.
Proof. exact (@lem2426243 (term713 y y' z z')). Qed.
Lemma lem2426245 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : term1172 y y' z z'.
Proof. exact (@lem2426244 y y' z z' (@lem2426166 y y' z z' h1)). Qed.
Lemma lem2426246 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : term1199 y y' z z'.
Proof. exact (@lem2426245 y y' z z' h1 term546). Qed.
Lemma lem2426247 (y : int) (y' : int) (z : int) (z' : int) : (term1199 y y' z z') = ((term1200 y y' z z') = term182).
Proof. exact (eq_refl (term1199 y y' z z')). Qed.
Lemma lem2426248 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : (term1200 y y' z z') = term182.
Proof. exact (EQ_MP (@lem2426247 y y' z z') (@lem2426246 y y' z z' h1)). Qed.
Lemma lem2426249 (y : int) (y' : int) (z : int) (z' : int) : (term1200 y y' z z') = (term1201 y y' z z').
Proof. exact (@lem1982781 (term177 y y') term546 (term712 y y' z z')). Qed.
Lemma lem2426250 (y : int) (y' : int) (z : int) (z' : int) : (term1202 y y' z z') = (term1203 y y' z z').
Proof. exact (@lem1982781 (term708 y z') term546 (term710 y' z z')). Qed.
Lemma lem2426251 (y' : int) (z : int) (z' : int) : (term1204 y' z z') = (term1205 y' z z').
Proof. exact (@lem1982781 (term708 z y') term546 (term177 z z')). Qed.
Lemma lem2426252 (z : int) (z' : int) : (term708 z z') = (term708 z z').
Proof. exact (eq_refl (term708 z z')). Qed.
Lemma lem2426253 (z : int) (y' : int) : (term760 z y') = (term734 z y').
Proof. exact (@lem1982749 term546 term546 (term177 z y')). Qed.
Lemma lem2426255 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2426256 : term546 = term547.
Proof. exact (@lem2426255 term193). Qed.
Lemma lem2426258 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2426259 : term546 = term547.
Proof. exact (@lem2426258 term193). Qed.
Lemma lem2426260 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426261 : term548 = term549.
Proof. exact (MK_COMB (@lem2426260) (@lem2426259)). Qed.
Lemma lem2426262 : term643 = term644.
Proof. exact (MK_COMB (@lem2426261) (@lem2426256)). Qed.
Lemma lem2426263 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2426265 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426266 : term555 = term556.
Proof. exact (@lem2426265 term193 term193). Qed.
Lemma lem2426267 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426268 : term558 = term193.
Proof. exact (EQ_MP (@lem2426267) (@lem940073)). Qed.
Lemma lem2426269 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426270 : term556 = term192.
Proof. exact (MK_COMB (@lem2426269) (@lem2426268)). Qed.
Lemma lem2426271 : term555 = term192.
Proof. exact (TRANS (@lem2426266) (@lem2426270)). Qed.
Lemma lem2426273 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2426274 : term643 = term556.
Proof. exact (@lem2426273 term193 term193). Qed.
Lemma lem2426275 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426276 : term558 = term193.
Proof. exact (EQ_MP (@lem2426275) (@lem940073)). Qed.
Lemma lem2426277 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426278 : term556 = term192.
Proof. exact (MK_COMB (@lem2426277) (@lem2426276)). Qed.
Lemma lem2426279 : term643 = term192.
Proof. exact (TRANS (@lem2426274) (@lem2426278)). Qed.
Lemma lem2426280 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2426281 : term647 = term648.
Proof. exact (MK_COMB (@lem2426280) (@lem2426279)). Qed.
Lemma lem2426282 : term645 = term567.
Proof. exact (MK_COMB (@lem2426281) (@lem2426271)). Qed.
Lemma lem2426283 : term644 = term567.
Proof. exact (TRANS (@lem2426263) (@lem2426282)). Qed.
Lemma lem2426284 : term643 = term567.
Proof. exact (TRANS (@lem2426262) (@lem2426283)). Qed.
Lemma lem2426286 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2426287 : term567 = term192.
Proof. exact (@lem2426286 term192). Qed.
Lemma lem2426288 : term643 = term192.
Proof. exact (TRANS (@lem2426284) (@lem2426287)). Qed.
Lemma lem2426289 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426290 : term649 = term650.
Proof. exact (MK_COMB (@lem2426289) (@lem2426288)). Qed.
Lemma lem2426291 (z : int) (y' : int) : (term177 z y') = (term177 z y').
Proof. exact (eq_refl (term177 z y')). Qed.
Lemma lem2426292 (z : int) (y' : int) : (term734 z y') = (term735 z y').
Proof. exact (MK_COMB (@lem2426290) (@lem2426291 z y')). Qed.
Lemma lem2426293 (z : int) (y' : int) : (term760 z y') = (term735 z y').
Proof. exact (TRANS (@lem2426253 z y') (@lem2426292 z y')). Qed.
Lemma lem2426294 (z : int) (y' : int) : (term735 z y') = (term177 z y').
Proof. exact (@lem1982709 (term177 z y')). Qed.
Lemma lem2426295 (z : int) (y' : int) : (term760 z y') = (term177 z y').
Proof. exact (TRANS (@lem2426293 z y') (@lem2426294 z y')). Qed.
Lemma lem2426296 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426297 (z : int) (y' : int) : (term761 z y') = (term283 z y').
Proof. exact (MK_COMB (@lem2426296) (@lem2426295 z y')). Qed.
Lemma lem2426298 (y' : int) (z : int) (z' : int) : (term1205 y' z z') = (term709 y' z z').
Proof. exact (MK_COMB (@lem2426297 z y') (@lem2426252 z z')). Qed.
Lemma lem2426299 (y' : int) (z : int) (z' : int) : (term1204 y' z z') = (term709 y' z z').
Proof. exact (TRANS (@lem2426251 y' z z') (@lem2426298 y' z z')). Qed.
Lemma lem2426300 (y : int) (z' : int) : (term760 y z') = (term734 y z').
Proof. exact (@lem1982749 term546 term546 (term177 y z')). Qed.
Lemma lem2426302 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2426303 : term546 = term547.
Proof. exact (@lem2426302 term193). Qed.
Lemma lem2426305 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2426306 : term546 = term547.
Proof. exact (@lem2426305 term193). Qed.
Lemma lem2426307 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426308 : term548 = term549.
Proof. exact (MK_COMB (@lem2426307) (@lem2426306)). Qed.
Lemma lem2426309 : term643 = term644.
Proof. exact (MK_COMB (@lem2426308) (@lem2426303)). Qed.
Lemma lem2426310 : term644 = term645.
Proof. exact (@lem1981613 term546 term546 term192 term192). Qed.
Lemma lem2426312 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426313 : term555 = term556.
Proof. exact (@lem2426312 term193 term193). Qed.
Lemma lem2426314 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426315 : term558 = term193.
Proof. exact (EQ_MP (@lem2426314) (@lem940073)). Qed.
Lemma lem2426316 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426317 : term556 = term192.
Proof. exact (MK_COMB (@lem2426316) (@lem2426315)). Qed.
Lemma lem2426318 : term555 = term192.
Proof. exact (TRANS (@lem2426313) (@lem2426317)). Qed.
Lemma lem2426320 (m : nat) (n : nat) : (term646 m n) = (term554 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2426321 : term643 = term556.
Proof. exact (@lem2426320 term193 term193). Qed.
Lemma lem2426322 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426323 : term558 = term193.
Proof. exact (EQ_MP (@lem2426322) (@lem940073)). Qed.
Lemma lem2426324 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426325 : term556 = term192.
Proof. exact (MK_COMB (@lem2426324) (@lem2426323)). Qed.
Lemma lem2426326 : term643 = term192.
Proof. exact (TRANS (@lem2426321) (@lem2426325)). Qed.
Lemma lem2426327 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2426328 : term647 = term648.
Proof. exact (MK_COMB (@lem2426327) (@lem2426326)). Qed.
Lemma lem2426329 : term645 = term567.
Proof. exact (MK_COMB (@lem2426328) (@lem2426318)). Qed.
Lemma lem2426330 : term644 = term567.
Proof. exact (TRANS (@lem2426310) (@lem2426329)). Qed.
Lemma lem2426331 : term643 = term567.
Proof. exact (TRANS (@lem2426309) (@lem2426330)). Qed.
Lemma lem2426333 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2426334 : term567 = term192.
Proof. exact (@lem2426333 term192). Qed.
Lemma lem2426335 : term643 = term192.
Proof. exact (TRANS (@lem2426331) (@lem2426334)). Qed.
Lemma lem2426336 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426337 : term649 = term650.
Proof. exact (MK_COMB (@lem2426336) (@lem2426335)). Qed.
Lemma lem2426338 (y : int) (z' : int) : (term177 y z') = (term177 y z').
Proof. exact (eq_refl (term177 y z')). Qed.
Lemma lem2426339 (y : int) (z' : int) : (term734 y z') = (term735 y z').
Proof. exact (MK_COMB (@lem2426337) (@lem2426338 y z')). Qed.
Lemma lem2426340 (y : int) (z' : int) : (term760 y z') = (term735 y z').
Proof. exact (TRANS (@lem2426300 y z') (@lem2426339 y z')). Qed.
Lemma lem2426341 (y : int) (z' : int) : (term735 y z') = (term177 y z').
Proof. exact (@lem1982709 (term177 y z')). Qed.
Lemma lem2426342 (y : int) (z' : int) : (term760 y z') = (term177 y z').
Proof. exact (TRANS (@lem2426340 y z') (@lem2426341 y z')). Qed.
Lemma lem2426343 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426344 (y : int) (z' : int) : (term761 y z') = (term283 y z').
Proof. exact (MK_COMB (@lem2426343) (@lem2426342 y z')). Qed.
Lemma lem2426345 (y : int) (y' : int) (z : int) (z' : int) : (term1203 y y' z z') = (term1206 y y' z z').
Proof. exact (MK_COMB (@lem2426344 y z') (@lem2426299 y' z z')). Qed.
Lemma lem2426346 (y : int) (y' : int) (z : int) (z' : int) : (term1202 y y' z z') = (term1206 y y' z z').
Proof. exact (TRANS (@lem2426250 y y' z z') (@lem2426345 y y' z z')). Qed.
Lemma lem2426349 (y : int) (y' : int) : (term711 y y') = (term711 y y').
Proof. exact (eq_refl (term711 y y')). Qed.
Lemma lem2426350 (y : int) (y' : int) (z : int) (z' : int) : (term1201 y y' z z') = (term1207 y y' z z').
Proof. exact (MK_COMB (@lem2426349 y y') (@lem2426346 y y' z z')). Qed.
Lemma lem2426351 (y : int) (y' : int) (z : int) (z' : int) : (term1200 y y' z z') = (term1207 y y' z z').
Proof. exact (TRANS (@lem2426249 y y' z z') (@lem2426350 y y' z z')). Qed.
Lemma lem2426352 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2426353 (y : int) (y' : int) (z : int) (z' : int) : (term1208 y y' z z') = (term1209 y y' z z').
Proof. exact (MK_COMB (@lem2426352) (@lem2426351 y y' z z')). Qed.
Lemma lem2426354 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2426355 (y : int) (y' : int) (z : int) (z' : int) : ((term1200 y y' z z') = term182) = ((term1207 y y' z z') = term182).
Proof. exact (MK_COMB (@lem2426353 y y' z z') (@lem2426354)). Qed.
Lemma lem2426356 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : (term1207 y y' z z') = term182.
Proof. exact (EQ_MP (@lem2426355 y y' z z') (@lem2426248 y y' z z' h1)). Qed.
Lemma lem2426357 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : term1210 y y' z z'.
Proof. exact (conj (@lem2426356 y y' z z' h1) (@lem2426241 y y' z z' h1)). Qed.
Lemma lem2426359 (x : real) (y : real) : term1132 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2426360 (y : int) (y' : int) (z : int) (z' : int) : term1211 y y' z z'.
Proof. exact (@lem2426359 (term1207 y y' z z') (term781 y y' z z')). Qed.
Lemma lem2426361 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : term1212 y y' z z'.
Proof. exact (@lem2426360 y y' z z' (@lem2426357 y y' z z' h1)). Qed.
Lemma lem2426362 (y : int) (y' : int) (z : int) (z' : int) : (term1213 y y' z z') = (term1214 y y' z z').
Proof. exact (@lem1982753 (term708 y y') (term177 y y') (term1206 y y' z z') (term780 y y' z z')). Qed.
Lemma lem2426363 (y : int) (y' : int) : (term1186 y y') = (term1181 y y').
Proof. exact (@lem1982713 term546 (term177 y y')). Qed.
Lemma lem2426365 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2426366 : term192 = term567.
Proof. exact (@lem2426365 term193). Qed.
Lemma lem2426368 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2426369 : term546 = term547.
Proof. exact (@lem2426368 term193). Qed.
Lemma lem2426370 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426371 : term598 = term599.
Proof. exact (MK_COMB (@lem2426370) (@lem2426369)). Qed.
Lemma lem2426372 : term600 = term601.
Proof. exact (MK_COMB (@lem2426371) (@lem2426366)). Qed.
Lemma lem2426373 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2426375 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426376 : term604 = term605.
Proof. exact (@lem2426375 (NUMERAL 0) term193). Qed.
Lemma lem2426377 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426378 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426379 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426378 h1) (fun h1 : term605 = True => @lem2426377)). Qed.
Lemma lem2426380 : term605 = True.
Proof. exact (EQ_MP (@lem2426379) (@lem2426377)). Qed.
Lemma lem2426381 : term604 = True.
Proof. exact (TRANS (@lem2426376) (@lem2426380)). Qed.
Lemma lem2426382 : True = term604.
Proof. exact (SYM (@lem2426381)). Qed.
Lemma lem2426383 : term604.
Proof. exact (EQ_MP (@lem2426382) (@lem0)). Qed.
Lemma lem2426384 : term607.
Proof. exact (@lem2426373 (@lem2426383)). Qed.
Lemma lem2426386 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426387 : term604 = term605.
Proof. exact (@lem2426386 (NUMERAL 0) term193). Qed.
Lemma lem2426388 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426389 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426390 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426389 h1) (fun h1 : term605 = True => @lem2426388)). Qed.
Lemma lem2426391 : term605 = True.
Proof. exact (EQ_MP (@lem2426390) (@lem2426388)). Qed.
Lemma lem2426392 : term604 = True.
Proof. exact (TRANS (@lem2426387) (@lem2426391)). Qed.
Lemma lem2426393 : True = term604.
Proof. exact (SYM (@lem2426392)). Qed.
Lemma lem2426394 : term604.
Proof. exact (EQ_MP (@lem2426393) (@lem0)). Qed.
Lemma lem2426395 : term608.
Proof. exact (@lem2426384 (@lem2426394)). Qed.
Lemma lem2426397 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426398 : term604 = term605.
Proof. exact (@lem2426397 (NUMERAL 0) term193). Qed.
Lemma lem2426399 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426400 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426401 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426400 h1) (fun h1 : term605 = True => @lem2426399)). Qed.
Lemma lem2426402 : term605 = True.
Proof. exact (EQ_MP (@lem2426401) (@lem2426399)). Qed.
Lemma lem2426403 : term604 = True.
Proof. exact (TRANS (@lem2426398) (@lem2426402)). Qed.
Lemma lem2426404 : True = term604.
Proof. exact (SYM (@lem2426403)). Qed.
Lemma lem2426405 : term604.
Proof. exact (EQ_MP (@lem2426404) (@lem0)). Qed.
Lemma lem2426406 : term609.
Proof. exact (@lem2426395 (@lem2426405)). Qed.
Lemma lem2426408 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426409 : term555 = term556.
Proof. exact (@lem2426408 term193 term193). Qed.
Lemma lem2426410 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426411 : term558 = term193.
Proof. exact (EQ_MP (@lem2426410) (@lem940073)). Qed.
Lemma lem2426412 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426413 : term556 = term192.
Proof. exact (MK_COMB (@lem2426412) (@lem2426411)). Qed.
Lemma lem2426414 : term555 = term192.
Proof. exact (TRANS (@lem2426409) (@lem2426413)). Qed.
Lemma lem2426416 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2426417 : term568 = term573.
Proof. exact (@lem2426416 term193 term193). Qed.
Lemma lem2426418 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426419 : term558 = term193.
Proof. exact (EQ_MP (@lem2426418) (@lem940073)). Qed.
Lemma lem2426420 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426421 : term556 = term192.
Proof. exact (MK_COMB (@lem2426420) (@lem2426419)). Qed.
Lemma lem2426422 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2426423 : term573 = term546.
Proof. exact (MK_COMB (@lem2426422) (@lem2426421)). Qed.
Lemma lem2426424 : term568 = term546.
Proof. exact (TRANS (@lem2426417) (@lem2426423)). Qed.
Lemma lem2426425 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426426 : term610 = term598.
Proof. exact (MK_COMB (@lem2426425) (@lem2426424)). Qed.
Lemma lem2426427 : term611 = term600.
Proof. exact (MK_COMB (@lem2426426) (@lem2426414)). Qed.
Lemma lem2426429 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2426430 : term600 = term182.
Proof. exact (@lem2426429 term193). Qed.
Lemma lem2426431 : term611 = term182.
Proof. exact (TRANS (@lem2426427) (@lem2426430)). Qed.
Lemma lem2426432 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426433 : term613 = term184.
Proof. exact (MK_COMB (@lem2426432) (@lem2426431)). Qed.
Lemma lem2426434 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2426435 : term614 = term615.
Proof. exact (MK_COMB (@lem2426433) (@lem2426434)). Qed.
Lemma lem2426437 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426438 : term615 = term182.
Proof. exact (@lem2426437 term193). Qed.
Lemma lem2426439 : term614 = term182.
Proof. exact (TRANS (@lem2426435) (@lem2426438)). Qed.
Lemma lem2426441 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426442 : term555 = term556.
Proof. exact (@lem2426441 term193 term193). Qed.
Lemma lem2426443 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426444 : term558 = term193.
Proof. exact (EQ_MP (@lem2426443) (@lem940073)). Qed.
Lemma lem2426445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426446 : term556 = term192.
Proof. exact (MK_COMB (@lem2426445) (@lem2426444)). Qed.
Lemma lem2426447 : term555 = term192.
Proof. exact (TRANS (@lem2426442) (@lem2426446)). Qed.
Lemma lem2426448 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2426449 : term617 = term615.
Proof. exact (MK_COMB (@lem2426448) (@lem2426447)). Qed.
Lemma lem2426451 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426452 : term615 = term182.
Proof. exact (@lem2426451 term193). Qed.
Lemma lem2426453 : term617 = term182.
Proof. exact (TRANS (@lem2426449) (@lem2426452)). Qed.
Lemma lem2426454 : term182 = term617.
Proof. exact (SYM (@lem2426453)). Qed.
Lemma lem2426455 : term614 = term617.
Proof. exact (TRANS (@lem2426439) (@lem2426454)). Qed.
Lemma lem2426456 : term601 = term543.
Proof. exact (@lem2426406 (@lem2426455)). Qed.
Lemma lem2426457 : term600 = term543.
Proof. exact (TRANS (@lem2426372) (@lem2426456)). Qed.
Lemma lem2426459 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2426460 : term543 = term182.
Proof. exact (@lem2426459 term182). Qed.
Lemma lem2426461 : term600 = term182.
Proof. exact (TRANS (@lem2426457) (@lem2426460)). Qed.
Lemma lem2426462 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426463 : term618 = term184.
Proof. exact (MK_COMB (@lem2426462) (@lem2426461)). Qed.
Lemma lem2426464 (y : int) (y' : int) : (term177 y y') = (term177 y y').
Proof. exact (eq_refl (term177 y y')). Qed.
Lemma lem2426465 (y : int) (y' : int) : (term1181 y y') = (term1182 y y').
Proof. exact (MK_COMB (@lem2426463) (@lem2426464 y y')). Qed.
Lemma lem2426466 (y : int) (y' : int) : (term1186 y y') = (term1182 y y').
Proof. exact (TRANS (@lem2426363 y y') (@lem2426465 y y')). Qed.
Lemma lem2426467 (y : int) (y' : int) : (term1182 y y') = term182.
Proof. exact (@lem1982719 (term177 y y')). Qed.
Lemma lem2426468 (y : int) (y' : int) : (term1186 y y') = term182.
Proof. exact (TRANS (@lem2426466 y y') (@lem2426467 y y')). Qed.
Lemma lem2426469 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426470 (y : int) (y' : int) : (term1187 y y') = term206.
Proof. exact (MK_COMB (@lem2426469) (@lem2426468 y y')). Qed.
Lemma lem2426471 (y : int) (y' : int) (z : int) (z' : int) : (term1215 y y' z z') = (term1216 y y' z z').
Proof. exact (@lem1982753 (term177 y z') (term708 y z') (term709 y' z z') (term779 y' z z')). Qed.
Lemma lem2426472 (y : int) (z' : int) : (term1180 y z') = (term1181 y z').
Proof. exact (@lem1982715 term546 (term177 y z')). Qed.
Lemma lem2426474 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2426475 : term192 = term567.
Proof. exact (@lem2426474 term193). Qed.
Lemma lem2426477 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2426478 : term546 = term547.
Proof. exact (@lem2426477 term193). Qed.
Lemma lem2426479 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426480 : term598 = term599.
Proof. exact (MK_COMB (@lem2426479) (@lem2426478)). Qed.
Lemma lem2426481 : term600 = term601.
Proof. exact (MK_COMB (@lem2426480) (@lem2426475)). Qed.
Lemma lem2426482 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2426484 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426485 : term604 = term605.
Proof. exact (@lem2426484 (NUMERAL 0) term193). Qed.
Lemma lem2426486 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426487 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426488 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426487 h1) (fun h1 : term605 = True => @lem2426486)). Qed.
Lemma lem2426489 : term605 = True.
Proof. exact (EQ_MP (@lem2426488) (@lem2426486)). Qed.
Lemma lem2426490 : term604 = True.
Proof. exact (TRANS (@lem2426485) (@lem2426489)). Qed.
Lemma lem2426491 : True = term604.
Proof. exact (SYM (@lem2426490)). Qed.
Lemma lem2426492 : term604.
Proof. exact (EQ_MP (@lem2426491) (@lem0)). Qed.
Lemma lem2426493 : term607.
Proof. exact (@lem2426482 (@lem2426492)). Qed.
Lemma lem2426495 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426496 : term604 = term605.
Proof. exact (@lem2426495 (NUMERAL 0) term193). Qed.
Lemma lem2426497 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426498 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426499 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426498 h1) (fun h1 : term605 = True => @lem2426497)). Qed.
Lemma lem2426500 : term605 = True.
Proof. exact (EQ_MP (@lem2426499) (@lem2426497)). Qed.
Lemma lem2426501 : term604 = True.
Proof. exact (TRANS (@lem2426496) (@lem2426500)). Qed.
Lemma lem2426502 : True = term604.
Proof. exact (SYM (@lem2426501)). Qed.
Lemma lem2426503 : term604.
Proof. exact (EQ_MP (@lem2426502) (@lem0)). Qed.
Lemma lem2426504 : term608.
Proof. exact (@lem2426493 (@lem2426503)). Qed.
Lemma lem2426506 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426507 : term604 = term605.
Proof. exact (@lem2426506 (NUMERAL 0) term193). Qed.
Lemma lem2426508 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426509 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426510 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426509 h1) (fun h1 : term605 = True => @lem2426508)). Qed.
Lemma lem2426511 : term605 = True.
Proof. exact (EQ_MP (@lem2426510) (@lem2426508)). Qed.
Lemma lem2426512 : term604 = True.
Proof. exact (TRANS (@lem2426507) (@lem2426511)). Qed.
Lemma lem2426513 : True = term604.
Proof. exact (SYM (@lem2426512)). Qed.
Lemma lem2426514 : term604.
Proof. exact (EQ_MP (@lem2426513) (@lem0)). Qed.
Lemma lem2426515 : term609.
Proof. exact (@lem2426504 (@lem2426514)). Qed.
Lemma lem2426517 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426518 : term555 = term556.
Proof. exact (@lem2426517 term193 term193). Qed.
Lemma lem2426519 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426520 : term558 = term193.
Proof. exact (EQ_MP (@lem2426519) (@lem940073)). Qed.
Lemma lem2426521 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426522 : term556 = term192.
Proof. exact (MK_COMB (@lem2426521) (@lem2426520)). Qed.
Lemma lem2426523 : term555 = term192.
Proof. exact (TRANS (@lem2426518) (@lem2426522)). Qed.
Lemma lem2426525 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2426526 : term568 = term573.
Proof. exact (@lem2426525 term193 term193). Qed.
Lemma lem2426527 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426528 : term558 = term193.
Proof. exact (EQ_MP (@lem2426527) (@lem940073)). Qed.
Lemma lem2426529 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426530 : term556 = term192.
Proof. exact (MK_COMB (@lem2426529) (@lem2426528)). Qed.
Lemma lem2426531 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2426532 : term573 = term546.
Proof. exact (MK_COMB (@lem2426531) (@lem2426530)). Qed.
Lemma lem2426533 : term568 = term546.
Proof. exact (TRANS (@lem2426526) (@lem2426532)). Qed.
Lemma lem2426534 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426535 : term610 = term598.
Proof. exact (MK_COMB (@lem2426534) (@lem2426533)). Qed.
Lemma lem2426536 : term611 = term600.
Proof. exact (MK_COMB (@lem2426535) (@lem2426523)). Qed.
Lemma lem2426538 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2426539 : term600 = term182.
Proof. exact (@lem2426538 term193). Qed.
Lemma lem2426540 : term611 = term182.
Proof. exact (TRANS (@lem2426536) (@lem2426539)). Qed.
Lemma lem2426541 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426542 : term613 = term184.
Proof. exact (MK_COMB (@lem2426541) (@lem2426540)). Qed.
Lemma lem2426543 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2426544 : term614 = term615.
Proof. exact (MK_COMB (@lem2426542) (@lem2426543)). Qed.
Lemma lem2426546 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426547 : term615 = term182.
Proof. exact (@lem2426546 term193). Qed.
Lemma lem2426548 : term614 = term182.
Proof. exact (TRANS (@lem2426544) (@lem2426547)). Qed.
Lemma lem2426550 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426551 : term555 = term556.
Proof. exact (@lem2426550 term193 term193). Qed.
Lemma lem2426552 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426553 : term558 = term193.
Proof. exact (EQ_MP (@lem2426552) (@lem940073)). Qed.
Lemma lem2426554 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426555 : term556 = term192.
Proof. exact (MK_COMB (@lem2426554) (@lem2426553)). Qed.
Lemma lem2426556 : term555 = term192.
Proof. exact (TRANS (@lem2426551) (@lem2426555)). Qed.
Lemma lem2426557 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2426558 : term617 = term615.
Proof. exact (MK_COMB (@lem2426557) (@lem2426556)). Qed.
Lemma lem2426560 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426561 : term615 = term182.
Proof. exact (@lem2426560 term193). Qed.
Lemma lem2426562 : term617 = term182.
Proof. exact (TRANS (@lem2426558) (@lem2426561)). Qed.
Lemma lem2426563 : term182 = term617.
Proof. exact (SYM (@lem2426562)). Qed.
Lemma lem2426564 : term614 = term617.
Proof. exact (TRANS (@lem2426548) (@lem2426563)). Qed.
Lemma lem2426565 : term601 = term543.
Proof. exact (@lem2426515 (@lem2426564)). Qed.
Lemma lem2426566 : term600 = term543.
Proof. exact (TRANS (@lem2426481) (@lem2426565)). Qed.
Lemma lem2426568 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2426569 : term543 = term182.
Proof. exact (@lem2426568 term182). Qed.
Lemma lem2426570 : term600 = term182.
Proof. exact (TRANS (@lem2426566) (@lem2426569)). Qed.
Lemma lem2426571 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426572 : term618 = term184.
Proof. exact (MK_COMB (@lem2426571) (@lem2426570)). Qed.
Lemma lem2426573 (y : int) (z' : int) : (term177 y z') = (term177 y z').
Proof. exact (eq_refl (term177 y z')). Qed.
Lemma lem2426574 (y : int) (z' : int) : (term1181 y z') = (term1182 y z').
Proof. exact (MK_COMB (@lem2426572) (@lem2426573 y z')). Qed.
Lemma lem2426575 (y : int) (z' : int) : (term1180 y z') = (term1182 y z').
Proof. exact (TRANS (@lem2426472 y z') (@lem2426574 y z')). Qed.
Lemma lem2426576 (y : int) (z' : int) : (term1182 y z') = term182.
Proof. exact (@lem1982719 (term177 y z')). Qed.
Lemma lem2426577 (y : int) (z' : int) : (term1180 y z') = term182.
Proof. exact (TRANS (@lem2426575 y z') (@lem2426576 y z')). Qed.
Lemma lem2426578 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426579 (y : int) (z' : int) : (term1183 y z') = term206.
Proof. exact (MK_COMB (@lem2426578) (@lem2426577 y z')). Qed.
Lemma lem2426580 (y' : int) (z : int) (z' : int) : (term1217 y' z z') = (term1218 y' z z').
Proof. exact (@lem1982753 (term177 z y') (term708 z y') (term708 z z') (term1219 z z')). Qed.
Lemma lem2426581 (z : int) (y' : int) : (term1180 z y') = (term1181 z y').
Proof. exact (@lem1982715 term546 (term177 z y')). Qed.
Lemma lem2426583 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2426584 : term192 = term567.
Proof. exact (@lem2426583 term193). Qed.
Lemma lem2426586 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2426587 : term546 = term547.
Proof. exact (@lem2426586 term193). Qed.
Lemma lem2426588 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426589 : term598 = term599.
Proof. exact (MK_COMB (@lem2426588) (@lem2426587)). Qed.
Lemma lem2426590 : term600 = term601.
Proof. exact (MK_COMB (@lem2426589) (@lem2426584)). Qed.
Lemma lem2426591 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2426593 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426594 : term604 = term605.
Proof. exact (@lem2426593 (NUMERAL 0) term193). Qed.
Lemma lem2426595 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426596 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426597 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426596 h1) (fun h1 : term605 = True => @lem2426595)). Qed.
Lemma lem2426598 : term605 = True.
Proof. exact (EQ_MP (@lem2426597) (@lem2426595)). Qed.
Lemma lem2426599 : term604 = True.
Proof. exact (TRANS (@lem2426594) (@lem2426598)). Qed.
Lemma lem2426600 : True = term604.
Proof. exact (SYM (@lem2426599)). Qed.
Lemma lem2426601 : term604.
Proof. exact (EQ_MP (@lem2426600) (@lem0)). Qed.
Lemma lem2426602 : term607.
Proof. exact (@lem2426591 (@lem2426601)). Qed.
Lemma lem2426604 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426605 : term604 = term605.
Proof. exact (@lem2426604 (NUMERAL 0) term193). Qed.
Lemma lem2426606 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426607 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426608 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426607 h1) (fun h1 : term605 = True => @lem2426606)). Qed.
Lemma lem2426609 : term605 = True.
Proof. exact (EQ_MP (@lem2426608) (@lem2426606)). Qed.
Lemma lem2426610 : term604 = True.
Proof. exact (TRANS (@lem2426605) (@lem2426609)). Qed.
Lemma lem2426611 : True = term604.
Proof. exact (SYM (@lem2426610)). Qed.
Lemma lem2426612 : term604.
Proof. exact (EQ_MP (@lem2426611) (@lem0)). Qed.
Lemma lem2426613 : term608.
Proof. exact (@lem2426602 (@lem2426612)). Qed.
Lemma lem2426615 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426616 : term604 = term605.
Proof. exact (@lem2426615 (NUMERAL 0) term193). Qed.
Lemma lem2426617 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426618 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426619 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426618 h1) (fun h1 : term605 = True => @lem2426617)). Qed.
Lemma lem2426620 : term605 = True.
Proof. exact (EQ_MP (@lem2426619) (@lem2426617)). Qed.
Lemma lem2426621 : term604 = True.
Proof. exact (TRANS (@lem2426616) (@lem2426620)). Qed.
Lemma lem2426622 : True = term604.
Proof. exact (SYM (@lem2426621)). Qed.
Lemma lem2426623 : term604.
Proof. exact (EQ_MP (@lem2426622) (@lem0)). Qed.
Lemma lem2426624 : term609.
Proof. exact (@lem2426613 (@lem2426623)). Qed.
Lemma lem2426626 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426627 : term555 = term556.
Proof. exact (@lem2426626 term193 term193). Qed.
Lemma lem2426628 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426629 : term558 = term193.
Proof. exact (EQ_MP (@lem2426628) (@lem940073)). Qed.
Lemma lem2426630 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426631 : term556 = term192.
Proof. exact (MK_COMB (@lem2426630) (@lem2426629)). Qed.
Lemma lem2426632 : term555 = term192.
Proof. exact (TRANS (@lem2426627) (@lem2426631)). Qed.
Lemma lem2426634 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2426635 : term568 = term573.
Proof. exact (@lem2426634 term193 term193). Qed.
Lemma lem2426636 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426637 : term558 = term193.
Proof. exact (EQ_MP (@lem2426636) (@lem940073)). Qed.
Lemma lem2426638 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426639 : term556 = term192.
Proof. exact (MK_COMB (@lem2426638) (@lem2426637)). Qed.
Lemma lem2426640 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2426641 : term573 = term546.
Proof. exact (MK_COMB (@lem2426640) (@lem2426639)). Qed.
Lemma lem2426642 : term568 = term546.
Proof. exact (TRANS (@lem2426635) (@lem2426641)). Qed.
Lemma lem2426643 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426644 : term610 = term598.
Proof. exact (MK_COMB (@lem2426643) (@lem2426642)). Qed.
Lemma lem2426645 : term611 = term600.
Proof. exact (MK_COMB (@lem2426644) (@lem2426632)). Qed.
Lemma lem2426647 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2426648 : term600 = term182.
Proof. exact (@lem2426647 term193). Qed.
Lemma lem2426649 : term611 = term182.
Proof. exact (TRANS (@lem2426645) (@lem2426648)). Qed.
Lemma lem2426650 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426651 : term613 = term184.
Proof. exact (MK_COMB (@lem2426650) (@lem2426649)). Qed.
Lemma lem2426652 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2426653 : term614 = term615.
Proof. exact (MK_COMB (@lem2426651) (@lem2426652)). Qed.
Lemma lem2426655 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426656 : term615 = term182.
Proof. exact (@lem2426655 term193). Qed.
Lemma lem2426657 : term614 = term182.
Proof. exact (TRANS (@lem2426653) (@lem2426656)). Qed.
Lemma lem2426659 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426660 : term555 = term556.
Proof. exact (@lem2426659 term193 term193). Qed.
Lemma lem2426661 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426662 : term558 = term193.
Proof. exact (EQ_MP (@lem2426661) (@lem940073)). Qed.
Lemma lem2426663 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426664 : term556 = term192.
Proof. exact (MK_COMB (@lem2426663) (@lem2426662)). Qed.
Lemma lem2426665 : term555 = term192.
Proof. exact (TRANS (@lem2426660) (@lem2426664)). Qed.
Lemma lem2426666 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2426667 : term617 = term615.
Proof. exact (MK_COMB (@lem2426666) (@lem2426665)). Qed.
Lemma lem2426669 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426670 : term615 = term182.
Proof. exact (@lem2426669 term193). Qed.
Lemma lem2426671 : term617 = term182.
Proof. exact (TRANS (@lem2426667) (@lem2426670)). Qed.
Lemma lem2426672 : term182 = term617.
Proof. exact (SYM (@lem2426671)). Qed.
Lemma lem2426673 : term614 = term617.
Proof. exact (TRANS (@lem2426657) (@lem2426672)). Qed.
Lemma lem2426674 : term601 = term543.
Proof. exact (@lem2426624 (@lem2426673)). Qed.
Lemma lem2426675 : term600 = term543.
Proof. exact (TRANS (@lem2426590) (@lem2426674)). Qed.
Lemma lem2426677 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2426678 : term543 = term182.
Proof. exact (@lem2426677 term182). Qed.
Lemma lem2426679 : term600 = term182.
Proof. exact (TRANS (@lem2426675) (@lem2426678)). Qed.
Lemma lem2426680 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426681 : term618 = term184.
Proof. exact (MK_COMB (@lem2426680) (@lem2426679)). Qed.
Lemma lem2426682 (z : int) (y' : int) : (term177 z y') = (term177 z y').
Proof. exact (eq_refl (term177 z y')). Qed.
Lemma lem2426683 (z : int) (y' : int) : (term1181 z y') = (term1182 z y').
Proof. exact (MK_COMB (@lem2426681) (@lem2426682 z y')). Qed.
Lemma lem2426684 (z : int) (y' : int) : (term1180 z y') = (term1182 z y').
Proof. exact (TRANS (@lem2426581 z y') (@lem2426683 z y')). Qed.
Lemma lem2426685 (z : int) (y' : int) : (term1182 z y') = term182.
Proof. exact (@lem1982719 (term177 z y')). Qed.
Lemma lem2426686 (z : int) (y' : int) : (term1180 z y') = term182.
Proof. exact (TRANS (@lem2426684 z y') (@lem2426685 z y')). Qed.
Lemma lem2426687 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426688 (z : int) (y' : int) : (term1183 z y') = term206.
Proof. exact (MK_COMB (@lem2426687) (@lem2426686 z y')). Qed.
Lemma lem2426689 (z : int) (z' : int) : (term1220 z z') = (term1221 z z').
Proof. exact (@lem1982763 (term708 z z') (term177 z z') term546). Qed.
Lemma lem2426690 (z : int) (z' : int) : (term1186 z z') = (term1181 z z').
Proof. exact (@lem1982713 term546 (term177 z z')). Qed.
Lemma lem2426692 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2426693 : term192 = term567.
Proof. exact (@lem2426692 term193). Qed.
Lemma lem2426695 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2426696 : term546 = term547.
Proof. exact (@lem2426695 term193). Qed.
Lemma lem2426697 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426698 : term598 = term599.
Proof. exact (MK_COMB (@lem2426697) (@lem2426696)). Qed.
Lemma lem2426699 : term600 = term601.
Proof. exact (MK_COMB (@lem2426698) (@lem2426693)). Qed.
Lemma lem2426700 : term602.
Proof. exact (@lem1981473 term546 term192 term192 term192 term182 term192). Qed.
Lemma lem2426702 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426703 : term604 = term605.
Proof. exact (@lem2426702 (NUMERAL 0) term193). Qed.
Lemma lem2426704 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426705 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426706 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426705 h1) (fun h1 : term605 = True => @lem2426704)). Qed.
Lemma lem2426707 : term605 = True.
Proof. exact (EQ_MP (@lem2426706) (@lem2426704)). Qed.
Lemma lem2426708 : term604 = True.
Proof. exact (TRANS (@lem2426703) (@lem2426707)). Qed.
Lemma lem2426709 : True = term604.
Proof. exact (SYM (@lem2426708)). Qed.
Lemma lem2426710 : term604.
Proof. exact (EQ_MP (@lem2426709) (@lem0)). Qed.
Lemma lem2426711 : term607.
Proof. exact (@lem2426700 (@lem2426710)). Qed.
Lemma lem2426713 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426714 : term604 = term605.
Proof. exact (@lem2426713 (NUMERAL 0) term193). Qed.
Lemma lem2426715 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426716 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426717 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426716 h1) (fun h1 : term605 = True => @lem2426715)). Qed.
Lemma lem2426718 : term605 = True.
Proof. exact (EQ_MP (@lem2426717) (@lem2426715)). Qed.
Lemma lem2426719 : term604 = True.
Proof. exact (TRANS (@lem2426714) (@lem2426718)). Qed.
Lemma lem2426720 : True = term604.
Proof. exact (SYM (@lem2426719)). Qed.
Lemma lem2426721 : term604.
Proof. exact (EQ_MP (@lem2426720) (@lem0)). Qed.
Lemma lem2426722 : term608.
Proof. exact (@lem2426711 (@lem2426721)). Qed.
Lemma lem2426724 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426725 : term604 = term605.
Proof. exact (@lem2426724 (NUMERAL 0) term193). Qed.
Lemma lem2426726 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426727 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426728 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426727 h1) (fun h1 : term605 = True => @lem2426726)). Qed.
Lemma lem2426729 : term605 = True.
Proof. exact (EQ_MP (@lem2426728) (@lem2426726)). Qed.
Lemma lem2426730 : term604 = True.
Proof. exact (TRANS (@lem2426725) (@lem2426729)). Qed.
Lemma lem2426731 : True = term604.
Proof. exact (SYM (@lem2426730)). Qed.
Lemma lem2426732 : term604.
Proof. exact (EQ_MP (@lem2426731) (@lem0)). Qed.
Lemma lem2426733 : term609.
Proof. exact (@lem2426722 (@lem2426732)). Qed.
Lemma lem2426735 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426736 : term555 = term556.
Proof. exact (@lem2426735 term193 term193). Qed.
Lemma lem2426737 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426738 : term558 = term193.
Proof. exact (EQ_MP (@lem2426737) (@lem940073)). Qed.
Lemma lem2426739 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426740 : term556 = term192.
Proof. exact (MK_COMB (@lem2426739) (@lem2426738)). Qed.
Lemma lem2426741 : term555 = term192.
Proof. exact (TRANS (@lem2426736) (@lem2426740)). Qed.
Lemma lem2426743 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2426744 : term568 = term573.
Proof. exact (@lem2426743 term193 term193). Qed.
Lemma lem2426745 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426746 : term558 = term193.
Proof. exact (EQ_MP (@lem2426745) (@lem940073)). Qed.
Lemma lem2426747 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426748 : term556 = term192.
Proof. exact (MK_COMB (@lem2426747) (@lem2426746)). Qed.
Lemma lem2426749 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2426750 : term573 = term546.
Proof. exact (MK_COMB (@lem2426749) (@lem2426748)). Qed.
Lemma lem2426751 : term568 = term546.
Proof. exact (TRANS (@lem2426744) (@lem2426750)). Qed.
Lemma lem2426752 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426753 : term610 = term598.
Proof. exact (MK_COMB (@lem2426752) (@lem2426751)). Qed.
Lemma lem2426754 : term611 = term600.
Proof. exact (MK_COMB (@lem2426753) (@lem2426741)). Qed.
Lemma lem2426756 (m : nat) : (term612 m) = term182.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2426757 : term600 = term182.
Proof. exact (@lem2426756 term193). Qed.
Lemma lem2426758 : term611 = term182.
Proof. exact (TRANS (@lem2426754) (@lem2426757)). Qed.
Lemma lem2426759 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426760 : term613 = term184.
Proof. exact (MK_COMB (@lem2426759) (@lem2426758)). Qed.
Lemma lem2426761 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem2426762 : term614 = term615.
Proof. exact (MK_COMB (@lem2426760) (@lem2426761)). Qed.
Lemma lem2426764 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426765 : term615 = term182.
Proof. exact (@lem2426764 term193). Qed.
Lemma lem2426766 : term614 = term182.
Proof. exact (TRANS (@lem2426762) (@lem2426765)). Qed.
Lemma lem2426768 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2426769 : term555 = term556.
Proof. exact (@lem2426768 term193 term193). Qed.
Lemma lem2426770 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426771 : term558 = term193.
Proof. exact (EQ_MP (@lem2426770) (@lem940073)). Qed.
Lemma lem2426772 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426773 : term556 = term192.
Proof. exact (MK_COMB (@lem2426772) (@lem2426771)). Qed.
Lemma lem2426774 : term555 = term192.
Proof. exact (TRANS (@lem2426769) (@lem2426773)). Qed.
Lemma lem2426775 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2426776 : term617 = term615.
Proof. exact (MK_COMB (@lem2426775) (@lem2426774)). Qed.
Lemma lem2426778 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426779 : term615 = term182.
Proof. exact (@lem2426778 term193). Qed.
Lemma lem2426780 : term617 = term182.
Proof. exact (TRANS (@lem2426776) (@lem2426779)). Qed.
Lemma lem2426781 : term182 = term617.
Proof. exact (SYM (@lem2426780)). Qed.
Lemma lem2426782 : term614 = term617.
Proof. exact (TRANS (@lem2426766) (@lem2426781)). Qed.
Lemma lem2426783 : term601 = term543.
Proof. exact (@lem2426733 (@lem2426782)). Qed.
Lemma lem2426784 : term600 = term543.
Proof. exact (TRANS (@lem2426699) (@lem2426783)). Qed.
Lemma lem2426786 (x : real) : (term562 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2426787 : term543 = term182.
Proof. exact (@lem2426786 term182). Qed.
Lemma lem2426788 : term600 = term182.
Proof. exact (TRANS (@lem2426784) (@lem2426787)). Qed.
Lemma lem2426789 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2426790 : term618 = term184.
Proof. exact (MK_COMB (@lem2426789) (@lem2426788)). Qed.
Lemma lem2426791 (z : int) (z' : int) : (term177 z z') = (term177 z z').
Proof. exact (eq_refl (term177 z z')). Qed.
Lemma lem2426792 (z : int) (z' : int) : (term1181 z z') = (term1182 z z').
Proof. exact (MK_COMB (@lem2426790) (@lem2426791 z z')). Qed.
Lemma lem2426793 (z : int) (z' : int) : (term1186 z z') = (term1182 z z').
Proof. exact (TRANS (@lem2426690 z z') (@lem2426792 z z')). Qed.
Lemma lem2426794 (z : int) (z' : int) : (term1182 z z') = term182.
Proof. exact (@lem1982719 (term177 z z')). Qed.
Lemma lem2426795 (z : int) (z' : int) : (term1186 z z') = term182.
Proof. exact (TRANS (@lem2426793 z z') (@lem2426794 z z')). Qed.
Lemma lem2426796 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2426797 (z : int) (z' : int) : (term1187 z z') = term206.
Proof. exact (MK_COMB (@lem2426796) (@lem2426795 z z')). Qed.
Lemma lem2426798 : term546 = term546.
Proof. exact (eq_refl term546). Qed.
Lemma lem2426799 (z : int) (z' : int) : (term1221 z z') = term576.
Proof. exact (MK_COMB (@lem2426797 z z') (@lem2426798)). Qed.
Lemma lem2426800 (z : int) (z' : int) : (term1220 z z') = term576.
Proof. exact (TRANS (@lem2426689 z z') (@lem2426799 z z')). Qed.
Lemma lem2426801 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2426802 (z : int) (z' : int) : (term1220 z z') = term546.
Proof. exact (TRANS (@lem2426800 z z') (@lem2426801)). Qed.
Lemma lem2426803 (y' : int) (z : int) (z' : int) : (term1218 y' z z') = term576.
Proof. exact (MK_COMB (@lem2426688 z y') (@lem2426802 z z')). Qed.
Lemma lem2426804 (y' : int) (z : int) (z' : int) : (term1217 y' z z') = term576.
Proof. exact (TRANS (@lem2426580 y' z z') (@lem2426803 y' z z')). Qed.
Lemma lem2426805 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2426806 (y' : int) (z : int) (z' : int) : (term1217 y' z z') = term546.
Proof. exact (TRANS (@lem2426804 y' z z') (@lem2426805)). Qed.
Lemma lem2426807 (y : int) (y' : int) (z : int) (z' : int) : (term1216 y y' z z') = term576.
Proof. exact (MK_COMB (@lem2426579 y z') (@lem2426806 y' z z')). Qed.
Lemma lem2426808 (y : int) (y' : int) (z : int) (z' : int) : (term1215 y y' z z') = term576.
Proof. exact (TRANS (@lem2426471 y y' z z') (@lem2426807 y y' z z')). Qed.
Lemma lem2426809 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2426810 (y : int) (y' : int) (z : int) (z' : int) : (term1215 y y' z z') = term546.
Proof. exact (TRANS (@lem2426808 y y' z z') (@lem2426809)). Qed.
Lemma lem2426811 (y : int) (y' : int) (z : int) (z' : int) : (term1214 y y' z z') = term576.
Proof. exact (MK_COMB (@lem2426470 y y') (@lem2426810 y y' z z')). Qed.
Lemma lem2426812 (y : int) (y' : int) (z : int) (z' : int) : (term1213 y y' z z') = term576.
Proof. exact (TRANS (@lem2426362 y y' z z') (@lem2426811 y y' z z')). Qed.
Lemma lem2426813 : term576 = term546.
Proof. exact (@lem1982721 term546). Qed.
Lemma lem2426814 (y : int) (y' : int) (z : int) (z' : int) : (term1213 y y' z z') = term546.
Proof. exact (TRANS (@lem2426812 y y' z z') (@lem2426813)). Qed.
Lemma lem2426815 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2426816 (y : int) (y' : int) (z : int) (z' : int) : (term1222 y y' z z') = term578.
Proof. exact (MK_COMB (@lem2426815) (@lem2426814 y y' z z')). Qed.
Lemma lem2426817 : term182 = term182.
Proof. exact (eq_refl term182). Qed.
Lemma lem2426818 (y : int) (y' : int) (z : int) (z' : int) : (term1212 y y' z z') = term579.
Proof. exact (MK_COMB (@lem2426816 y y' z z') (@lem2426817)). Qed.
Lemma lem2426819 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : term579.
Proof. exact (EQ_MP (@lem2426818 y y' z z') (@lem2426361 y y' z z' h1)). Qed.
Lemma lem2426821 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2426822 : term579 = term1099.
Proof. exact (@lem2426821 term182 term546). Qed.
Lemma lem2426824 (x : nat) : (term544 x) = (term545 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2426825 : term546 = term547.
Proof. exact (@lem2426824 term193). Qed.
Lemma lem2426827 (x : nat) : (real_of_num x) = (term542 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2426828 : term182 = term543.
Proof. exact (@lem2426827 (NUMERAL 0)). Qed.
Lemma lem2426829 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2426830 : term1100 = term1101.
Proof. exact (MK_COMB (@lem2426829) (@lem2426828)). Qed.
Lemma lem2426831 : term1099 = term1102.
Proof. exact (MK_COMB (@lem2426830) (@lem2426825)). Qed.
Lemma lem2426832 : term1103.
Proof. exact (@lem1980026 term182 term192 term546 term192). Qed.
Lemma lem2426834 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426835 : term604 = term605.
Proof. exact (@lem2426834 (NUMERAL 0) term193). Qed.
Lemma lem2426836 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426837 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426838 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426837 h1) (fun h1 : term605 = True => @lem2426836)). Qed.
Lemma lem2426839 : term605 = True.
Proof. exact (EQ_MP (@lem2426838) (@lem2426836)). Qed.
Lemma lem2426840 : term604 = True.
Proof. exact (TRANS (@lem2426835) (@lem2426839)). Qed.
Lemma lem2426841 : True = term604.
Proof. exact (SYM (@lem2426840)). Qed.
Lemma lem2426842 : term604.
Proof. exact (EQ_MP (@lem2426841) (@lem0)). Qed.
Lemma lem2426843 : term1104.
Proof. exact (@lem2426832 (@lem2426842)). Qed.
Lemma lem2426845 (m : nat) (n : nat) : (term603 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2426846 : term604 = term605.
Proof. exact (@lem2426845 (NUMERAL 0) term193). Qed.
Lemma lem2426847 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426848 (h1 : term606 = (BIT1 0)) : term605 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2426849 : (term606 = (BIT1 0)) = (term605 = True).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426848 h1) (fun h1 : term605 = True => @lem2426847)). Qed.
Lemma lem2426850 : term605 = True.
Proof. exact (EQ_MP (@lem2426849) (@lem2426847)). Qed.
Lemma lem2426851 : term604 = True.
Proof. exact (TRANS (@lem2426846) (@lem2426850)). Qed.
Lemma lem2426852 : True = term604.
Proof. exact (SYM (@lem2426851)). Qed.
Lemma lem2426853 : term604.
Proof. exact (EQ_MP (@lem2426852) (@lem0)). Qed.
Lemma lem2426854 : term1102 = term1105.
Proof. exact (@lem2426843 (@lem2426853)). Qed.
Lemma lem2426856 (m : nat) (n : nat) : (term571 m n) = (term572 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2426857 : term568 = term573.
Proof. exact (@lem2426856 term193 term193). Qed.
Lemma lem2426858 : (term557 = (BIT1 0)) = (term558 = term193).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2426859 : term558 = term193.
Proof. exact (EQ_MP (@lem2426858) (@lem940073)). Qed.
Lemma lem2426860 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2426861 : term556 = term192.
Proof. exact (MK_COMB (@lem2426860) (@lem2426859)). Qed.
Lemma lem2426862 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2426863 : term573 = term546.
Proof. exact (MK_COMB (@lem2426862) (@lem2426861)). Qed.
Lemma lem2426864 : term568 = term546.
Proof. exact (TRANS (@lem2426857) (@lem2426863)). Qed.
Lemma lem2426866 (x : nat) : (term616 x) = term182.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2426867 : term615 = term182.
Proof. exact (@lem2426866 term193). Qed.
Lemma lem2426868 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2426869 : term1106 = term1100.
Proof. exact (MK_COMB (@lem2426868) (@lem2426867)). Qed.
Lemma lem2426870 : term1105 = term1099.
Proof. exact (MK_COMB (@lem2426869) (@lem2426864)). Qed.
Lemma lem2426872 (m : nat) (n : nat) : (term1107 m n) = (term1108 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2426873 : term1099 = term1109.
Proof. exact (@lem2426872 (NUMERAL 0) term193). Qed.
Lemma lem2426874 : term606 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2426875 (h1 : term606 = (BIT1 0)) : (term193 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2426876 : (term606 = (BIT1 0)) = ((term193 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term606 = (BIT1 0) => @lem2426875 h1) (fun h1 : (term193 = (NUMERAL 0)) = False => @lem2426874)). Qed.
Lemma lem2426877 : (term193 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2426876) (@lem2426874)). Qed.
Lemma lem2426878 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2426879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2426880 : term1110 = (and True).
Proof. exact (MK_COMB (@lem2426879) (@lem2426878)). Qed.
Lemma lem2426881 : term1109 = (True /\ False).
Proof. exact (MK_COMB (@lem2426880) (@lem2426877)). Qed.
Lemma lem2426883 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2426884 : term1109 = False.
Proof. exact (TRANS (@lem2426881) (@lem2426883)). Qed.
Lemma lem2426885 : term1099 = False.
Proof. exact (TRANS (@lem2426873) (@lem2426884)). Qed.
Lemma lem2426886 : term1105 = False.
Proof. exact (TRANS (@lem2426870) (@lem2426885)). Qed.
Lemma lem2426887 : term1102 = False.
Proof. exact (TRANS (@lem2426854) (@lem2426886)). Qed.
Lemma lem2426888 : term1099 = False.
Proof. exact (TRANS (@lem2426831) (@lem2426887)). Qed.
Lemma lem2426889 : term579 = False.
Proof. exact (TRANS (@lem2426822) (@lem2426888)). Qed.
Lemma lem2426890 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1224 y y' z z') : False.
Proof. exact (EQ_MP (@lem2426889) (@lem2426819 y y' z z' h1)). Qed.
Lemma lem2426891 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1080 y y' z z') : False.
Proof. exact (or_elim (@lem2425540 y y' z z' h1) (fun h0 : term1223 y y' z z' => @lem2426164 y y' z z' h0) (fun h0 : term1224 y y' z z' => @lem2426890 y y' z z' h0)). Qed.
Lemma lem2426892 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1083 y y' z z') : False.
Proof. exact (or_elim (@lem2424187 y y' z z' h1) (fun h0 : term1081 y y' z z' => @lem2425539 y y' z z' h0) (fun h0 : term1080 y y' z z' => @lem2426891 y y' z z' h0)). Qed.
Lemma lem2426893 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1089 y y' z z') : False.
Proof. exact (or_elim (@lem2422492 y y' z z' h1) (fun h0 : term1087 y z => @lem2424186 y z h0) (fun h0 : term1083 y y' z z' => @lem2426892 y y' z z' h0)). Qed.
Lemma lem2426894 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1090 y y' z z') : False.
Proof. exact (or_elim (@lem2422345 y y' z z' h1) (fun h0 : term824 => @lem2422491 h0) (fun h0 : term1089 y y' z z' => @lem2426893 y y' z z' h0)). Qed.
Lemma lem2426896 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1090 y y' z z') : term1090 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem2426897 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1090 y y' z z') : (term1090 y y' z z') = False.
Proof. exact (prop_ext (fun h2 : term1090 y y' z z' => @lem2426894 y y' z z' h1) (fun h2 : False => @lem2426896 y y' z z' h1)). Qed.
Lemma lem2426898 (y : int) (y' : int) (z : int) (z' : int) (h1 : term1090 y y' z z') : False.
Proof. exact (EQ_MP (@lem2426897 y y' z z' h1) (@lem2426896 y y' z z' h1)). Qed.
Lemma lem2426899 (y : int) (y' : int) (z : int) (h1 : term1092 y y' z) : term1092 y y' z.
Proof. exact (h1). Qed.
Lemma lem2426900 (y : int) (y' : int) (z : int) (h1 : term1092 y y' z) : False.
Proof. exact (ex_elim (@lem2426899 y y' z h1) (fun z' : int => fun h0 : term1091 y y' z z' => @lem2426898 y y' z z' h0)). Qed.
Lemma lem2426901 (y : int) (z : int) (h1 : term1094 y z) : term1094 y z.
Proof. exact (h1). Qed.
Lemma lem2426902 (y : int) (z : int) (h1 : term1094 y z) : False.
Proof. exact (ex_elim (@lem2426901 y z h1) (fun y' : int => fun h0 : term1093 y z y' => @lem2426900 y y' z h0)). Qed.
Lemma lem2426903 (y : int) (h1 : term1096 y) : term1096 y.
Proof. exact (h1). Qed.
Lemma lem2426904 (y : int) (h1 : term1096 y) : False.
Proof. exact (ex_elim (@lem2426903 y h1) (fun z : int => fun h0 : term1095 y z => @lem2426902 y z h0)). Qed.
Lemma lem2426905 (h1 : term1098) : term1098.
Proof. exact (h1). Qed.
Lemma lem2426906 (h1 : term1098) : False.
Proof. exact (ex_elim (@lem2426905 h1) (fun y : int => fun h0 : term1097 y => @lem2426904 y h0)). Qed.
Lemma lem2426907 (h1 : term359) : term359.
Proof. exact (h1). Qed.
Lemma lem2426908 (h1 : term359) : term1098.
Proof. exact (EQ_MP (@lem2422287) (@lem2426907 h1)). Qed.
Lemma lem2426909 (h1 : term359) : term1098 = False.
Proof. exact (prop_ext (fun h2 : term1098 => @lem2426906 h2) (fun h2 : False => @lem2426908 h1)). Qed.
Lemma lem2426910 (h1 : term359) : False.
Proof. exact (EQ_MP (@lem2426909 h1) (@lem2426908 h1)). Qed.
Lemma lem2426911 : term1225.
Proof. exact (fun h0 : term359 => @lem2426910 h0). Qed.
Lemma lem2426912 : term1226.
Proof. exact (@lem1386578 term1227). Qed.
Lemma lem2426915 : term1227.
Proof. exact (@lem2426912 (@lem2426911)). Qed.
Lemma lem2426916 : term357 = term159.
Proof. exact (SYM (@lem2417869)). Qed.
Lemma lem2426917 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2426918 : term1227 = term86.
Proof. exact (MK_COMB (@lem2426917) (@lem2426916)). Qed.
Lemma lem2426919 : term86.
Proof. exact (EQ_MP (@lem2426918) (@lem2426915)). Qed.
Lemma lem2426920 : term85.
Proof. exact (EQ_MP (@lem2417076) (@lem2426919)). Qed.
Lemma lem2426921 : term85 = (term85 = True).
Proof. exact (@lem7 term85). Qed.
Lemma lem2426922 : term85 = True.
Proof. exact (EQ_MP (@lem2426921) (@lem2426920)). Qed.
Lemma lem2426923 : True = term85.
Proof. exact (SYM (@lem2426922)). Qed.
Lemma lem2426924 : term85.
Proof. exact (EQ_MP (@lem2426923) (@lem0)). Qed.
Lemma lem2426925 : term74.
Proof. exact (EQ_MP (@lem2417075) (@lem2426924)). Qed.
Lemma lem2426928 : term73.
Proof. exact (EQ_MP (@lem2416981) (@lem2426925)). Qed.
Lemma lem2426989 {A : Type'} (add : type1400 A) : term1228 A add.
Proof. exact (@lem1032609 A add). Qed.
Lemma lem2426990 {A : Type'} (add : type1400 A) : (term1228 A add) = (term1229 A add).
Proof. exact (eq_refl (term1228 A add)). Qed.
Lemma lem2426991 {A : Type'} (add : type1400 A) : term1229 A add.
Proof. exact (EQ_MP (@lem2426990 A add) (@lem2426989 A add)). Qed.
Lemma lem2426992 {A : Type'} (add : type1400 A) (mul : type1400 A) : term1230 A add mul.
Proof. exact (@lem2426991 A add mul). Qed.
Lemma lem2426993 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term1230 A add mul) = (term1231 A add mul).
Proof. exact (eq_refl (term1230 A add mul)). Qed.
Lemma lem2426994 {A : Type'} (add : type1400 A) (mul : type1400 A) : term1231 A add mul.
Proof. exact (EQ_MP (@lem2426993 A add mul) (@lem2426992 A add mul)). Qed.
Lemma lem2426995 {A : Type'} (add : type1400 A) (mul : type1400 A) (n0 : A) : term1232 A add mul n0.
Proof. exact (@lem2426994 A add mul n0). Qed.
Lemma lem2426996 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) : (term1232 A add mul n0) = (term1233 A n0 add mul).
Proof. exact (eq_refl (term1232 A add mul n0)). Qed.
Lemma lem2426999 {A : Type'} (n0 : A) (add : type1400 A) (mul : type1400 A) : term1233 A n0 add mul.
Proof. exact (EQ_MP (@lem2426996 A n0 add mul) (@lem2426995 A add mul n0)). Qed.
Lemma lem2427000 (n0 : int) (add : type1551) (mul : type1551) : term1234 n0 add mul.
Proof. exact (@lem2426999 int n0 add mul). Qed.
Lemma lem2427001 : term1235.
Proof. exact (@lem2427000 term0 int_add int_mul). Qed.
Lemma lem2427002 : term1236.
Proof. exact (@lem2427001 (@lem2426928)). Qed.
