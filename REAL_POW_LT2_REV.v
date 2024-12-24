Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_LT2_REV_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_NOT_LE_spec.
Require Import REAL_POW_LE2_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
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
Require Import thm69_spec.
Lemma lem1650796 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1650797 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1650798 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1650797 t1) (@lem1650796 t1)). Qed.
Lemma lem1650799 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1650798 t1 t2). Qed.
Lemma lem1650800 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1650801 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1650800 t1 t2) (@lem1650799 t1 t2)). Qed.
Lemma lem1650802 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1650801 t1 t2 t3). Qed.
Lemma lem1650803 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1650804 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1650803 t1 t2 t3) (@lem1650802 t1 t2 t3)). Qed.
Lemma lem1650805 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1650804 t1 t2 t3)). Qed.
Lemma lem1650807 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1650808 : term8 = term9.
Proof. exact (@lem1650807 term8). Qed.
Lemma lem1650809 : term9 = term8.
Proof. exact (SYM (@lem1650808)). Qed.
Lemma lem1650810 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1650813 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1650814 : term12.
Proof. exact (fun h0 : term11 => @lem1650813 h0). Qed.
Lemma lem1650815 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1650816 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1650817 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1650815 h2 (@lem1650816 h1)). Qed.
Lemma lem1650818 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1650817 h1 h0). Qed.
Lemma lem1650819 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1650820 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1650818 h1 (@lem1650819 h2)). Qed.
Lemma lem1650821 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1650820 h0 h1). Qed.
Lemma lem1650822 : term14.
Proof. exact (fun h0 : term12 => @lem1650821 h0). Qed.
Lemma lem1650825 : term12.
Proof. exact (@lem1650822 (@lem1650814)). Qed.
Lemma lem1650855 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1650856 : term15 = term16.
Proof. exact (@lem1650855 term17). Qed.
Lemma lem1650873 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1650874 : term19 = term20.
Proof. exact (MK_COMB (@lem1650873) (@lem1650856)). Qed.
Lemma lem1650877 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1650884 : term11 = term22.
Proof. exact (MK_COMB (@lem1650877) (@lem1650874)). Qed.
Lemma lem1650893 (x : real) (y : real) (n : nat) : (term23 x y n) = (term23 x y n).
Proof. exact (eq_refl (term23 x y n)). Qed.
Lemma lem1650894 (x : real) (n : nat) : (term24 x n) = (term24 x n).
Proof. exact (fun_ext (fun y : real => @lem1650893 x y n)). Qed.
Lemma lem1650895 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650896 (x : real) (n : nat) : (term25 x n) = (term25 x n).
Proof. exact (MK_COMB (@lem1650895) (@lem1650894 x n)). Qed.
Lemma lem1650897 (n : nat) : (term26 n) = (term26 n).
Proof. exact (fun_ext (fun x : real => @lem1650896 x n)). Qed.
Lemma lem1650898 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650899 (n : nat) : (term27 n) = (term27 n).
Proof. exact (MK_COMB (@lem1650898) (@lem1650897 n)). Qed.
Lemma lem1650900 : term28 = term28.
Proof. exact (fun_ext (fun n : nat => @lem1650899 n)). Qed.
Lemma lem1650901 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1650902 : term17 = term17.
Proof. exact (MK_COMB (@lem1650901) (@lem1650900)). Qed.
Lemma lem1650903 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1650904 : term16 = term16.
Proof. exact (MK_COMB (@lem1650903) (@lem1650902)). Qed.
Lemma lem1650911 (y : real) (x : real) : ((term29 x y) = (real_lt y x)) = ((term29 x y) = (real_lt y x)).
Proof. exact (eq_refl ((term29 x y) = (real_lt y x))). Qed.
Lemma lem1650912 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1650911 y x)). Qed.
Lemma lem1650913 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650914 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1650913) (@lem1650912 x)). Qed.
Lemma lem1650915 : term32 = term32.
Proof. exact (fun_ext (fun x : real => @lem1650914 x)). Qed.
Lemma lem1650916 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650917 : term33 = term33.
Proof. exact (MK_COMB (@lem1650916) (@lem1650915)). Qed.
Lemma lem1650918 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1650919 : term18 = term18.
Proof. exact (MK_COMB (@lem1650918) (@lem1650917)). Qed.
Lemma lem1650920 : term20 = term20.
Proof. exact (MK_COMB (@lem1650919) (@lem1650904)). Qed.
Lemma lem1650929 (n : nat) (x : real) (y : real) : (term34 n x y) = (term34 n x y).
Proof. exact (eq_refl (term34 n x y)). Qed.
Lemma lem1650930 (n : nat) (x : real) : (term35 n x) = (term35 n x).
Proof. exact (fun_ext (fun y : real => @lem1650929 n x y)). Qed.
Lemma lem1650931 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650932 (n : nat) (x : real) : (term36 n x) = (term36 n x).
Proof. exact (MK_COMB (@lem1650931) (@lem1650930 n x)). Qed.
Lemma lem1650933 (n : nat) : (term37 n) = (term37 n).
Proof. exact (fun_ext (fun x : real => @lem1650932 n x)). Qed.
Lemma lem1650934 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1650935 (n : nat) : (term38 n) = (term38 n).
Proof. exact (MK_COMB (@lem1650934) (@lem1650933 n)). Qed.
Lemma lem1650936 : term39 = term39.
Proof. exact (fun_ext (fun n : nat => @lem1650935 n)). Qed.
Lemma lem1650937 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1650938 : term8 = term8.
Proof. exact (MK_COMB (@lem1650937) (@lem1650936)). Qed.
Lemma lem1650939 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1650940 : term10 = term10.
Proof. exact (MK_COMB (@lem1650939) (@lem1650938)). Qed.
Lemma lem1650941 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1650942 : term21 = term21.
Proof. exact (MK_COMB (@lem1650941) (@lem1650940)). Qed.
Lemma lem1650943 : term22 = term22.
Proof. exact (MK_COMB (@lem1650942) (@lem1650920)). Qed.
Lemma lem1651006 : term11 = term22.
Proof. exact (TRANS (@lem1650884) (@lem1650943)). Qed.
Lemma lem1651007 : term22 = term11.
Proof. exact (SYM (@lem1651006)). Qed.
Lemma lem1651008 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1651009 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1651010 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1651021 (n : nat) (x : real) (y : real) : (term40 n x y) = (term41 n x y).
Proof. exact (@lem17362 (term42 x y n) (real_lt x y)). Qed.
Lemma lem1651022 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1651023 (n : nat) (x : real) : (term45 n x) = (term46 n x).
Proof. exact (@lem1651022 (term35 n x)). Qed.
Lemma lem1651024 (n : nat) (x : real) (y : real) : (term47 n x y) = (term34 n x y).
Proof. exact (eq_refl (term47 n x y)). Qed.
Lemma lem1651025 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1651026 (n : nat) (x : real) (y : real) : (term48 n x y) = (term40 n x y).
Proof. exact (MK_COMB (@lem1651025) (@lem1651024 n x y)). Qed.
Lemma lem1651027 (n : nat) (x : real) (y : real) : (term48 n x y) = (term41 n x y).
Proof. exact (TRANS (@lem1651026 n x y) (@lem1651021 n x y)). Qed.
Lemma lem1651028 (n : nat) (x : real) : (term49 n x) = (term50 n x).
Proof. exact (fun_ext (fun y : real => @lem1651027 n x y)). Qed.
Lemma lem1651029 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1651030 (n : nat) (x : real) : (term46 n x) = (term51 n x).
Proof. exact (MK_COMB (@lem1651029) (@lem1651028 n x)). Qed.
Lemma lem1651031 (n : nat) (x : real) : (term45 n x) = (term51 n x).
Proof. exact (TRANS (@lem1651023 n x) (@lem1651030 n x)). Qed.
Lemma lem1651032 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1651033 (n : nat) : (term52 n) = (term53 n).
Proof. exact (@lem1651032 (term37 n)). Qed.
Lemma lem1651034 (n : nat) (x : real) : (term54 n x) = (term36 n x).
Proof. exact (eq_refl (term54 n x)). Qed.
Lemma lem1651035 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1651036 (n : nat) (x : real) : (term55 n x) = (term45 n x).
Proof. exact (MK_COMB (@lem1651035) (@lem1651034 n x)). Qed.
Lemma lem1651037 (n : nat) (x : real) : (term55 n x) = (term51 n x).
Proof. exact (TRANS (@lem1651036 n x) (@lem1651031 n x)). Qed.
Lemma lem1651038 (n : nat) : (term56 n) = (term57 n).
Proof. exact (fun_ext (fun x : real => @lem1651037 n x)). Qed.
Lemma lem1651039 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1651040 (n : nat) : (term53 n) = (term58 n).
Proof. exact (MK_COMB (@lem1651039) (@lem1651038 n)). Qed.
Lemma lem1651041 (n : nat) : (term52 n) = (term58 n).
Proof. exact (TRANS (@lem1651033 n) (@lem1651040 n)). Qed.
Lemma lem1651042 (P : nat -> Prop) : (term59 P) = (term60 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1651043 : term10 = term61.
Proof. exact (@lem1651042 term39). Qed.
Lemma lem1651044 (n : nat) : (term62 n) = (term38 n).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem1651045 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1651046 (n : nat) : (term63 n) = (term52 n).
Proof. exact (MK_COMB (@lem1651045) (@lem1651044 n)). Qed.
Lemma lem1651047 (n : nat) : (term63 n) = (term58 n).
Proof. exact (TRANS (@lem1651046 n) (@lem1651041 n)). Qed.
Lemma lem1651048 : term64 = term65.
Proof. exact (fun_ext (fun n : nat => @lem1651047 n)). Qed.
Lemma lem1651049 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1651050 : term61 = term66.
Proof. exact (MK_COMB (@lem1651049) (@lem1651048)). Qed.
Lemma lem1651111 : term10 = term66.
Proof. exact (TRANS (@lem1651043) (@lem1651050)). Qed.
Lemma lem1651112 (h1 : term10) : term66.
Proof. exact (EQ_MP (@lem1651111) (@lem1651008 h1)). Qed.
Lemma lem1651116 (x : real) (y : real) : (term67 x y) = (real_le x y).
Proof. exact (@lem16933 (real_le x y)). Qed.
Lemma lem1651118 (y : real) (x : real) : (real_lt y x) = (real_lt y x).
Proof. exact (eq_refl (real_lt y x)). Qed.
Lemma lem1651119 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1651120 (x : real) (y : real) : (term68 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1651119) (@lem1651116 x y)). Qed.
Lemma lem1651121 (y : real) (x : real) : (term70 y x) = (term71 y x).
Proof. exact (MK_COMB (@lem1651120 x y) (@lem1651118 y x)). Qed.
Lemma lem1651126 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (eq_refl (term72 y x)). Qed.
Lemma lem1651127 (y : real) (x : real) : (term73 y x) = (term74 y x).
Proof. exact (MK_COMB (@lem1651126 y x) (@lem1651121 y x)). Qed.
Lemma lem1651128 (y : real) (x : real) : ((term29 x y) = (real_lt y x)) = (term73 y x).
Proof. exact (@lem17784 (term29 x y) (real_lt y x)). Qed.
Lemma lem1651129 (y : real) (x : real) : ((term29 x y) = (real_lt y x)) = (term74 y x).
Proof. exact (TRANS (@lem1651128 y x) (@lem1651127 y x)). Qed.
Lemma lem1651130 (x : real) : (term30 x) = (term75 x).
Proof. exact (fun_ext (fun y : real => @lem1651129 y x)). Qed.
Lemma lem1651131 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651132 (x : real) : (term31 x) = (term76 x).
Proof. exact (MK_COMB (@lem1651131) (@lem1651130 x)). Qed.
Lemma lem1651133 : term32 = term77.
Proof. exact (fun_ext (fun x : real => @lem1651132 x)). Qed.
Lemma lem1651134 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651135 : term33 = term78.
Proof. exact (MK_COMB (@lem1651134) (@lem1651133)). Qed.
Lemma lem1651141 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1651142 (P : real -> Prop) (Q : real -> Prop) : (term81 P Q) = (term82 P Q).
Proof. exact (@lem1651141 real P Q). Qed.
Lemma lem1651143 (x : real) : (term83 x) = (term84 x).
Proof. exact (@lem1651142 (term85 x) (term86 x)). Qed.
Lemma lem1651144 (y : real) (x : real) : (term87 x y) = (term88 y x).
Proof. exact (eq_refl (term87 x y)). Qed.
Lemma lem1651145 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1651146 (y : real) (x : real) : (term89 x y) = (term72 y x).
Proof. exact (MK_COMB (@lem1651145) (@lem1651144 y x)). Qed.
Lemma lem1651147 (y : real) (x : real) : (term90 x y) = (term71 y x).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem1651148 (y : real) (x : real) : (term91 x y) = (term74 y x).
Proof. exact (MK_COMB (@lem1651146 y x) (@lem1651147 y x)). Qed.
Lemma lem1651149 (x : real) : (term92 x) = (term75 x).
Proof. exact (fun_ext (fun y : real => @lem1651148 y x)). Qed.
Lemma lem1651150 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651151 (x : real) : (term83 x) = (term76 x).
Proof. exact (MK_COMB (@lem1651150) (@lem1651149 x)). Qed.
Lemma lem1651152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1651153 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem1651152) (@lem1651151 x)). Qed.
Lemma lem1651154 (y : real) (x : real) : (term87 x y) = (term88 y x).
Proof. exact (eq_refl (term87 x y)). Qed.
Lemma lem1651155 (x : real) : (term95 x) = (term85 x).
Proof. exact (fun_ext (fun y : real => @lem1651154 y x)). Qed.
Lemma lem1651156 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651157 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1651156) (@lem1651155 x)). Qed.
Lemma lem1651158 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1651159 (x : real) : (term98 x) = (term99 x).
Proof. exact (MK_COMB (@lem1651158) (@lem1651157 x)). Qed.
Lemma lem1651160 (y : real) (x : real) : (term90 x y) = (term71 y x).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem1651161 (x : real) : (term100 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1651160 y x)). Qed.
Lemma lem1651162 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651163 (x : real) : (term101 x) = (term102 x).
Proof. exact (MK_COMB (@lem1651162) (@lem1651161 x)). Qed.
Lemma lem1651164 (x : real) : (term84 x) = (term103 x).
Proof. exact (MK_COMB (@lem1651159 x) (@lem1651163 x)). Qed.
Lemma lem1651165 (x : real) : ((term83 x) = (term84 x)) = ((term76 x) = (term103 x)).
Proof. exact (MK_COMB (@lem1651153 x) (@lem1651164 x)). Qed.
Lemma lem1651166 (x : real) : (term76 x) = (term103 x).
Proof. exact (EQ_MP (@lem1651165 x) (@lem1651143 x)). Qed.
Lemma lem1651263 : term77 = term104.
Proof. exact (fun_ext (fun x : real => @lem1651166 x)). Qed.
Lemma lem1651264 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651265 : term78 = term105.
Proof. exact (MK_COMB (@lem1651264) (@lem1651263)). Qed.
Lemma lem1651267 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1651268 (P : real -> Prop) (Q : real -> Prop) : (term81 P Q) = (term82 P Q).
Proof. exact (@lem1651267 real P Q). Qed.
Lemma lem1651269 : term106 = term107.
Proof. exact (@lem1651268 term108 term109). Qed.
Lemma lem1651270 (x : real) : (term110 x) = (term97 x).
Proof. exact (eq_refl (term110 x)). Qed.
Lemma lem1651271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1651272 (x : real) : (term111 x) = (term99 x).
Proof. exact (MK_COMB (@lem1651271) (@lem1651270 x)). Qed.
Lemma lem1651273 (x : real) : (term112 x) = (term102 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem1651274 (x : real) : (term113 x) = (term103 x).
Proof. exact (MK_COMB (@lem1651272 x) (@lem1651273 x)). Qed.
Lemma lem1651275 : term114 = term104.
Proof. exact (fun_ext (fun x : real => @lem1651274 x)). Qed.
Lemma lem1651276 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651277 : term106 = term105.
Proof. exact (MK_COMB (@lem1651276) (@lem1651275)). Qed.
Lemma lem1651278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1651279 : term115 = term116.
Proof. exact (MK_COMB (@lem1651278) (@lem1651277)). Qed.
Lemma lem1651280 (x : real) : (term110 x) = (term97 x).
Proof. exact (eq_refl (term110 x)). Qed.
Lemma lem1651281 : term117 = term108.
Proof. exact (fun_ext (fun x : real => @lem1651280 x)). Qed.
Lemma lem1651282 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651283 : term118 = term119.
Proof. exact (MK_COMB (@lem1651282) (@lem1651281)). Qed.
Lemma lem1651284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1651285 : term120 = term121.
Proof. exact (MK_COMB (@lem1651284) (@lem1651283)). Qed.
Lemma lem1651286 (x : real) : (term112 x) = (term102 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem1651287 : term122 = term109.
Proof. exact (fun_ext (fun x : real => @lem1651286 x)). Qed.
Lemma lem1651288 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651289 : term123 = term124.
Proof. exact (MK_COMB (@lem1651288) (@lem1651287)). Qed.
Lemma lem1651290 : term107 = term125.
Proof. exact (MK_COMB (@lem1651285) (@lem1651289)). Qed.
Lemma lem1651291 : (term106 = term107) = (term105 = term125).
Proof. exact (MK_COMB (@lem1651279) (@lem1651290)). Qed.
Lemma lem1651292 : term105 = term125.
Proof. exact (EQ_MP (@lem1651291) (@lem1651269)). Qed.
Lemma lem1651399 : term78 = term125.
Proof. exact (TRANS (@lem1651265) (@lem1651292)). Qed.
Lemma lem1651400 : term33 = term125.
Proof. exact (TRANS (@lem1651135) (@lem1651399)). Qed.
Lemma lem1651401 (h1 : term33) : term125.
Proof. exact (EQ_MP (@lem1651400) (@lem1651009 h1)). Qed.
Lemma lem1651408 (x : real) (y : real) : (term126 x y) = (term127 x y).
Proof. exact (@lem17045 (term128 x) (real_le x y)). Qed.
Lemma lem1651409 (x : real) (y : real) (n : nat) : (term129 x y n) = (term129 x y n).
Proof. exact (eq_refl (term129 x y n)). Qed.
Lemma lem1651410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1651411 (x : real) (y : real) : (term130 x y) = (term131 x y).
Proof. exact (MK_COMB (@lem1651410) (@lem1651408 x y)). Qed.
Lemma lem1651412 (x : real) (y : real) (n : nat) : (term132 x y n) = (term133 x y n).
Proof. exact (MK_COMB (@lem1651411 x y) (@lem1651409 x y n)). Qed.
Lemma lem1651413 (x : real) (y : real) (n : nat) : (term23 x y n) = (term132 x y n).
Proof. exact (@lem17265 (term134 x y) (term129 x y n)). Qed.
Lemma lem1651414 (x : real) (y : real) (n : nat) : (term23 x y n) = (term133 x y n).
Proof. exact (TRANS (@lem1651413 x y n) (@lem1651412 x y n)). Qed.
Lemma lem1651415 (x : real) (n : nat) : (term24 x n) = (term135 x n).
Proof. exact (fun_ext (fun y : real => @lem1651414 x y n)). Qed.
Lemma lem1651416 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651417 (x : real) (n : nat) : (term25 x n) = (term136 x n).
Proof. exact (MK_COMB (@lem1651416) (@lem1651415 x n)). Qed.
Lemma lem1651418 (n : nat) : (term26 n) = (term137 n).
Proof. exact (fun_ext (fun x : real => @lem1651417 x n)). Qed.
Lemma lem1651419 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651420 (n : nat) : (term27 n) = (term138 n).
Proof. exact (MK_COMB (@lem1651419) (@lem1651418 n)). Qed.
Lemma lem1651421 : term28 = term139.
Proof. exact (fun_ext (fun n : nat => @lem1651420 n)). Qed.
Lemma lem1651422 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1651483 : term17 = term140.
Proof. exact (MK_COMB (@lem1651422) (@lem1651421)). Qed.
Lemma lem1651484 (h1 : term17) : term140.
Proof. exact (EQ_MP (@lem1651483) (@lem1651010 h1)). Qed.
Lemma lem1651485 (n : nat) (h1 : term58 n) : term58 n.
Proof. exact (h1). Qed.
Lemma lem1651486 (n : nat) (x : real) (h1 : term51 n x) : term51 n x.
Proof. exact (h1). Qed.
Lemma lem1651500 (y : real) (x : real) : (term71 y x) = (term71 y x).
Proof. exact (eq_refl (term71 y x)). Qed.
Lemma lem1651501 (x : real) : (term86 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1651500 y x)). Qed.
Lemma lem1651502 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651503 (x : real) : (term102 x) = (term102 x).
Proof. exact (MK_COMB (@lem1651502) (@lem1651501 x)). Qed.
Lemma lem1651504 : term109 = term109.
Proof. exact (fun_ext (fun x : real => @lem1651503 x)). Qed.
Lemma lem1651505 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651506 : term124 = term124.
Proof. exact (MK_COMB (@lem1651505) (@lem1651504)). Qed.
Lemma lem1651523 (y : real) (x : real) : (term88 y x) = (term88 y x).
Proof. exact (eq_refl (term88 y x)). Qed.
Lemma lem1651524 (x : real) : (term85 x) = (term85 x).
Proof. exact (fun_ext (fun y : real => @lem1651523 y x)). Qed.
Lemma lem1651525 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651526 (x : real) : (term97 x) = (term97 x).
Proof. exact (MK_COMB (@lem1651525) (@lem1651524 x)). Qed.
Lemma lem1651527 : term108 = term108.
Proof. exact (fun_ext (fun x : real => @lem1651526 x)). Qed.
Lemma lem1651528 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651529 : term119 = term119.
Proof. exact (MK_COMB (@lem1651528) (@lem1651527)). Qed.
Lemma lem1651530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1651531 : term121 = term121.
Proof. exact (MK_COMB (@lem1651530) (@lem1651529)). Qed.
Lemma lem1651532 : term125 = term125.
Proof. exact (MK_COMB (@lem1651531) (@lem1651506)). Qed.
Lemma lem1651533 (h1 : term33) : term125.
Proof. exact (EQ_MP (@lem1651532) (@lem1651401 h1)). Qed.
Lemma lem1651570 (x : real) (y : real) (n : nat) : (term133 x y n) = (term133 x y n).
Proof. exact (eq_refl (term133 x y n)). Qed.
Lemma lem1651571 (x : real) (n : nat) : (term135 x n) = (term135 x n).
Proof. exact (fun_ext (fun y : real => @lem1651570 x y n)). Qed.
Lemma lem1651572 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651573 (x : real) (n : nat) : (term136 x n) = (term136 x n).
Proof. exact (MK_COMB (@lem1651572) (@lem1651571 x n)). Qed.
Lemma lem1651574 (n : nat) : (term137 n) = (term137 n).
Proof. exact (fun_ext (fun x : real => @lem1651573 x n)). Qed.
Lemma lem1651575 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651576 (n : nat) : (term138 n) = (term138 n).
Proof. exact (MK_COMB (@lem1651575) (@lem1651574 n)). Qed.
Lemma lem1651577 : term139 = term139.
Proof. exact (fun_ext (fun n : nat => @lem1651576 n)). Qed.
Lemma lem1651578 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1651579 : term140 = term140.
Proof. exact (MK_COMB (@lem1651578) (@lem1651577)). Qed.
Lemma lem1651580 (h1 : term17) : term140.
Proof. exact (EQ_MP (@lem1651579) (@lem1651484 h1)). Qed.
Lemma lem1651616 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term41 n x y.
Proof. exact (h1). Qed.
Lemma lem1651618 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term42 x y n.
Proof. exact (proj1 (@lem1651616 n x y h1)). Qed.
Lemma lem1651621 (h1 : term33) : term124.
Proof. exact (proj2 (@lem1651533 h1)). Qed.
Lemma lem1651622 (h1 : term33) : term119.
Proof. exact (proj1 (@lem1651533 h1)). Qed.
Lemma lem1651636 (x : real) (y : real) (n : nat) : (term133 x y n) = (term133 x y n).
Proof. exact (eq_refl (term133 x y n)). Qed.
Lemma lem1651637 (x : real) (n : nat) : (term135 x n) = (term135 x n).
Proof. exact (fun_ext (fun y : real => @lem1651636 x y n)). Qed.
Lemma lem1651638 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651639 (x : real) (n : nat) : (term136 x n) = (term136 x n).
Proof. exact (MK_COMB (@lem1651638) (@lem1651637 x n)). Qed.
Lemma lem1651640 (n : nat) : (term137 n) = (term137 n).
Proof. exact (fun_ext (fun x : real => @lem1651639 x n)). Qed.
Lemma lem1651641 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651642 (n : nat) : (term138 n) = (term138 n).
Proof. exact (MK_COMB (@lem1651641) (@lem1651640 n)). Qed.
Lemma lem1651643 : term139 = term139.
Proof. exact (fun_ext (fun n : nat => @lem1651642 n)). Qed.
Lemma lem1651644 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1651646 : term140 = term140.
Proof. exact (MK_COMB (@lem1651644) (@lem1651643)). Qed.
Lemma lem1651647 (h1 : term17) : term140.
Proof. exact (EQ_MP (@lem1651646) (@lem1651580 h1)). Qed.
Lemma lem1651667 (y : real) (x : real) : (term88 y x) = (term88 y x).
Proof. exact (eq_refl (term88 y x)). Qed.
Lemma lem1651668 (x : real) : (term85 x) = (term85 x).
Proof. exact (fun_ext (fun y : real => @lem1651667 y x)). Qed.
Lemma lem1651669 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651670 (x : real) : (term97 x) = (term97 x).
Proof. exact (MK_COMB (@lem1651669) (@lem1651668 x)). Qed.
Lemma lem1651671 : term108 = term108.
Proof. exact (fun_ext (fun x : real => @lem1651670 x)). Qed.
Lemma lem1651672 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651674 : term119 = term119.
Proof. exact (MK_COMB (@lem1651672) (@lem1651671)). Qed.
Lemma lem1651675 (h1 : term33) : term119.
Proof. exact (EQ_MP (@lem1651674) (@lem1651622 h1)). Qed.
Lemma lem1651683 (y : real) (x : real) : (term71 y x) = (term71 y x).
Proof. exact (eq_refl (term71 y x)). Qed.
Lemma lem1651684 (x : real) : (term86 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1651683 y x)). Qed.
Lemma lem1651685 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651686 (x : real) : (term102 x) = (term102 x).
Proof. exact (MK_COMB (@lem1651685) (@lem1651684 x)). Qed.
Lemma lem1651687 : term109 = term109.
Proof. exact (fun_ext (fun x : real => @lem1651686 x)). Qed.
Lemma lem1651688 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1651690 : term124 = term124.
Proof. exact (MK_COMB (@lem1651688) (@lem1651687)). Qed.
Lemma lem1651691 (h1 : term33) : term124.
Proof. exact (EQ_MP (@lem1651690) (@lem1651621 h1)). Qed.
Lemma lem1651692 (_25602 : nat) (h1 : term17) : term141 _25602.
Proof. exact (@lem1651647 h1 _25602). Qed.
Lemma lem1651693 (_25602 : nat) : (term141 _25602) = (term138 _25602).
Proof. exact (eq_refl (term141 _25602)). Qed.
Lemma lem1651694 (_25602 : nat) (h1 : term17) : term138 _25602.
Proof. exact (EQ_MP (@lem1651693 _25602) (@lem1651692 _25602 h1)). Qed.
Lemma lem1651695 (_25602 : nat) (_25603 : real) (h1 : term17) : term142 _25602 _25603.
Proof. exact (@lem1651694 _25602 h1 _25603). Qed.
Lemma lem1651696 (_25603 : real) (_25602 : nat) : (term142 _25602 _25603) = (term136 _25603 _25602).
Proof. exact (eq_refl (term142 _25602 _25603)). Qed.
Lemma lem1651697 (_25603 : real) (_25602 : nat) (h1 : term17) : term136 _25603 _25602.
Proof. exact (EQ_MP (@lem1651696 _25603 _25602) (@lem1651695 _25602 _25603 h1)). Qed.
Lemma lem1651698 (_25603 : real) (_25602 : nat) (_25604 : real) (h1 : term17) : term143 _25603 _25602 _25604.
Proof. exact (@lem1651697 _25603 _25602 h1 _25604). Qed.
Lemma lem1651699 (_25603 : real) (_25604 : real) (_25602 : nat) : (term143 _25603 _25602 _25604) = (term133 _25603 _25604 _25602).
Proof. exact (eq_refl (term143 _25603 _25602 _25604)). Qed.
Lemma lem1651700 (_25603 : real) (_25604 : real) (_25602 : nat) (h1 : term17) : term133 _25603 _25604 _25602.
Proof. exact (EQ_MP (@lem1651699 _25603 _25604 _25602) (@lem1651698 _25603 _25602 _25604 h1)). Qed.
Lemma lem1651701 (_25605 : real) (h1 : term33) : term110 _25605.
Proof. exact (@lem1651675 h1 _25605). Qed.
Lemma lem1651702 (_25605 : real) : (term110 _25605) = (term97 _25605).
Proof. exact (eq_refl (term110 _25605)). Qed.
Lemma lem1651703 (_25605 : real) (h1 : term33) : term97 _25605.
Proof. exact (EQ_MP (@lem1651702 _25605) (@lem1651701 _25605 h1)). Qed.
Lemma lem1651704 (_25605 : real) (_25606 : real) (h1 : term33) : term87 _25605 _25606.
Proof. exact (@lem1651703 _25605 h1 _25606). Qed.
Lemma lem1651705 (_25606 : real) (_25605 : real) : (term87 _25605 _25606) = (term88 _25606 _25605).
Proof. exact (eq_refl (term87 _25605 _25606)). Qed.
Lemma lem1651707 (_25607 : real) (h1 : term33) : term112 _25607.
Proof. exact (@lem1651691 h1 _25607). Qed.
Lemma lem1651708 (_25607 : real) : (term112 _25607) = (term102 _25607).
Proof. exact (eq_refl (term112 _25607)). Qed.
Lemma lem1651709 (_25607 : real) (h1 : term33) : term102 _25607.
Proof. exact (EQ_MP (@lem1651708 _25607) (@lem1651707 _25607 h1)). Qed.
Lemma lem1651710 (_25607 : real) (_25608 : real) (h1 : term33) : term90 _25607 _25608.
Proof. exact (@lem1651709 _25607 h1 _25608). Qed.
Lemma lem1651711 (_25608 : real) (_25607 : real) : (term90 _25607 _25608) = (term71 _25608 _25607).
Proof. exact (eq_refl (term90 _25607 _25608)). Qed.
Lemma lem1651723 (_25603 : real) (_25604 : real) (_25602 : nat) : (term133 _25603 _25604 _25602) = (term144 _25603 _25604 _25602).
Proof. exact (@lem1650805 (term145 _25603) (term29 _25603 _25604) (term129 _25603 _25604 _25602)). Qed.
Lemma lem1651724 (_25603 : real) (_25604 : real) (_25602 : nat) (h1 : term17) : term144 _25603 _25604 _25602.
Proof. exact (EQ_MP (@lem1651723 _25603 _25604 _25602) (@lem1651700 _25603 _25604 _25602 h1)). Qed.
Lemma lem1651726 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term146 x y.
Proof. exact (proj2 (@lem1651616 n x y h1)). Qed.
Lemma lem1651736 (_25606 : real) (_25605 : real) (h1 : term33) : term88 _25606 _25605.
Proof. exact (EQ_MP (@lem1651705 _25606 _25605) (@lem1651704 _25605 _25606 h1)). Qed.
Lemma lem1651742 (_25608 : real) (_25607 : real) (h1 : term33) : term71 _25608 _25607.
Proof. exact (EQ_MP (@lem1651711 _25608 _25607) (@lem1651710 _25607 _25608 h1)). Qed.
Lemma lem1651744 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term128 y.
Proof. exact (proj1 (@lem1651618 n x y h1)). Qed.
Lemma lem1651745 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term147 y.
Proof. exact (fun h0 : term145 y => @lem1651744 n x y h1). Qed.
Lemma lem1651747 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1651748 (y : real) : (term147 y) = (term128 y).
Proof. exact (@lem1651747 (term128 y)). Qed.
Lemma lem1651749 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term128 y.
Proof. exact (EQ_MP (@lem1651748 y) (@lem1651745 n x y h1)). Qed.
Lemma lem1651751 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term149 x y n.
Proof. exact (proj2 (@lem1651618 n x y h1)). Qed.
Lemma lem1651752 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term150 x y n.
Proof. exact (fun h0 : term151 x y n => @lem1651751 n x y h1). Qed.
Lemma lem1651754 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1651755 (x : real) (y : real) (n : nat) : (term150 x y n) = (term149 x y n).
Proof. exact (@lem1651754 (term149 x y n)). Qed.
Lemma lem1651756 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term149 x y n.
Proof. exact (EQ_MP (@lem1651755 x y n) (@lem1651752 n x y h1)). Qed.
Lemma lem1651758 (b : Prop) (a : Prop) : (a \/ b) = (term152 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1651759 (_25605 : real) (_25606 : real) : (term88 _25606 _25605) = (term153 _25605 _25606).
Proof. exact (@lem1651758 (term146 _25606 _25605) (term29 _25605 _25606)). Qed.
Lemma lem1651761 (a : Prop) : (term154 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1651762 (_25606 : real) (_25605 : real) : (term155 _25606 _25605) = (real_lt _25606 _25605).
Proof. exact (@lem1651761 (real_lt _25606 _25605)). Qed.
Lemma lem1651763 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1651764 (_25606 : real) (_25605 : real) : (term156 _25606 _25605) = (term157 _25606 _25605).
Proof. exact (MK_COMB (@lem1651763) (@lem1651762 _25606 _25605)). Qed.
Lemma lem1651765 (_25605 : real) (_25606 : real) : (term29 _25605 _25606) = (term29 _25605 _25606).
Proof. exact (eq_refl (term29 _25605 _25606)). Qed.
Lemma lem1651766 (_25605 : real) (_25606 : real) : (term153 _25605 _25606) = (term158 _25605 _25606).
Proof. exact (MK_COMB (@lem1651764 _25606 _25605) (@lem1651765 _25605 _25606)). Qed.
Lemma lem1651767 (_25605 : real) (_25606 : real) : (term88 _25606 _25605) = (term158 _25605 _25606).
Proof. exact (TRANS (@lem1651759 _25605 _25606) (@lem1651766 _25605 _25606)). Qed.
Lemma lem1651770 (_25605 : real) (_25606 : real) (h1 : term33) : term158 _25605 _25606.
Proof. exact (EQ_MP (@lem1651767 _25605 _25606) (@lem1651736 _25606 _25605 h1)). Qed.
Lemma lem1651771 (y : real) (x : real) (n : nat) (h1 : term33) : term159 y x n.
Proof. exact (@lem1651770 (real_pow y n) (real_pow x n) h1). Qed.
Lemma lem1651774 (n : nat) (x : real) (y : real) (h1 : term33) (h2 : term41 n x y) : term160 y x n.
Proof. exact (@lem1651771 y x n h1 (@lem1651756 n x y h2)). Qed.
Lemma lem1651775 (n : nat) (x : real) (y : real) (h1 : term33) (h2 : term41 n x y) : term161 y x n.
Proof. exact (fun h0 : term129 y x n => @lem1651774 n x y h1 h2). Qed.
Lemma lem1651777 (p : Prop) : (term162 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1651778 (y : real) (x : real) (n : nat) : (term161 y x n) = (term160 y x n).
Proof. exact (@lem1651777 (term129 y x n)). Qed.
Lemma lem1651779 (n : nat) (x : real) (y : real) (h1 : term33) (h2 : term41 n x y) : term160 y x n.
Proof. exact (EQ_MP (@lem1651778 y x n) (@lem1651775 n x y h1 h2)). Qed.
Lemma lem1651785 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1651786 (_25603 : real) (_25604 : real) (_25602 : nat) : (term144 _25603 _25604 _25602) = (term163 _25603 _25604 _25602).
Proof. exact (@lem1651785 (term29 _25603 _25604) (term145 _25603) (term129 _25603 _25604 _25602)). Qed.
Lemma lem1651800 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1651801 (_25604 : real) (_25602 : nat) (_25603 : real) : (term164 _25603 _25604 _25602) = (term165 _25604 _25602 _25603).
Proof. exact (@lem1651800 (term129 _25603 _25604 _25602) (term145 _25603)). Qed.
Lemma lem1651807 (_25603 : real) (_25604 : real) : (term166 _25603 _25604) = (term166 _25603 _25604).
Proof. exact (eq_refl (term166 _25603 _25604)). Qed.
Lemma lem1651808 (_25604 : real) (_25602 : nat) (_25603 : real) : (term163 _25603 _25604 _25602) = (term167 _25604 _25602 _25603).
Proof. exact (MK_COMB (@lem1651807 _25603 _25604) (@lem1651801 _25604 _25602 _25603)). Qed.
Lemma lem1651812 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1651813 (_25602 : nat) (_25604 : real) (_25603 : real) : (term167 _25604 _25602 _25603) = (term168 _25602 _25604 _25603).
Proof. exact (@lem1651812 (term129 _25603 _25604 _25602) (term29 _25603 _25604) (term145 _25603)). Qed.
Lemma lem1651829 (_25602 : nat) (_25604 : real) (_25603 : real) : (term163 _25603 _25604 _25602) = (term168 _25602 _25604 _25603).
Proof. exact (TRANS (@lem1651808 _25604 _25602 _25603) (@lem1651813 _25602 _25604 _25603)). Qed.
Lemma lem1651830 (_25602 : nat) (_25604 : real) (_25603 : real) : (term144 _25603 _25604 _25602) = (term168 _25602 _25604 _25603).
Proof. exact (TRANS (@lem1651786 _25603 _25604 _25602) (@lem1651829 _25602 _25604 _25603)). Qed.
Lemma lem1651831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1651832 (_25602 : nat) (_25604 : real) (_25603 : real) : (term169 _25603 _25604 _25602) = (term170 _25602 _25604 _25603).
Proof. exact (MK_COMB (@lem1651831) (@lem1651830 _25602 _25604 _25603)). Qed.
Lemma lem1651846 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1651847 (_25604 : real) (_25602 : nat) (_25603 : real) : (term164 _25603 _25604 _25602) = (term165 _25604 _25602 _25603).
Proof. exact (@lem1651846 (term129 _25603 _25604 _25602) (term145 _25603)). Qed.
Lemma lem1651853 (_25603 : real) (_25604 : real) : (term166 _25603 _25604) = (term166 _25603 _25604).
Proof. exact (eq_refl (term166 _25603 _25604)). Qed.
Lemma lem1651854 (_25604 : real) (_25602 : nat) (_25603 : real) : (term163 _25603 _25604 _25602) = (term167 _25604 _25602 _25603).
Proof. exact (MK_COMB (@lem1651853 _25603 _25604) (@lem1651847 _25604 _25602 _25603)). Qed.
Lemma lem1651858 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1651859 (_25602 : nat) (_25604 : real) (_25603 : real) : (term167 _25604 _25602 _25603) = (term168 _25602 _25604 _25603).
Proof. exact (@lem1651858 (term129 _25603 _25604 _25602) (term29 _25603 _25604) (term145 _25603)). Qed.
Lemma lem1651875 (_25602 : nat) (_25604 : real) (_25603 : real) : (term163 _25603 _25604 _25602) = (term168 _25602 _25604 _25603).
Proof. exact (TRANS (@lem1651854 _25604 _25602 _25603) (@lem1651859 _25602 _25604 _25603)). Qed.
Lemma lem1651876 (_25602 : nat) (_25604 : real) (_25603 : real) : ((term144 _25603 _25604 _25602) = (term163 _25603 _25604 _25602)) = ((term168 _25602 _25604 _25603) = (term168 _25602 _25604 _25603)).
Proof. exact (MK_COMB (@lem1651832 _25602 _25604 _25603) (@lem1651875 _25602 _25604 _25603)). Qed.
Lemma lem1651878 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1651879 (x : Prop) : (x = x) = True.
Proof. exact (@lem1651878 Prop x). Qed.
Lemma lem1651880 (_25602 : nat) (_25604 : real) (_25603 : real) : ((term168 _25602 _25604 _25603) = (term168 _25602 _25604 _25603)) = True.
Proof. exact (@lem1651879 (term168 _25602 _25604 _25603)). Qed.
Lemma lem1651881 (_25603 : real) (_25604 : real) (_25602 : nat) : ((term144 _25603 _25604 _25602) = (term163 _25603 _25604 _25602)) = True.
Proof. exact (TRANS (@lem1651876 _25602 _25604 _25603) (@lem1651880 _25602 _25604 _25603)). Qed.
Lemma lem1651882 (_25603 : real) (_25604 : real) (_25602 : nat) : True = ((term144 _25603 _25604 _25602) = (term163 _25603 _25604 _25602)).
Proof. exact (SYM (@lem1651881 _25603 _25604 _25602)). Qed.
Lemma lem1651883 (_25603 : real) (_25604 : real) (_25602 : nat) : (term144 _25603 _25604 _25602) = (term163 _25603 _25604 _25602).
Proof. exact (EQ_MP (@lem1651882 _25603 _25604 _25602) (@lem0)). Qed.
Lemma lem1651884 (_25603 : real) (_25604 : real) (_25602 : nat) (h1 : term17) : term163 _25603 _25604 _25602.
Proof. exact (EQ_MP (@lem1651883 _25603 _25604 _25602) (@lem1651724 _25603 _25604 _25602 h1)). Qed.
Lemma lem1651886 (b : Prop) (a : Prop) : (a \/ b) = (term152 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1651887 (_25602 : nat) (_25603 : real) (_25604 : real) : (term163 _25603 _25604 _25602) = (term171 _25602 _25603 _25604).
Proof. exact (@lem1651886 (term164 _25603 _25604 _25602) (term29 _25603 _25604)). Qed.
Lemma lem1651889 (a : Prop) (b : Prop) : (term172 a b) = (term173 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1651890 (_25603 : real) (_25604 : real) (_25602 : nat) : (term174 _25603 _25604 _25602) = (term175 _25603 _25604 _25602).
Proof. exact (@lem1651889 (term145 _25603) (term129 _25603 _25604 _25602)). Qed.
Lemma lem1651892 (a : Prop) : (term154 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1651893 (_25603 : real) : (term176 _25603) = (term128 _25603).
Proof. exact (@lem1651892 (term128 _25603)). Qed.
Lemma lem1651894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1651895 (_25603 : real) : (term177 _25603) = (term178 _25603).
Proof. exact (MK_COMB (@lem1651894) (@lem1651893 _25603)). Qed.
Lemma lem1651896 (_25603 : real) (_25604 : real) (_25602 : nat) : (term160 _25603 _25604 _25602) = (term160 _25603 _25604 _25602).
Proof. exact (eq_refl (term160 _25603 _25604 _25602)). Qed.
Lemma lem1651897 (_25603 : real) (_25604 : real) (_25602 : nat) : (term175 _25603 _25604 _25602) = (term179 _25603 _25604 _25602).
Proof. exact (MK_COMB (@lem1651895 _25603) (@lem1651896 _25603 _25604 _25602)). Qed.
Lemma lem1651898 (_25603 : real) (_25604 : real) (_25602 : nat) : (term174 _25603 _25604 _25602) = (term179 _25603 _25604 _25602).
Proof. exact (TRANS (@lem1651890 _25603 _25604 _25602) (@lem1651897 _25603 _25604 _25602)). Qed.
Lemma lem1651899 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1651900 (_25603 : real) (_25604 : real) (_25602 : nat) : (term180 _25603 _25604 _25602) = (term181 _25603 _25604 _25602).
Proof. exact (MK_COMB (@lem1651899) (@lem1651898 _25603 _25604 _25602)). Qed.
Lemma lem1651901 (_25603 : real) (_25604 : real) : (term29 _25603 _25604) = (term29 _25603 _25604).
Proof. exact (eq_refl (term29 _25603 _25604)). Qed.
Lemma lem1651902 (_25602 : nat) (_25603 : real) (_25604 : real) : (term171 _25602 _25603 _25604) = (term182 _25602 _25603 _25604).
Proof. exact (MK_COMB (@lem1651900 _25603 _25604 _25602) (@lem1651901 _25603 _25604)). Qed.
Lemma lem1651903 (_25602 : nat) (_25603 : real) (_25604 : real) : (term163 _25603 _25604 _25602) = (term182 _25602 _25603 _25604).
Proof. exact (TRANS (@lem1651887 _25602 _25603 _25604) (@lem1651902 _25602 _25603 _25604)). Qed.
Lemma lem1651905 (n : nat) (x : real) (y : real) (h1 : term33) (h2 : term41 n x y) : term179 y x n.
Proof. exact (conj (@lem1651749 n x y h2) (@lem1651779 n x y h1 h2)). Qed.
Lemma lem1651907 (_25602 : nat) (_25603 : real) (_25604 : real) (h1 : term17) : term182 _25602 _25603 _25604.
Proof. exact (EQ_MP (@lem1651903 _25602 _25603 _25604) (@lem1651884 _25603 _25604 _25602 h1)). Qed.
Lemma lem1651908 (n : nat) (y : real) (x : real) (h1 : term17) : term182 n y x.
Proof. exact (@lem1651907 n y x h1). Qed.
Lemma lem1651911 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : term29 y x.
Proof. exact (@lem1651908 n y x h1 (@lem1651905 n x y h2 h3)). Qed.
Lemma lem1651912 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : term183 y x.
Proof. exact (fun h0 : real_le y x => @lem1651911 n x y h1 h2 h3). Qed.
Lemma lem1651914 (p : Prop) : (term162 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1651915 (y : real) (x : real) : (term183 y x) = (term29 y x).
Proof. exact (@lem1651914 (real_le y x)). Qed.
Lemma lem1651916 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : term29 y x.
Proof. exact (EQ_MP (@lem1651915 y x) (@lem1651912 n x y h1 h2 h3)). Qed.
Lemma lem1651927 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1651928 (_25608 : real) (_25607 : real) : (term184 _25607 _25608) = (term71 _25608 _25607).
Proof. exact (@lem1651927 (real_le _25607 _25608) (real_lt _25608 _25607)). Qed.
Lemma lem1651934 (_25608 : real) (_25607 : real) : (term185 _25608 _25607) = (term185 _25608 _25607).
Proof. exact (eq_refl (term185 _25608 _25607)). Qed.
Lemma lem1651935 (_25608 : real) (_25607 : real) : ((term71 _25608 _25607) = (term184 _25607 _25608)) = ((term71 _25608 _25607) = (term71 _25608 _25607)).
Proof. exact (MK_COMB (@lem1651934 _25608 _25607) (@lem1651928 _25608 _25607)). Qed.
Lemma lem1651937 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1651938 (x : Prop) : (x = x) = True.
Proof. exact (@lem1651937 Prop x). Qed.
Lemma lem1651939 (_25608 : real) (_25607 : real) : ((term71 _25608 _25607) = (term71 _25608 _25607)) = True.
Proof. exact (@lem1651938 (term71 _25608 _25607)). Qed.
Lemma lem1651940 (_25607 : real) (_25608 : real) : ((term71 _25608 _25607) = (term184 _25607 _25608)) = True.
Proof. exact (TRANS (@lem1651935 _25608 _25607) (@lem1651939 _25608 _25607)). Qed.
Lemma lem1651941 (_25607 : real) (_25608 : real) : True = ((term71 _25608 _25607) = (term184 _25607 _25608)).
Proof. exact (SYM (@lem1651940 _25607 _25608)). Qed.
Lemma lem1651942 (_25607 : real) (_25608 : real) : (term71 _25608 _25607) = (term184 _25607 _25608).
Proof. exact (EQ_MP (@lem1651941 _25607 _25608) (@lem0)). Qed.
Lemma lem1651943 (_25607 : real) (_25608 : real) (h1 : term33) : term184 _25607 _25608.
Proof. exact (EQ_MP (@lem1651942 _25607 _25608) (@lem1651742 _25608 _25607 h1)). Qed.
Lemma lem1651945 (b : Prop) (a : Prop) : (a \/ b) = (term152 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1651948 (_25608 : real) (_25607 : real) : (term184 _25607 _25608) = (term186 _25608 _25607).
Proof. exact (@lem1651945 (real_le _25607 _25608) (real_lt _25608 _25607)). Qed.
Lemma lem1651951 (_25608 : real) (_25607 : real) (h1 : term33) : term186 _25608 _25607.
Proof. exact (EQ_MP (@lem1651948 _25608 _25607) (@lem1651943 _25607 _25608 h1)). Qed.
Lemma lem1651952 (x : real) (y : real) (h1 : term33) : term186 x y.
Proof. exact (@lem1651951 x y h1). Qed.
Lemma lem1651955 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : real_lt x y.
Proof. exact (@lem1651952 x y h2 (@lem1651916 n x y h1 h2 h3)). Qed.
Lemma lem1651956 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : term187 x y.
Proof. exact (fun h0 : term146 x y => @lem1651955 n x y h1 h2 h3). Qed.
Lemma lem1651958 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1651959 (x : real) (y : real) : (term187 x y) = (real_lt x y).
Proof. exact (@lem1651958 (real_lt x y)). Qed.
Lemma lem1651960 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : real_lt x y.
Proof. exact (EQ_MP (@lem1651959 x y) (@lem1651956 n x y h1 h2 h3)). Qed.
Lemma lem1651963 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1651965 (x : real) (y : real) : (term146 x y) = (term188 x y).
Proof. exact (@lem1651963 (real_lt x y)). Qed.
Lemma lem1651968 (n : nat) (x : real) (y : real) (h1 : term41 n x y) : term188 x y.
Proof. exact (EQ_MP (@lem1651965 x y) (@lem1651726 n x y h1)). Qed.
Lemma lem1651971 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : False.
Proof. exact (@lem1651968 n x y h3 (@lem1651960 n x y h1 h2 h3)). Qed.
Lemma lem1651972 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : term189.
Proof. exact (fun h0 : ~ False => @lem1651971 n x y h1 h2 h3). Qed.
Lemma lem1651974 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1651975 : term189 = False.
Proof. exact (@lem1651974 False). Qed.
Lemma lem1651976 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : False.
Proof. exact (EQ_MP (@lem1651975) (@lem1651972 n x y h1 h2 h3)). Qed.
Lemma lem1651977 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : (term41 n x y) = False.
Proof. exact (prop_ext (fun h4 : term41 n x y => @lem1651976 n x y h1 h2 h3) (fun h4 : False => @lem1651616 n x y h3)). Qed.
Lemma lem1651978 (n : nat) (x : real) (y : real) (h1 : term17) (h2 : term33) (h3 : term41 n x y) : False.
Proof. exact (EQ_MP (@lem1651977 n x y h1 h2 h3) (@lem1651616 n x y h3)). Qed.
Lemma lem1651979 (n : nat) (x : real) (h1 : term17) (h2 : term33) (h3 : term51 n x) : False.
Proof. exact (ex_elim (@lem1651486 n x h3) (fun y : real => fun h0 : term50 n x y => @lem1651978 n x y h1 h2 h0)). Qed.
Lemma lem1651980 (n : nat) (h1 : term17) (h2 : term33) (h3 : term58 n) : False.
Proof. exact (ex_elim (@lem1651485 n h3) (fun x : real => fun h0 : term57 n x => @lem1651979 n x h1 h2 h0)). Qed.
Lemma lem1651981 (h1 : term17) (h2 : term33) (h3 : term10) : False.
Proof. exact (ex_elim (@lem1651112 h3) (fun n : nat => fun h0 : term65 n => @lem1651980 n h1 h2 h0)). Qed.
Lemma lem1651982 (h1 : term33) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1651981 h0 h1 h2). Qed.
Lemma lem1651983 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1651984 (h1 : term33) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem1651983) (@lem1651982 h1 h2)). Qed.
Lemma lem1651985 (h1 : term10) : term20.
Proof. exact (fun h0 : term33 => @lem1651984 h0 h1). Qed.
Lemma lem1651986 : term22.
Proof. exact (fun h0 : term10 => @lem1651985 h0). Qed.
Lemma lem1651987 : term11.
Proof. exact (EQ_MP (@lem1651007) (@lem1651986)). Qed.
Lemma lem1651989 : term11.
Proof. exact (@lem1650825 (@lem1651987)). Qed.
Lemma lem1651990 (h1 : term10) : term19.
Proof. exact (@lem1651989 (@lem1650810 h1)). Qed.
Lemma lem1651991 (h1 : term10) : term15.
Proof. exact (@lem1651990 h1 (@lem1495933)). Qed.
Lemma lem1651992 (h1 : term10) : False.
Proof. exact (@lem1651991 h1 (@lem1636714)). Qed.
Lemma lem1651993 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1651992 h1) (fun h2 : False => @lem1650810 h1)). Qed.
Lemma lem1651994 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1651993 h1) (@lem1650810 h1)). Qed.
Lemma lem1651995 : term9.
Proof. exact (fun h0 : term10 => @lem1651994 h0). Qed.
Lemma lem1651996 : term8.
Proof. exact (EQ_MP (@lem1650809) (@lem1651995)). Qed.
