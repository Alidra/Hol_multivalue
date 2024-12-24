Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_LMUL_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_LE_RMUL_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338712_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm19490_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1600753 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1600754 : term1 = term2.
Proof. exact (@lem1600753 term1). Qed.
Lemma lem1600755 : term2 = term1.
Proof. exact (SYM (@lem1600754)). Qed.
Lemma lem1600756 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1600759 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1600760 : term5.
Proof. exact (fun h0 : term4 => @lem1600759 h0). Qed.
Lemma lem1600761 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1600762 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1600763 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1600761 h2 (@lem1600762 h1)). Qed.
Lemma lem1600764 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1600763 h1 h0). Qed.
Lemma lem1600765 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1600766 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1600764 h1 (@lem1600765 h2)). Qed.
Lemma lem1600767 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1600766 h0 h1). Qed.
Lemma lem1600768 : term7.
Proof. exact (fun h0 : term5 => @lem1600767 h0). Qed.
Lemma lem1600771 : term5.
Proof. exact (@lem1600768 (@lem1600760)). Qed.
Lemma lem1600799 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1600800 : term8 = term9.
Proof. exact (@lem1600799 term10). Qed.
Lemma lem1600815 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1600816 : term12 = term13.
Proof. exact (MK_COMB (@lem1600815) (@lem1600800)). Qed.
Lemma lem1600819 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1600826 : term4 = term15.
Proof. exact (MK_COMB (@lem1600819) (@lem1600816)). Qed.
Lemma lem1600835 (z : real) (x : real) (y : real) : (term16 z x y) = (term16 z x y).
Proof. exact (eq_refl (term16 z x y)). Qed.
Lemma lem1600836 (x : real) (y : real) : (term17 x y) = (term17 x y).
Proof. exact (fun_ext (fun z : real => @lem1600835 z x y)). Qed.
Lemma lem1600837 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600838 (x : real) (y : real) : (term18 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem1600837) (@lem1600836 x y)). Qed.
Lemma lem1600839 (x : real) : (term19 x) = (term19 x).
Proof. exact (fun_ext (fun y : real => @lem1600838 x y)). Qed.
Lemma lem1600840 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600841 (x : real) : (term20 x) = (term20 x).
Proof. exact (MK_COMB (@lem1600840) (@lem1600839 x)). Qed.
Lemma lem1600842 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1600841 x)). Qed.
Lemma lem1600843 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600844 : term10 = term10.
Proof. exact (MK_COMB (@lem1600843) (@lem1600842)). Qed.
Lemma lem1600845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1600846 : term9 = term9.
Proof. exact (MK_COMB (@lem1600845) (@lem1600844)). Qed.
Lemma lem1600847 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1600848 (x : real) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1600847 y x)). Qed.
Lemma lem1600849 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600850 (x : real) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem1600849) (@lem1600848 x)). Qed.
Lemma lem1600851 : term24 = term24.
Proof. exact (fun_ext (fun x : real => @lem1600850 x)). Qed.
Lemma lem1600852 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600853 : term25 = term25.
Proof. exact (MK_COMB (@lem1600852) (@lem1600851)). Qed.
Lemma lem1600854 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1600855 : term11 = term11.
Proof. exact (MK_COMB (@lem1600854) (@lem1600853)). Qed.
Lemma lem1600856 : term13 = term13.
Proof. exact (MK_COMB (@lem1600855) (@lem1600846)). Qed.
Lemma lem1600865 (z : real) (x : real) (y : real) : (term26 z x y) = (term26 z x y).
Proof. exact (eq_refl (term26 z x y)). Qed.
Lemma lem1600866 (x : real) (y : real) : (term27 x y) = (term27 x y).
Proof. exact (fun_ext (fun z : real => @lem1600865 z x y)). Qed.
Lemma lem1600867 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600868 (x : real) (y : real) : (term28 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1600867) (@lem1600866 x y)). Qed.
Lemma lem1600869 (x : real) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem1600868 x y)). Qed.
Lemma lem1600870 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600871 (x : real) : (term30 x) = (term30 x).
Proof. exact (MK_COMB (@lem1600870) (@lem1600869 x)). Qed.
Lemma lem1600872 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1600871 x)). Qed.
Lemma lem1600873 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600874 : term1 = term1.
Proof. exact (MK_COMB (@lem1600873) (@lem1600872)). Qed.
Lemma lem1600875 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1600876 : term3 = term3.
Proof. exact (MK_COMB (@lem1600875) (@lem1600874)). Qed.
Lemma lem1600877 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1600878 : term14 = term14.
Proof. exact (MK_COMB (@lem1600877) (@lem1600876)). Qed.
Lemma lem1600879 : term15 = term15.
Proof. exact (MK_COMB (@lem1600878) (@lem1600856)). Qed.
Lemma lem1600938 : term4 = term15.
Proof. exact (TRANS (@lem1600826) (@lem1600879)). Qed.
Lemma lem1600939 : term15 = term4.
Proof. exact (SYM (@lem1600938)). Qed.
Lemma lem1600940 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1600941 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem1600942 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1600958 (z : real) (x : real) (y : real) : (term32 z x y) = (term33 z x y).
Proof. exact (@lem17646 (term34 x z y) (real_le x y)). Qed.
Lemma lem1600960 (z : real) : (term35 z) = (term35 z).
Proof. exact (eq_refl (term35 z)). Qed.
Lemma lem1600961 (z : real) (x : real) (y : real) : (term36 z x y) = (term37 z x y).
Proof. exact (MK_COMB (@lem1600960 z) (@lem1600958 z x y)). Qed.
Lemma lem1600962 (z : real) (x : real) (y : real) : (term38 z x y) = (term36 z x y).
Proof. exact (@lem17362 (term39 z) ((term34 x z y) = (real_le x y))). Qed.
Lemma lem1600963 (z : real) (x : real) (y : real) : (term38 z x y) = (term37 z x y).
Proof. exact (TRANS (@lem1600962 z x y) (@lem1600961 z x y)). Qed.
Lemma lem1600964 (P : real -> Prop) : (term40 P) = (term41 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1600965 (x : real) (y : real) : (term42 x y) = (term43 x y).
Proof. exact (@lem1600964 (term27 x y)). Qed.
Lemma lem1600966 (z : real) (x : real) (y : real) : (term44 x y z) = (term26 z x y).
Proof. exact (eq_refl (term44 x y z)). Qed.
Lemma lem1600967 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1600968 (z : real) (x : real) (y : real) : (term45 x y z) = (term38 z x y).
Proof. exact (MK_COMB (@lem1600967) (@lem1600966 z x y)). Qed.
Lemma lem1600969 (z : real) (x : real) (y : real) : (term45 x y z) = (term37 z x y).
Proof. exact (TRANS (@lem1600968 z x y) (@lem1600963 z x y)). Qed.
Lemma lem1600970 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (fun_ext (fun z : real => @lem1600969 z x y)). Qed.
Lemma lem1600971 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1600972 (x : real) (y : real) : (term43 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1600971) (@lem1600970 x y)). Qed.
Lemma lem1600973 (x : real) (y : real) : (term42 x y) = (term48 x y).
Proof. exact (TRANS (@lem1600965 x y) (@lem1600972 x y)). Qed.
Lemma lem1600974 (P : real -> Prop) : (term40 P) = (term41 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1600975 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1600974 (term29 x)). Qed.
Lemma lem1600976 (x : real) (y : real) : (term51 x y) = (term28 x y).
Proof. exact (eq_refl (term51 x y)). Qed.
Lemma lem1600977 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1600978 (x : real) (y : real) : (term52 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1600977) (@lem1600976 x y)). Qed.
Lemma lem1600979 (x : real) (y : real) : (term52 x y) = (term48 x y).
Proof. exact (TRANS (@lem1600978 x y) (@lem1600973 x y)). Qed.
Lemma lem1600980 (x : real) : (term53 x) = (term54 x).
Proof. exact (fun_ext (fun y : real => @lem1600979 x y)). Qed.
Lemma lem1600981 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1600982 (x : real) : (term50 x) = (term55 x).
Proof. exact (MK_COMB (@lem1600981) (@lem1600980 x)). Qed.
Lemma lem1600983 (x : real) : (term49 x) = (term55 x).
Proof. exact (TRANS (@lem1600975 x) (@lem1600982 x)). Qed.
Lemma lem1600984 (P : real -> Prop) : (term40 P) = (term41 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1600985 : term3 = term56.
Proof. exact (@lem1600984 term31). Qed.
Lemma lem1600986 (x : real) : (term57 x) = (term30 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1600987 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1600988 (x : real) : (term58 x) = (term49 x).
Proof. exact (MK_COMB (@lem1600987) (@lem1600986 x)). Qed.
Lemma lem1600989 (x : real) : (term58 x) = (term55 x).
Proof. exact (TRANS (@lem1600988 x) (@lem1600983 x)). Qed.
Lemma lem1600990 : term59 = term60.
Proof. exact (fun_ext (fun x : real => @lem1600989 x)). Qed.
Lemma lem1600991 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1600992 : term56 = term61.
Proof. exact (MK_COMB (@lem1600991) (@lem1600990)). Qed.
Lemma lem1601053 : term3 = term61.
Proof. exact (TRANS (@lem1600985) (@lem1600992)). Qed.
Lemma lem1601054 (h1 : term3) : term61.
Proof. exact (EQ_MP (@lem1601053) (@lem1600940 h1)). Qed.
Lemma lem1601055 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1601056 (x : real) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1601055 y x)). Qed.
Lemma lem1601057 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601058 (x : real) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem1601057) (@lem1601056 x)). Qed.
Lemma lem1601059 : term24 = term24.
Proof. exact (fun_ext (fun x : real => @lem1601058 x)). Qed.
Lemma lem1601060 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601073 : term25 = term25.
Proof. exact (MK_COMB (@lem1601060) (@lem1601059)). Qed.
Lemma lem1601074 (h1 : term25) : term25.
Proof. exact (EQ_MP (@lem1601073) (@lem1600941 h1)). Qed.
Lemma lem1601090 (z : real) (x : real) (y : real) : ((term62 x y z) = (real_le x y)) = (term63 z x y).
Proof. exact (@lem17784 (term62 x y z) (real_le x y)). Qed.
Lemma lem1601092 (z : real) : (term64 z) = (term64 z).
Proof. exact (eq_refl (term64 z)). Qed.
Lemma lem1601093 (z : real) (x : real) (y : real) : (term65 z x y) = (term66 z x y).
Proof. exact (MK_COMB (@lem1601092 z) (@lem1601090 z x y)). Qed.
Lemma lem1601094 (z : real) (x : real) (y : real) : (term16 z x y) = (term65 z x y).
Proof. exact (@lem17265 (term39 z) ((term62 x y z) = (real_le x y))). Qed.
Lemma lem1601095 (z : real) (x : real) (y : real) : (term16 z x y) = (term66 z x y).
Proof. exact (TRANS (@lem1601094 z x y) (@lem1601093 z x y)). Qed.
Lemma lem1601096 (x : real) (y : real) : (term17 x y) = (term67 x y).
Proof. exact (fun_ext (fun z : real => @lem1601095 z x y)). Qed.
Lemma lem1601097 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601098 (x : real) (y : real) : (term18 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1601097) (@lem1601096 x y)). Qed.
Lemma lem1601099 (x : real) : (term19 x) = (term69 x).
Proof. exact (fun_ext (fun y : real => @lem1601098 x y)). Qed.
Lemma lem1601100 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601101 (x : real) : (term20 x) = (term70 x).
Proof. exact (MK_COMB (@lem1601100) (@lem1601099 x)). Qed.
Lemma lem1601102 : term21 = term71.
Proof. exact (fun_ext (fun x : real => @lem1601101 x)). Qed.
Lemma lem1601103 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601164 : term10 = term72.
Proof. exact (MK_COMB (@lem1601103) (@lem1601102)). Qed.
Lemma lem1601165 (h1 : term10) : term72.
Proof. exact (EQ_MP (@lem1601164) (@lem1600942 h1)). Qed.
Lemma lem1601166 (x : real) (h1 : term55 x) : term55 x.
Proof. exact (h1). Qed.
Lemma lem1601167 (x : real) (y : real) (h1 : term48 x y) : term48 x y.
Proof. exact (h1). Qed.
Lemma lem1601181 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1601182 (x : real) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1601181 y x)). Qed.
Lemma lem1601183 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601184 (x : real) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem1601183) (@lem1601182 x)). Qed.
Lemma lem1601185 : term24 = term24.
Proof. exact (fun_ext (fun x : real => @lem1601184 x)). Qed.
Lemma lem1601186 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601187 : term25 = term25.
Proof. exact (MK_COMB (@lem1601186) (@lem1601185)). Qed.
Lemma lem1601188 (h1 : term25) : term25.
Proof. exact (EQ_MP (@lem1601187) (@lem1601074 h1)). Qed.
Lemma lem1601251 (z : real) (x : real) (y : real) : (term66 z x y) = (term66 z x y).
Proof. exact (eq_refl (term66 z x y)). Qed.
Lemma lem1601252 (x : real) (y : real) : (term67 x y) = (term67 x y).
Proof. exact (fun_ext (fun z : real => @lem1601251 z x y)). Qed.
Lemma lem1601253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601254 (x : real) (y : real) : (term68 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1601253) (@lem1601252 x y)). Qed.
Lemma lem1601255 (x : real) : (term69 x) = (term69 x).
Proof. exact (fun_ext (fun y : real => @lem1601254 x y)). Qed.
Lemma lem1601256 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601257 (x : real) : (term70 x) = (term70 x).
Proof. exact (MK_COMB (@lem1601256) (@lem1601255 x)). Qed.
Lemma lem1601258 : term71 = term71.
Proof. exact (fun_ext (fun x : real => @lem1601257 x)). Qed.
Lemma lem1601259 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601260 : term72 = term72.
Proof. exact (MK_COMB (@lem1601259) (@lem1601258)). Qed.
Lemma lem1601261 (h1 : term10) : term72.
Proof. exact (EQ_MP (@lem1601260) (@lem1601165 h1)). Qed.
Lemma lem1601323 (z : real) (x : real) (y : real) (h1 : term37 z x y) : term37 z x y.
Proof. exact (h1). Qed.
Lemma lem1601324 (z : real) (x : real) (y : real) (h1 : term37 z x y) : term33 z x y.
Proof. exact (proj2 (@lem1601323 z x y h1)). Qed.
Lemma lem1601326 (z : real) (x : real) (y : real) (h1 : term73 z x y) : term73 z x y.
Proof. exact (h1). Qed.
Lemma lem1601327 (z : real) (x : real) (y : real) (h1 : term74 z x y) : term74 z x y.
Proof. exact (h1). Qed.
Lemma lem1601333 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1601334 (x : real) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1601333 y x)). Qed.
Lemma lem1601335 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601336 (x : real) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem1601335) (@lem1601334 x)). Qed.
Lemma lem1601337 : term24 = term24.
Proof. exact (fun_ext (fun x : real => @lem1601336 x)). Qed.
Lemma lem1601338 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601340 : term25 = term25.
Proof. exact (MK_COMB (@lem1601338) (@lem1601337)). Qed.
Lemma lem1601341 (h1 : term25) : term25.
Proof. exact (EQ_MP (@lem1601340) (@lem1601188 h1)). Qed.
Lemma lem1601371 (z : real) (x : real) (y : real) : (term66 z x y) = (term75 z x y).
Proof. exact (@lem19490 (term76 z x y) (term77 z) (term78 z x y)). Qed.
Lemma lem1601372 (x : real) (y : real) : (term67 x y) = (term79 x y).
Proof. exact (fun_ext (fun z : real => @lem1601371 z x y)). Qed.
Lemma lem1601373 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601374 (x : real) (y : real) : (term68 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1601373) (@lem1601372 x y)). Qed.
Lemma lem1601375 (x : real) : (term69 x) = (term81 x).
Proof. exact (fun_ext (fun y : real => @lem1601374 x y)). Qed.
Lemma lem1601376 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601377 (x : real) : (term70 x) = (term82 x).
Proof. exact (MK_COMB (@lem1601376) (@lem1601375 x)). Qed.
Lemma lem1601378 : term71 = term83.
Proof. exact (fun_ext (fun x : real => @lem1601377 x)). Qed.
Lemma lem1601379 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601381 : term72 = term84.
Proof. exact (MK_COMB (@lem1601379) (@lem1601378)). Qed.
Lemma lem1601382 (h1 : term10) : term84.
Proof. exact (EQ_MP (@lem1601381) (@lem1601261 h1)). Qed.
Lemma lem1601396 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1601397 (x : real) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1601396 y x)). Qed.
Lemma lem1601398 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601399 (x : real) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem1601398) (@lem1601397 x)). Qed.
Lemma lem1601400 : term24 = term24.
Proof. exact (fun_ext (fun x : real => @lem1601399 x)). Qed.
Lemma lem1601401 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601403 : term25 = term25.
Proof. exact (MK_COMB (@lem1601401) (@lem1601400)). Qed.
Lemma lem1601404 (h1 : term25) : term25.
Proof. exact (EQ_MP (@lem1601403) (@lem1601188 h1)). Qed.
Lemma lem1601434 (z : real) (x : real) (y : real) : (term66 z x y) = (term75 z x y).
Proof. exact (@lem19490 (term76 z x y) (term77 z) (term78 z x y)). Qed.
Lemma lem1601435 (x : real) (y : real) : (term67 x y) = (term79 x y).
Proof. exact (fun_ext (fun z : real => @lem1601434 z x y)). Qed.
Lemma lem1601436 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601437 (x : real) (y : real) : (term68 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1601436) (@lem1601435 x y)). Qed.
Lemma lem1601438 (x : real) : (term69 x) = (term81 x).
Proof. exact (fun_ext (fun y : real => @lem1601437 x y)). Qed.
Lemma lem1601439 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601440 (x : real) : (term70 x) = (term82 x).
Proof. exact (MK_COMB (@lem1601439) (@lem1601438 x)). Qed.
Lemma lem1601441 : term71 = term83.
Proof. exact (fun_ext (fun x : real => @lem1601440 x)). Qed.
Lemma lem1601442 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1601444 : term72 = term84.
Proof. exact (MK_COMB (@lem1601442) (@lem1601441)). Qed.
Lemma lem1601445 (h1 : term10) : term84.
Proof. exact (EQ_MP (@lem1601444) (@lem1601261 h1)). Qed.
Lemma lem1601458 (_25251 : real) (h1 : term25) : term85 _25251.
Proof. exact (@lem1601341 h1 _25251). Qed.
Lemma lem1601459 (_25251 : real) : (term85 _25251) = (term23 _25251).
Proof. exact (eq_refl (term85 _25251)). Qed.
Lemma lem1601460 (_25251 : real) (h1 : term25) : term23 _25251.
Proof. exact (EQ_MP (@lem1601459 _25251) (@lem1601458 _25251 h1)). Qed.
Lemma lem1601461 (_25251 : real) (_25252 : real) (h1 : term25) : term86 _25251 _25252.
Proof. exact (@lem1601460 _25251 h1 _25252). Qed.
Lemma lem1601462 (_25252 : real) (_25251 : real) : (term86 _25251 _25252) = ((real_mul _25251 _25252) = (real_mul _25252 _25251)).
Proof. exact (eq_refl (term86 _25251 _25252)). Qed.
Lemma lem1601464 (_25253 : real) (h1 : term10) : term87 _25253.
Proof. exact (@lem1601382 h1 _25253). Qed.
Lemma lem1601465 (_25253 : real) : (term87 _25253) = (term82 _25253).
Proof. exact (eq_refl (term87 _25253)). Qed.
Lemma lem1601466 (_25253 : real) (h1 : term10) : term82 _25253.
Proof. exact (EQ_MP (@lem1601465 _25253) (@lem1601464 _25253 h1)). Qed.
Lemma lem1601467 (_25253 : real) (_25254 : real) (h1 : term10) : term88 _25253 _25254.
Proof. exact (@lem1601466 _25253 h1 _25254). Qed.
Lemma lem1601468 (_25253 : real) (_25254 : real) : (term88 _25253 _25254) = (term80 _25253 _25254).
Proof. exact (eq_refl (term88 _25253 _25254)). Qed.
Lemma lem1601469 (_25253 : real) (_25254 : real) (h1 : term10) : term80 _25253 _25254.
Proof. exact (EQ_MP (@lem1601468 _25253 _25254) (@lem1601467 _25253 _25254 h1)). Qed.
Lemma lem1601470 (_25253 : real) (_25254 : real) (_25255 : real) (h1 : term10) : term89 _25253 _25254 _25255.
Proof. exact (@lem1601469 _25253 _25254 h1 _25255). Qed.
Lemma lem1601471 (_25255 : real) (_25253 : real) (_25254 : real) : (term89 _25253 _25254 _25255) = (term75 _25255 _25253 _25254).
Proof. exact (eq_refl (term89 _25253 _25254 _25255)). Qed.
Lemma lem1601472 (_25255 : real) (_25253 : real) (_25254 : real) (h1 : term10) : term75 _25255 _25253 _25254.
Proof. exact (EQ_MP (@lem1601471 _25255 _25253 _25254) (@lem1601470 _25253 _25254 _25255 h1)). Qed.
Lemma lem1601473 (_25256 : real) (h1 : term25) : term85 _25256.
Proof. exact (@lem1601404 h1 _25256). Qed.
Lemma lem1601474 (_25256 : real) : (term85 _25256) = (term23 _25256).
Proof. exact (eq_refl (term85 _25256)). Qed.
Lemma lem1601475 (_25256 : real) (h1 : term25) : term23 _25256.
Proof. exact (EQ_MP (@lem1601474 _25256) (@lem1601473 _25256 h1)). Qed.
Lemma lem1601476 (_25256 : real) (_25257 : real) (h1 : term25) : term86 _25256 _25257.
Proof. exact (@lem1601475 _25256 h1 _25257). Qed.
Lemma lem1601477 (_25257 : real) (_25256 : real) : (term86 _25256 _25257) = ((real_mul _25256 _25257) = (real_mul _25257 _25256)).
Proof. exact (eq_refl (term86 _25256 _25257)). Qed.
Lemma lem1601479 (_25258 : real) (h1 : term10) : term87 _25258.
Proof. exact (@lem1601445 h1 _25258). Qed.
Lemma lem1601480 (_25258 : real) : (term87 _25258) = (term82 _25258).
Proof. exact (eq_refl (term87 _25258)). Qed.
Lemma lem1601481 (_25258 : real) (h1 : term10) : term82 _25258.
Proof. exact (EQ_MP (@lem1601480 _25258) (@lem1601479 _25258 h1)). Qed.
Lemma lem1601482 (_25258 : real) (_25259 : real) (h1 : term10) : term88 _25258 _25259.
Proof. exact (@lem1601481 _25258 h1 _25259). Qed.
Lemma lem1601483 (_25258 : real) (_25259 : real) : (term88 _25258 _25259) = (term80 _25258 _25259).
Proof. exact (eq_refl (term88 _25258 _25259)). Qed.
Lemma lem1601484 (_25258 : real) (_25259 : real) (h1 : term10) : term80 _25258 _25259.
Proof. exact (EQ_MP (@lem1601483 _25258 _25259) (@lem1601482 _25258 _25259 h1)). Qed.
Lemma lem1601485 (_25258 : real) (_25259 : real) (_25260 : real) (h1 : term10) : term89 _25258 _25259 _25260.
Proof. exact (@lem1601484 _25258 _25259 h1 _25260). Qed.
Lemma lem1601486 (_25260 : real) (_25258 : real) (_25259 : real) : (term89 _25258 _25259 _25260) = (term75 _25260 _25258 _25259).
Proof. exact (eq_refl (term89 _25258 _25259 _25260)). Qed.
Lemma lem1601487 (_25260 : real) (_25258 : real) (_25259 : real) (h1 : term10) : term75 _25260 _25258 _25259.
Proof. exact (EQ_MP (@lem1601486 _25260 _25258 _25259) (@lem1601485 _25258 _25259 _25260 h1)). Qed.
Lemma lem1601499 (z : real) (x : real) (y : real) (h1 : term73 z x y) : term90 x y.
Proof. exact (proj2 (@lem1601326 z x y h1)). Qed.
Lemma lem1601519 (_25255 : real) (_25253 : real) (_25254 : real) (h1 : term10) : term91 _25255 _25253 _25254.
Proof. exact (proj2 (@lem1601472 _25255 _25253 _25254 h1)). Qed.
Lemma lem1601525 (z : real) (x : real) (y : real) (h1 : term74 z x y) : term92 x z y.
Proof. exact (proj1 (@lem1601327 z x y h1)). Qed.
Lemma lem1601537 (_25260 : real) (_25258 : real) (_25259 : real) (h1 : term10) : term93 _25260 _25258 _25259.
Proof. exact (proj1 (@lem1601487 _25260 _25258 _25259 h1)). Qed.
Lemma lem1601548 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1601549 (_25261 : real) (_25263 : real) (h1 : _25261 = _25263) : _25261 = _25263.
Proof. exact (h1). Qed.
Lemma lem1601550 (_25262 : real) (_25264 : real) (h1 : _25262 = _25264) : _25262 = _25264.
Proof. exact (h1). Qed.
Lemma lem1601551 (_25261 : real) (_25263 : real) (h1 : _25261 = _25263) : (real_le _25261) = (real_le _25263).
Proof. exact (MK_COMB (@lem1601548) (@lem1601549 _25261 _25263 h1)). Qed.
Lemma lem1601552 (_25261 : real) (_25263 : real) (_25262 : real) (_25264 : real) (h1 : _25261 = _25263) (h2 : _25262 = _25264) : (real_le _25261 _25262) = (real_le _25263 _25264).
Proof. exact (MK_COMB (@lem1601551 _25261 _25263 h1) (@lem1601550 _25262 _25264 h2)). Qed.
Lemma lem1601554 (b : Prop) (a : Prop) : term94 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1601555 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : term95 _25263 _25264 _25261 _25262.
Proof. exact (@lem1601554 (real_le _25263 _25264) (real_le _25261 _25262)). Qed.
Lemma lem1601556 (_25261 : real) (_25263 : real) (_25262 : real) (_25264 : real) (h1 : _25261 = _25263) (h2 : _25262 = _25264) : term96 _25263 _25264 _25261 _25262.
Proof. exact (@lem1601555 _25263 _25264 _25261 _25262 (@lem1601552 _25261 _25263 _25262 _25264 h1 h2)). Qed.
Lemma lem1601557 (_25264 : real) (_25262 : real) (_25261 : real) (_25263 : real) (h1 : _25261 = _25263) : term97 _25263 _25264 _25261 _25262.
Proof. exact (fun h0 : _25262 = _25264 => @lem1601556 _25261 _25263 _25262 _25264 h1 h0). Qed.
Lemma lem1601559 (a : Prop) (b : Prop) : (a -> b) = (term98 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1601560 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term97 _25263 _25264 _25261 _25262) = (term99 _25263 _25264 _25261 _25262).
Proof. exact (@lem1601559 (_25262 = _25264) (term96 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601561 (_25264 : real) (_25262 : real) (_25261 : real) (_25263 : real) (h1 : _25261 = _25263) : term99 _25263 _25264 _25261 _25262.
Proof. exact (EQ_MP (@lem1601560 _25263 _25264 _25261 _25262) (@lem1601557 _25264 _25262 _25261 _25263 h1)). Qed.
Lemma lem1601562 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : term100 _25263 _25264 _25261 _25262.
Proof. exact (fun h0 : _25261 = _25263 => @lem1601561 _25264 _25262 _25261 _25263 h0). Qed.
Lemma lem1601564 (a : Prop) (b : Prop) : (a -> b) = (term98 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1601565 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term100 _25263 _25264 _25261 _25262) = (term101 _25263 _25264 _25261 _25262).
Proof. exact (@lem1601564 (_25261 = _25263) (term99 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601566 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : term101 _25263 _25264 _25261 _25262.
Proof. exact (EQ_MP (@lem1601565 _25263 _25264 _25261 _25262) (@lem1601562 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601622 (z : real) (x : real) (y : real) (h1 : term37 z x y) : term39 z.
Proof. exact (proj1 (@lem1601323 z x y h1)). Qed.
Lemma lem1601623 (z : real) (x : real) (y : real) (h1 : term37 z x y) : term102 z.
Proof. exact (fun h0 : term77 z => @lem1601622 z x y h1). Qed.
Lemma lem1601625 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1601626 (z : real) : (term102 z) = (term39 z).
Proof. exact (@lem1601625 (term39 z)). Qed.
Lemma lem1601627 (z : real) (x : real) (y : real) (h1 : term37 z x y) : term39 z.
Proof. exact (EQ_MP (@lem1601626 z) (@lem1601623 z x y h1)). Qed.
Lemma lem1601629 (_25252 : real) (_25251 : real) (h1 : term25) : (real_mul _25251 _25252) = (real_mul _25252 _25251).
Proof. exact (EQ_MP (@lem1601462 _25252 _25251) (@lem1601461 _25251 _25252 h1)). Qed.
Lemma lem1601630 (x : real) (z : real) (h1 : term25) : (real_mul z x) = (real_mul x z).
Proof. exact (@lem1601629 x z h1). Qed.
Lemma lem1601631 (x : real) (z : real) (h1 : term25) : term104 x z.
Proof. exact (fun h0 : term105 x z => @lem1601630 x z h1). Qed.
Lemma lem1601633 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1601634 (x : real) (z : real) : (term104 x z) = ((real_mul z x) = (real_mul x z)).
Proof. exact (@lem1601633 ((real_mul z x) = (real_mul x z))). Qed.
Lemma lem1601635 (x : real) (z : real) (h1 : term25) : (real_mul z x) = (real_mul x z).
Proof. exact (EQ_MP (@lem1601634 x z) (@lem1601631 x z h1)). Qed.
Lemma lem1601637 (_25252 : real) (_25251 : real) (h1 : term25) : (real_mul _25251 _25252) = (real_mul _25252 _25251).
Proof. exact (EQ_MP (@lem1601462 _25252 _25251) (@lem1601461 _25251 _25252 h1)). Qed.
Lemma lem1601638 (y : real) (z : real) (h1 : term25) : (real_mul z y) = (real_mul y z).
Proof. exact (@lem1601637 y z h1). Qed.
Lemma lem1601639 (y : real) (z : real) (h1 : term25) : term104 y z.
Proof. exact (fun h0 : term105 y z => @lem1601638 y z h1). Qed.
Lemma lem1601641 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1601642 (y : real) (z : real) : (term104 y z) = ((real_mul z y) = (real_mul y z)).
Proof. exact (@lem1601641 ((real_mul z y) = (real_mul y z))). Qed.
Lemma lem1601643 (y : real) (z : real) (h1 : term25) : (real_mul z y) = (real_mul y z).
Proof. exact (EQ_MP (@lem1601642 y z) (@lem1601639 y z h1)). Qed.
Lemma lem1601645 (z : real) (x : real) (y : real) (h1 : term73 z x y) : term34 x z y.
Proof. exact (proj1 (@lem1601326 z x y h1)). Qed.
Lemma lem1601646 (z : real) (x : real) (y : real) (h1 : term73 z x y) : term106 x z y.
Proof. exact (fun h0 : term92 x z y => @lem1601645 z x y h1). Qed.
Lemma lem1601648 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1601649 (x : real) (z : real) (y : real) : (term106 x z y) = (term34 x z y).
Proof. exact (@lem1601648 (term34 x z y)). Qed.
Lemma lem1601650 (z : real) (x : real) (y : real) (h1 : term73 z x y) : term34 x z y.
Proof. exact (EQ_MP (@lem1601649 x z y) (@lem1601646 z x y h1)). Qed.
Lemma lem1601668 (q : Prop) (p : Prop) (r : Prop) : (term107 p q r) = (term107 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1601669 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term99 _25263 _25264 _25261 _25262) = (term108 _25263 _25264 _25261 _25262).
Proof. exact (@lem1601668 (real_le _25263 _25264) (term109 _25262 _25264) (term90 _25261 _25262)). Qed.
Lemma lem1601687 (_25261 : real) (_25263 : real) : (term110 _25261 _25263) = (term110 _25261 _25263).
Proof. exact (eq_refl (term110 _25261 _25263)). Qed.
Lemma lem1601688 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term101 _25263 _25264 _25261 _25262) = (term111 _25263 _25264 _25261 _25262).
Proof. exact (MK_COMB (@lem1601687 _25261 _25263) (@lem1601669 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601692 (q : Prop) (p : Prop) (r : Prop) : (term107 p q r) = (term107 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1601693 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term111 _25263 _25264 _25261 _25262) = (term112 _25263 _25264 _25261 _25262).
Proof. exact (@lem1601692 (real_le _25263 _25264) (term109 _25261 _25263) (term113 _25264 _25261 _25262)). Qed.
Lemma lem1601723 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term101 _25263 _25264 _25261 _25262) = (term112 _25263 _25264 _25261 _25262).
Proof. exact (TRANS (@lem1601688 _25263 _25264 _25261 _25262) (@lem1601693 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601724 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1601725 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term114 _25263 _25264 _25261 _25262) = (term115 _25263 _25264 _25261 _25262).
Proof. exact (MK_COMB (@lem1601724) (@lem1601723 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601755 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term112 _25263 _25264 _25261 _25262) = (term112 _25263 _25264 _25261 _25262).
Proof. exact (eq_refl (term112 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601756 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : ((term101 _25263 _25264 _25261 _25262) = (term112 _25263 _25264 _25261 _25262)) = ((term112 _25263 _25264 _25261 _25262) = (term112 _25263 _25264 _25261 _25262)).
Proof. exact (MK_COMB (@lem1601725 _25263 _25264 _25261 _25262) (@lem1601755 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601758 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1601759 (x : Prop) : (x = x) = True.
Proof. exact (@lem1601758 Prop x). Qed.
Lemma lem1601760 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : ((term112 _25263 _25264 _25261 _25262) = (term112 _25263 _25264 _25261 _25262)) = True.
Proof. exact (@lem1601759 (term112 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601761 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : ((term101 _25263 _25264 _25261 _25262) = (term112 _25263 _25264 _25261 _25262)) = True.
Proof. exact (TRANS (@lem1601756 _25263 _25264 _25261 _25262) (@lem1601760 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601762 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : True = ((term101 _25263 _25264 _25261 _25262) = (term112 _25263 _25264 _25261 _25262)).
Proof. exact (SYM (@lem1601761 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601763 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term101 _25263 _25264 _25261 _25262) = (term112 _25263 _25264 _25261 _25262).
Proof. exact (EQ_MP (@lem1601762 _25263 _25264 _25261 _25262) (@lem0)). Qed.
Lemma lem1601764 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : term112 _25263 _25264 _25261 _25262.
Proof. exact (EQ_MP (@lem1601763 _25263 _25264 _25261 _25262) (@lem1601566 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601766 (b : Prop) (a : Prop) : (a \/ b) = (term116 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1601767 (_25261 : real) (_25262 : real) (_25263 : real) (_25264 : real) : (term112 _25263 _25264 _25261 _25262) = (term117 _25261 _25262 _25263 _25264).
Proof. exact (@lem1601766 (term118 _25263 _25264 _25261 _25262) (real_le _25263 _25264)). Qed.
Lemma lem1601769 (a : Prop) (b : Prop) : (term119 a b) = (term120 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1601770 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term121 _25263 _25264 _25261 _25262) = (term122 _25263 _25264 _25261 _25262).
Proof. exact (@lem1601769 (term109 _25261 _25263) (term113 _25264 _25261 _25262)). Qed.
Lemma lem1601772 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1601773 (_25261 : real) (_25263 : real) : (term124 _25261 _25263) = (_25261 = _25263).
Proof. exact (@lem1601772 (_25261 = _25263)). Qed.
Lemma lem1601774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1601775 (_25261 : real) (_25263 : real) : (term125 _25261 _25263) = (term126 _25261 _25263).
Proof. exact (MK_COMB (@lem1601774) (@lem1601773 _25261 _25263)). Qed.
Lemma lem1601777 (a : Prop) (b : Prop) : (term119 a b) = (term120 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1601778 (_25264 : real) (_25261 : real) (_25262 : real) : (term127 _25264 _25261 _25262) = (term128 _25264 _25261 _25262).
Proof. exact (@lem1601777 (term109 _25262 _25264) (term90 _25261 _25262)). Qed.
Lemma lem1601780 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1601781 (_25262 : real) (_25264 : real) : (term124 _25262 _25264) = (_25262 = _25264).
Proof. exact (@lem1601780 (_25262 = _25264)). Qed.
Lemma lem1601782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1601783 (_25262 : real) (_25264 : real) : (term125 _25262 _25264) = (term126 _25262 _25264).
Proof. exact (MK_COMB (@lem1601782) (@lem1601781 _25262 _25264)). Qed.
Lemma lem1601785 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1601786 (_25261 : real) (_25262 : real) : (term129 _25261 _25262) = (real_le _25261 _25262).
Proof. exact (@lem1601785 (real_le _25261 _25262)). Qed.
Lemma lem1601787 (_25264 : real) (_25261 : real) (_25262 : real) : (term128 _25264 _25261 _25262) = (term130 _25264 _25261 _25262).
Proof. exact (MK_COMB (@lem1601783 _25262 _25264) (@lem1601786 _25261 _25262)). Qed.
Lemma lem1601788 (_25264 : real) (_25261 : real) (_25262 : real) : (term127 _25264 _25261 _25262) = (term130 _25264 _25261 _25262).
Proof. exact (TRANS (@lem1601778 _25264 _25261 _25262) (@lem1601787 _25264 _25261 _25262)). Qed.
Lemma lem1601789 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term122 _25263 _25264 _25261 _25262) = (term131 _25263 _25264 _25261 _25262).
Proof. exact (MK_COMB (@lem1601775 _25261 _25263) (@lem1601788 _25264 _25261 _25262)). Qed.
Lemma lem1601790 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term121 _25263 _25264 _25261 _25262) = (term131 _25263 _25264 _25261 _25262).
Proof. exact (TRANS (@lem1601770 _25263 _25264 _25261 _25262) (@lem1601789 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601791 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1601792 (_25263 : real) (_25264 : real) (_25261 : real) (_25262 : real) : (term132 _25263 _25264 _25261 _25262) = (term133 _25263 _25264 _25261 _25262).
Proof. exact (MK_COMB (@lem1601791) (@lem1601790 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601793 (_25263 : real) (_25264 : real) : (real_le _25263 _25264) = (real_le _25263 _25264).
Proof. exact (eq_refl (real_le _25263 _25264)). Qed.
Lemma lem1601794 (_25261 : real) (_25262 : real) (_25263 : real) (_25264 : real) : (term117 _25261 _25262 _25263 _25264) = (term134 _25261 _25262 _25263 _25264).
Proof. exact (MK_COMB (@lem1601792 _25263 _25264 _25261 _25262) (@lem1601793 _25263 _25264)). Qed.
Lemma lem1601795 (_25261 : real) (_25262 : real) (_25263 : real) (_25264 : real) : (term112 _25263 _25264 _25261 _25262) = (term134 _25261 _25262 _25263 _25264).
Proof. exact (TRANS (@lem1601767 _25261 _25262 _25263 _25264) (@lem1601794 _25261 _25262 _25263 _25264)). Qed.
Lemma lem1601797 (z : real) (x : real) (y : real) (h1 : term25) (h2 : term73 z x y) : term135 x z y.
Proof. exact (conj (@lem1601643 y z h1) (@lem1601650 z x y h2)). Qed.
Lemma lem1601798 (z : real) (x : real) (y : real) (h1 : term25) (h2 : term73 z x y) : term136 x z y.
Proof. exact (conj (@lem1601635 x z h1) (@lem1601797 z x y h1 h2)). Qed.
Lemma lem1601800 (_25261 : real) (_25262 : real) (_25263 : real) (_25264 : real) : term134 _25261 _25262 _25263 _25264.
Proof. exact (EQ_MP (@lem1601795 _25261 _25262 _25263 _25264) (@lem1601764 _25263 _25264 _25261 _25262)). Qed.
Lemma lem1601801 (x : real) (y : real) (z : real) : term137 x y z.
Proof. exact (@lem1601800 (real_mul z x) (real_mul z y) (real_mul x z) (real_mul y z)). Qed.
Lemma lem1601804 (z : real) (x : real) (y : real) (h1 : term25) (h2 : term73 z x y) : term62 x y z.
Proof. exact (@lem1601801 x y z (@lem1601798 z x y h1 h2)). Qed.
Lemma lem1601805 (z : real) (x : real) (y : real) (h1 : term25) (h2 : term73 z x y) : term138 x y z.
Proof. exact (fun h0 : term139 x y z => @lem1601804 z x y h1 h2). Qed.
Lemma lem1601807 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1601808 (x : real) (y : real) (z : real) : (term138 x y z) = (term62 x y z).
Proof. exact (@lem1601807 (term62 x y z)). Qed.
Lemma lem1601809 (z : real) (x : real) (y : real) (h1 : term25) (h2 : term73 z x y) : term62 x y z.
Proof. exact (EQ_MP (@lem1601808 x y z) (@lem1601805 z x y h1 h2)). Qed.
Lemma lem1601815 (q : Prop) (p : Prop) (r : Prop) : (term107 p q r) = (term107 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1601816 (_25255 : real) (_25253 : real) (_25254 : real) : (term91 _25255 _25253 _25254) = (term140 _25255 _25253 _25254).
Proof. exact (@lem1601815 (term139 _25253 _25254 _25255) (term77 _25255) (real_le _25253 _25254)). Qed.
Lemma lem1601830 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1601831 (_25253 : real) (_25254 : real) (_25255 : real) : (term141 _25255 _25253 _25254) = (term142 _25253 _25254 _25255).
Proof. exact (@lem1601830 (real_le _25253 _25254) (term77 _25255)). Qed.
Lemma lem1601837 (_25253 : real) (_25254 : real) (_25255 : real) : (term143 _25253 _25254 _25255) = (term143 _25253 _25254 _25255).
Proof. exact (eq_refl (term143 _25253 _25254 _25255)). Qed.
Lemma lem1601838 (_25253 : real) (_25254 : real) (_25255 : real) : (term140 _25255 _25253 _25254) = (term144 _25253 _25254 _25255).
Proof. exact (MK_COMB (@lem1601837 _25253 _25254 _25255) (@lem1601831 _25253 _25254 _25255)). Qed.
Lemma lem1601842 (q : Prop) (p : Prop) (r : Prop) : (term107 p q r) = (term107 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1601843 (_25253 : real) (_25254 : real) (_25255 : real) : (term144 _25253 _25254 _25255) = (term145 _25253 _25254 _25255).
Proof. exact (@lem1601842 (real_le _25253 _25254) (term139 _25253 _25254 _25255) (term77 _25255)). Qed.
Lemma lem1601859 (_25253 : real) (_25254 : real) (_25255 : real) : (term140 _25255 _25253 _25254) = (term145 _25253 _25254 _25255).
Proof. exact (TRANS (@lem1601838 _25253 _25254 _25255) (@lem1601843 _25253 _25254 _25255)). Qed.
Lemma lem1601860 (_25253 : real) (_25254 : real) (_25255 : real) : (term91 _25255 _25253 _25254) = (term145 _25253 _25254 _25255).
Proof. exact (TRANS (@lem1601816 _25255 _25253 _25254) (@lem1601859 _25253 _25254 _25255)). Qed.
Lemma lem1601861 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1601862 (_25253 : real) (_25254 : real) (_25255 : real) : (term146 _25255 _25253 _25254) = (term147 _25253 _25254 _25255).
Proof. exact (MK_COMB (@lem1601861) (@lem1601860 _25253 _25254 _25255)). Qed.
Lemma lem1601876 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1601877 (_25253 : real) (_25254 : real) (_25255 : real) : (term148 _25253 _25254 _25255) = (term149 _25253 _25254 _25255).
Proof. exact (@lem1601876 (term139 _25253 _25254 _25255) (term77 _25255)). Qed.
Lemma lem1601883 (_25253 : real) (_25254 : real) : (term150 _25253 _25254) = (term150 _25253 _25254).
Proof. exact (eq_refl (term150 _25253 _25254)). Qed.
Lemma lem1601884 (_25253 : real) (_25254 : real) (_25255 : real) : (term151 _25253 _25254 _25255) = (term145 _25253 _25254 _25255).
Proof. exact (MK_COMB (@lem1601883 _25253 _25254) (@lem1601877 _25253 _25254 _25255)). Qed.
Lemma lem1601895 (_25253 : real) (_25254 : real) (_25255 : real) : ((term91 _25255 _25253 _25254) = (term151 _25253 _25254 _25255)) = ((term145 _25253 _25254 _25255) = (term145 _25253 _25254 _25255)).
Proof. exact (MK_COMB (@lem1601862 _25253 _25254 _25255) (@lem1601884 _25253 _25254 _25255)). Qed.
Lemma lem1601897 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1601898 (x : Prop) : (x = x) = True.
Proof. exact (@lem1601897 Prop x). Qed.
Lemma lem1601899 (_25253 : real) (_25254 : real) (_25255 : real) : ((term145 _25253 _25254 _25255) = (term145 _25253 _25254 _25255)) = True.
Proof. exact (@lem1601898 (term145 _25253 _25254 _25255)). Qed.
Lemma lem1601900 (_25253 : real) (_25254 : real) (_25255 : real) : ((term91 _25255 _25253 _25254) = (term151 _25253 _25254 _25255)) = True.
Proof. exact (TRANS (@lem1601895 _25253 _25254 _25255) (@lem1601899 _25253 _25254 _25255)). Qed.
Lemma lem1601901 (_25253 : real) (_25254 : real) (_25255 : real) : True = ((term91 _25255 _25253 _25254) = (term151 _25253 _25254 _25255)).
Proof. exact (SYM (@lem1601900 _25253 _25254 _25255)). Qed.
Lemma lem1601902 (_25253 : real) (_25254 : real) (_25255 : real) : (term91 _25255 _25253 _25254) = (term151 _25253 _25254 _25255).
Proof. exact (EQ_MP (@lem1601901 _25253 _25254 _25255) (@lem0)). Qed.
Lemma lem1601903 (_25253 : real) (_25254 : real) (_25255 : real) (h1 : term10) : term151 _25253 _25254 _25255.
Proof. exact (EQ_MP (@lem1601902 _25253 _25254 _25255) (@lem1601519 _25255 _25253 _25254 h1)). Qed.
Lemma lem1601905 (b : Prop) (a : Prop) : (a \/ b) = (term116 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1601906 (_25255 : real) (_25253 : real) (_25254 : real) : (term151 _25253 _25254 _25255) = (term152 _25255 _25253 _25254).
Proof. exact (@lem1601905 (term148 _25253 _25254 _25255) (real_le _25253 _25254)). Qed.
Lemma lem1601908 (a : Prop) (b : Prop) : (term119 a b) = (term120 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1601909 (_25253 : real) (_25254 : real) (_25255 : real) : (term153 _25253 _25254 _25255) = (term154 _25253 _25254 _25255).
Proof. exact (@lem1601908 (term77 _25255) (term139 _25253 _25254 _25255)). Qed.
Lemma lem1601911 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1601912 (_25255 : real) : (term155 _25255) = (term39 _25255).
Proof. exact (@lem1601911 (term39 _25255)). Qed.
Lemma lem1601913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1601914 (_25255 : real) : (term156 _25255) = (term35 _25255).
Proof. exact (MK_COMB (@lem1601913) (@lem1601912 _25255)). Qed.
Lemma lem1601916 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1601917 (_25253 : real) (_25254 : real) (_25255 : real) : (term157 _25253 _25254 _25255) = (term62 _25253 _25254 _25255).
Proof. exact (@lem1601916 (term62 _25253 _25254 _25255)). Qed.
Lemma lem1601918 (_25253 : real) (_25254 : real) (_25255 : real) : (term154 _25253 _25254 _25255) = (term158 _25253 _25254 _25255).
Proof. exact (MK_COMB (@lem1601914 _25255) (@lem1601917 _25253 _25254 _25255)). Qed.
Lemma lem1601919 (_25253 : real) (_25254 : real) (_25255 : real) : (term153 _25253 _25254 _25255) = (term158 _25253 _25254 _25255).
Proof. exact (TRANS (@lem1601909 _25253 _25254 _25255) (@lem1601918 _25253 _25254 _25255)). Qed.
Lemma lem1601920 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1601921 (_25253 : real) (_25254 : real) (_25255 : real) : (term159 _25253 _25254 _25255) = (term160 _25253 _25254 _25255).
Proof. exact (MK_COMB (@lem1601920) (@lem1601919 _25253 _25254 _25255)). Qed.
Lemma lem1601922 (_25253 : real) (_25254 : real) : (real_le _25253 _25254) = (real_le _25253 _25254).
Proof. exact (eq_refl (real_le _25253 _25254)). Qed.
Lemma lem1601923 (_25255 : real) (_25253 : real) (_25254 : real) : (term152 _25255 _25253 _25254) = (term161 _25255 _25253 _25254).
Proof. exact (MK_COMB (@lem1601921 _25253 _25254 _25255) (@lem1601922 _25253 _25254)). Qed.
Lemma lem1601924 (_25255 : real) (_25253 : real) (_25254 : real) : (term151 _25253 _25254 _25255) = (term161 _25255 _25253 _25254).
Proof. exact (TRANS (@lem1601906 _25255 _25253 _25254) (@lem1601923 _25255 _25253 _25254)). Qed.
Lemma lem1601926 (z : real) (x : real) (y : real) (h1 : term25) (h2 : term73 z x y) (h3 : term37 z x y) : term158 x y z.
Proof. exact (conj (@lem1601627 z x y h3) (@lem1601809 z x y h1 h2)). Qed.
Lemma lem1601928 (_25255 : real) (_25253 : real) (_25254 : real) (h1 : term10) : term161 _25255 _25253 _25254.
Proof. exact (EQ_MP (@lem1601924 _25255 _25253 _25254) (@lem1601903 _25253 _25254 _25255 h1)). Qed.
Lemma lem1601929 (z : real) (x : real) (y : real) (h1 : term10) : term161 z x y.
Proof. exact (@lem1601928 z x y h1). Qed.
Lemma lem1601932 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term73 z x y) (h4 : term37 z x y) : real_le x y.
Proof. exact (@lem1601929 z x y h1 (@lem1601926 z x y h2 h3 h4)). Qed.
Lemma lem1601933 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term73 z x y) (h4 : term37 z x y) : term162 x y.
Proof. exact (fun h0 : term90 x y => @lem1601932 z x y h1 h2 h3 h4). Qed.
Lemma lem1601935 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1601936 (x : real) (y : real) : (term162 x y) = (real_le x y).
Proof. exact (@lem1601935 (real_le x y)). Qed.
Lemma lem1601937 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term73 z x y) (h4 : term37 z x y) : real_le x y.
Proof. exact (EQ_MP (@lem1601936 x y) (@lem1601933 z x y h1 h2 h3 h4)). Qed.
Lemma lem1601940 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1601942 (x : real) (y : real) : (term90 x y) = (term163 x y).
Proof. exact (@lem1601940 (real_le x y)). Qed.
Lemma lem1601945 (z : real) (x : real) (y : real) (h1 : term73 z x y) : term163 x y.
Proof. exact (EQ_MP (@lem1601942 x y) (@lem1601499 z x y h1)). Qed.
Lemma lem1601948 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term73 z x y) (h4 : term37 z x y) : False.
Proof. exact (@lem1601945 z x y h3 (@lem1601937 z x y h1 h2 h3 h4)). Qed.
Lemma lem1601949 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term73 z x y) (h4 : term37 z x y) : term164.
Proof. exact (fun h0 : ~ False => @lem1601948 z x y h1 h2 h3 h4). Qed.
Lemma lem1601951 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1601952 : term164 = False.
Proof. exact (@lem1601951 False). Qed.
Lemma lem1601953 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term73 z x y) (h4 : term37 z x y) : False.
Proof. exact (EQ_MP (@lem1601952) (@lem1601949 z x y h1 h2 h3 h4)). Qed.
Lemma lem1601954 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1601955 (_25277 : real) (_25279 : real) (h1 : _25277 = _25279) : _25277 = _25279.
Proof. exact (h1). Qed.
Lemma lem1601956 (_25278 : real) (_25280 : real) (h1 : _25278 = _25280) : _25278 = _25280.
Proof. exact (h1). Qed.
Lemma lem1601957 (_25277 : real) (_25279 : real) (h1 : _25277 = _25279) : (real_le _25277) = (real_le _25279).
Proof. exact (MK_COMB (@lem1601954) (@lem1601955 _25277 _25279 h1)). Qed.
Lemma lem1601958 (_25277 : real) (_25279 : real) (_25278 : real) (_25280 : real) (h1 : _25277 = _25279) (h2 : _25278 = _25280) : (real_le _25277 _25278) = (real_le _25279 _25280).
Proof. exact (MK_COMB (@lem1601957 _25277 _25279 h1) (@lem1601956 _25278 _25280 h2)). Qed.
Lemma lem1601960 (b : Prop) (a : Prop) : term94 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1601961 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : term95 _25279 _25280 _25277 _25278.
Proof. exact (@lem1601960 (real_le _25279 _25280) (real_le _25277 _25278)). Qed.
Lemma lem1601962 (_25277 : real) (_25279 : real) (_25278 : real) (_25280 : real) (h1 : _25277 = _25279) (h2 : _25278 = _25280) : term96 _25279 _25280 _25277 _25278.
Proof. exact (@lem1601961 _25279 _25280 _25277 _25278 (@lem1601958 _25277 _25279 _25278 _25280 h1 h2)). Qed.
Lemma lem1601963 (_25280 : real) (_25278 : real) (_25277 : real) (_25279 : real) (h1 : _25277 = _25279) : term97 _25279 _25280 _25277 _25278.
Proof. exact (fun h0 : _25278 = _25280 => @lem1601962 _25277 _25279 _25278 _25280 h1 h0). Qed.
Lemma lem1601965 (a : Prop) (b : Prop) : (a -> b) = (term98 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1601966 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term97 _25279 _25280 _25277 _25278) = (term99 _25279 _25280 _25277 _25278).
Proof. exact (@lem1601965 (_25278 = _25280) (term96 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1601967 (_25280 : real) (_25278 : real) (_25277 : real) (_25279 : real) (h1 : _25277 = _25279) : term99 _25279 _25280 _25277 _25278.
Proof. exact (EQ_MP (@lem1601966 _25279 _25280 _25277 _25278) (@lem1601963 _25280 _25278 _25277 _25279 h1)). Qed.
Lemma lem1601968 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : term100 _25279 _25280 _25277 _25278.
Proof. exact (fun h0 : _25277 = _25279 => @lem1601967 _25280 _25278 _25277 _25279 h0). Qed.
Lemma lem1601970 (a : Prop) (b : Prop) : (a -> b) = (term98 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1601971 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term100 _25279 _25280 _25277 _25278) = (term101 _25279 _25280 _25277 _25278).
Proof. exact (@lem1601970 (_25277 = _25279) (term99 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1601972 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : term101 _25279 _25280 _25277 _25278.
Proof. exact (EQ_MP (@lem1601971 _25279 _25280 _25277 _25278) (@lem1601968 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602028 (_25257 : real) (_25256 : real) (h1 : term25) : (real_mul _25256 _25257) = (real_mul _25257 _25256).
Proof. exact (EQ_MP (@lem1601477 _25257 _25256) (@lem1601476 _25256 _25257 h1)). Qed.
Lemma lem1602029 (z : real) (x : real) (h1 : term25) : (real_mul x z) = (real_mul z x).
Proof. exact (@lem1602028 z x h1). Qed.
Lemma lem1602030 (z : real) (x : real) (h1 : term25) : term104 z x.
Proof. exact (fun h0 : term105 z x => @lem1602029 z x h1). Qed.
Lemma lem1602032 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1602033 (z : real) (x : real) : (term104 z x) = ((real_mul x z) = (real_mul z x)).
Proof. exact (@lem1602032 ((real_mul x z) = (real_mul z x))). Qed.
Lemma lem1602034 (z : real) (x : real) (h1 : term25) : (real_mul x z) = (real_mul z x).
Proof. exact (EQ_MP (@lem1602033 z x) (@lem1602030 z x h1)). Qed.
Lemma lem1602036 (_25257 : real) (_25256 : real) (h1 : term25) : (real_mul _25256 _25257) = (real_mul _25257 _25256).
Proof. exact (EQ_MP (@lem1601477 _25257 _25256) (@lem1601476 _25256 _25257 h1)). Qed.
Lemma lem1602037 (z : real) (y : real) (h1 : term25) : (real_mul y z) = (real_mul z y).
Proof. exact (@lem1602036 z y h1). Qed.
Lemma lem1602038 (z : real) (y : real) (h1 : term25) : term104 z y.
Proof. exact (fun h0 : term105 z y => @lem1602037 z y h1). Qed.
Lemma lem1602040 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1602041 (z : real) (y : real) : (term104 z y) = ((real_mul y z) = (real_mul z y)).
Proof. exact (@lem1602040 ((real_mul y z) = (real_mul z y))). Qed.
Lemma lem1602042 (z : real) (y : real) (h1 : term25) : (real_mul y z) = (real_mul z y).
Proof. exact (EQ_MP (@lem1602041 z y) (@lem1602038 z y h1)). Qed.
Lemma lem1602044 (z : real) (x : real) (y : real) (h1 : term37 z x y) : term39 z.
Proof. exact (proj1 (@lem1601323 z x y h1)). Qed.
Lemma lem1602045 (z : real) (x : real) (y : real) (h1 : term37 z x y) : term102 z.
Proof. exact (fun h0 : term77 z => @lem1602044 z x y h1). Qed.
Lemma lem1602047 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1602048 (z : real) : (term102 z) = (term39 z).
Proof. exact (@lem1602047 (term39 z)). Qed.
Lemma lem1602049 (z : real) (x : real) (y : real) (h1 : term37 z x y) : term39 z.
Proof. exact (EQ_MP (@lem1602048 z) (@lem1602045 z x y h1)). Qed.
Lemma lem1602051 (z : real) (x : real) (y : real) (h1 : term74 z x y) : real_le x y.
Proof. exact (proj2 (@lem1601327 z x y h1)). Qed.
Lemma lem1602052 (z : real) (x : real) (y : real) (h1 : term74 z x y) : term162 x y.
Proof. exact (fun h0 : term90 x y => @lem1602051 z x y h1). Qed.
Lemma lem1602054 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1602055 (x : real) (y : real) : (term162 x y) = (real_le x y).
Proof. exact (@lem1602054 (real_le x y)). Qed.
Lemma lem1602056 (z : real) (x : real) (y : real) (h1 : term74 z x y) : real_le x y.
Proof. exact (EQ_MP (@lem1602055 x y) (@lem1602052 z x y h1)). Qed.
Lemma lem1602062 (q : Prop) (p : Prop) (r : Prop) : (term107 p q r) = (term107 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1602063 (_25260 : real) (_25258 : real) (_25259 : real) : (term93 _25260 _25258 _25259) = (term165 _25260 _25258 _25259).
Proof. exact (@lem1602062 (term62 _25258 _25259 _25260) (term77 _25260) (term90 _25258 _25259)). Qed.
Lemma lem1602077 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1602078 (_25258 : real) (_25259 : real) (_25260 : real) : (term166 _25260 _25258 _25259) = (term167 _25258 _25259 _25260).
Proof. exact (@lem1602077 (term90 _25258 _25259) (term77 _25260)). Qed.
Lemma lem1602084 (_25258 : real) (_25259 : real) (_25260 : real) : (term168 _25258 _25259 _25260) = (term168 _25258 _25259 _25260).
Proof. exact (eq_refl (term168 _25258 _25259 _25260)). Qed.
Lemma lem1602085 (_25258 : real) (_25259 : real) (_25260 : real) : (term165 _25260 _25258 _25259) = (term169 _25258 _25259 _25260).
Proof. exact (MK_COMB (@lem1602084 _25258 _25259 _25260) (@lem1602078 _25258 _25259 _25260)). Qed.
Lemma lem1602096 (_25258 : real) (_25259 : real) (_25260 : real) : (term93 _25260 _25258 _25259) = (term169 _25258 _25259 _25260).
Proof. exact (TRANS (@lem1602063 _25260 _25258 _25259) (@lem1602085 _25258 _25259 _25260)). Qed.
Lemma lem1602097 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1602098 (_25258 : real) (_25259 : real) (_25260 : real) : (term170 _25260 _25258 _25259) = (term171 _25258 _25259 _25260).
Proof. exact (MK_COMB (@lem1602097) (@lem1602096 _25258 _25259 _25260)). Qed.
Lemma lem1602112 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1602113 (_25258 : real) (_25259 : real) (_25260 : real) : (term166 _25260 _25258 _25259) = (term167 _25258 _25259 _25260).
Proof. exact (@lem1602112 (term90 _25258 _25259) (term77 _25260)). Qed.
Lemma lem1602119 (_25258 : real) (_25259 : real) (_25260 : real) : (term168 _25258 _25259 _25260) = (term168 _25258 _25259 _25260).
Proof. exact (eq_refl (term168 _25258 _25259 _25260)). Qed.
Lemma lem1602120 (_25258 : real) (_25259 : real) (_25260 : real) : (term165 _25260 _25258 _25259) = (term169 _25258 _25259 _25260).
Proof. exact (MK_COMB (@lem1602119 _25258 _25259 _25260) (@lem1602113 _25258 _25259 _25260)). Qed.
Lemma lem1602131 (_25258 : real) (_25259 : real) (_25260 : real) : ((term93 _25260 _25258 _25259) = (term165 _25260 _25258 _25259)) = ((term169 _25258 _25259 _25260) = (term169 _25258 _25259 _25260)).
Proof. exact (MK_COMB (@lem1602098 _25258 _25259 _25260) (@lem1602120 _25258 _25259 _25260)). Qed.
Lemma lem1602133 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1602134 (x : Prop) : (x = x) = True.
Proof. exact (@lem1602133 Prop x). Qed.
Lemma lem1602135 (_25258 : real) (_25259 : real) (_25260 : real) : ((term169 _25258 _25259 _25260) = (term169 _25258 _25259 _25260)) = True.
Proof. exact (@lem1602134 (term169 _25258 _25259 _25260)). Qed.
Lemma lem1602136 (_25260 : real) (_25258 : real) (_25259 : real) : ((term93 _25260 _25258 _25259) = (term165 _25260 _25258 _25259)) = True.
Proof. exact (TRANS (@lem1602131 _25258 _25259 _25260) (@lem1602135 _25258 _25259 _25260)). Qed.
Lemma lem1602137 (_25260 : real) (_25258 : real) (_25259 : real) : True = ((term93 _25260 _25258 _25259) = (term165 _25260 _25258 _25259)).
Proof. exact (SYM (@lem1602136 _25260 _25258 _25259)). Qed.
Lemma lem1602138 (_25260 : real) (_25258 : real) (_25259 : real) : (term93 _25260 _25258 _25259) = (term165 _25260 _25258 _25259).
Proof. exact (EQ_MP (@lem1602137 _25260 _25258 _25259) (@lem0)). Qed.
Lemma lem1602139 (_25260 : real) (_25258 : real) (_25259 : real) (h1 : term10) : term165 _25260 _25258 _25259.
Proof. exact (EQ_MP (@lem1602138 _25260 _25258 _25259) (@lem1601537 _25260 _25258 _25259 h1)). Qed.
Lemma lem1602141 (b : Prop) (a : Prop) : (a \/ b) = (term116 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1602142 (_25258 : real) (_25259 : real) (_25260 : real) : (term165 _25260 _25258 _25259) = (term172 _25258 _25259 _25260).
Proof. exact (@lem1602141 (term166 _25260 _25258 _25259) (term62 _25258 _25259 _25260)). Qed.
Lemma lem1602144 (a : Prop) (b : Prop) : (term119 a b) = (term120 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1602145 (_25260 : real) (_25258 : real) (_25259 : real) : (term173 _25260 _25258 _25259) = (term174 _25260 _25258 _25259).
Proof. exact (@lem1602144 (term77 _25260) (term90 _25258 _25259)). Qed.
Lemma lem1602147 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1602148 (_25260 : real) : (term155 _25260) = (term39 _25260).
Proof. exact (@lem1602147 (term39 _25260)). Qed.
Lemma lem1602149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1602150 (_25260 : real) : (term156 _25260) = (term35 _25260).
Proof. exact (MK_COMB (@lem1602149) (@lem1602148 _25260)). Qed.
Lemma lem1602152 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1602153 (_25258 : real) (_25259 : real) : (term129 _25258 _25259) = (real_le _25258 _25259).
Proof. exact (@lem1602152 (real_le _25258 _25259)). Qed.
Lemma lem1602154 (_25260 : real) (_25258 : real) (_25259 : real) : (term174 _25260 _25258 _25259) = (term175 _25260 _25258 _25259).
Proof. exact (MK_COMB (@lem1602150 _25260) (@lem1602153 _25258 _25259)). Qed.
Lemma lem1602155 (_25260 : real) (_25258 : real) (_25259 : real) : (term173 _25260 _25258 _25259) = (term175 _25260 _25258 _25259).
Proof. exact (TRANS (@lem1602145 _25260 _25258 _25259) (@lem1602154 _25260 _25258 _25259)). Qed.
Lemma lem1602156 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1602157 (_25260 : real) (_25258 : real) (_25259 : real) : (term176 _25260 _25258 _25259) = (term177 _25260 _25258 _25259).
Proof. exact (MK_COMB (@lem1602156) (@lem1602155 _25260 _25258 _25259)). Qed.
Lemma lem1602158 (_25258 : real) (_25259 : real) (_25260 : real) : (term62 _25258 _25259 _25260) = (term62 _25258 _25259 _25260).
Proof. exact (eq_refl (term62 _25258 _25259 _25260)). Qed.
Lemma lem1602159 (_25258 : real) (_25259 : real) (_25260 : real) : (term172 _25258 _25259 _25260) = (term178 _25258 _25259 _25260).
Proof. exact (MK_COMB (@lem1602157 _25260 _25258 _25259) (@lem1602158 _25258 _25259 _25260)). Qed.
Lemma lem1602160 (_25258 : real) (_25259 : real) (_25260 : real) : (term165 _25260 _25258 _25259) = (term178 _25258 _25259 _25260).
Proof. exact (TRANS (@lem1602142 _25258 _25259 _25260) (@lem1602159 _25258 _25259 _25260)). Qed.
Lemma lem1602162 (z : real) (x : real) (y : real) (h1 : term74 z x y) (h2 : term37 z x y) : term175 z x y.
Proof. exact (conj (@lem1602049 z x y h2) (@lem1602056 z x y h1)). Qed.
Lemma lem1602164 (_25258 : real) (_25259 : real) (_25260 : real) (h1 : term10) : term178 _25258 _25259 _25260.
Proof. exact (EQ_MP (@lem1602160 _25258 _25259 _25260) (@lem1602139 _25260 _25258 _25259 h1)). Qed.
Lemma lem1602165 (x : real) (y : real) (z : real) (h1 : term10) : term178 x y z.
Proof. exact (@lem1602164 x y z h1). Qed.
Lemma lem1602168 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term74 z x y) (h3 : term37 z x y) : term62 x y z.
Proof. exact (@lem1602165 x y z h1 (@lem1602162 z x y h2 h3)). Qed.
Lemma lem1602169 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term74 z x y) (h3 : term37 z x y) : term138 x y z.
Proof. exact (fun h0 : term139 x y z => @lem1602168 z x y h1 h2 h3). Qed.
Lemma lem1602171 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1602172 (x : real) (y : real) (z : real) : (term138 x y z) = (term62 x y z).
Proof. exact (@lem1602171 (term62 x y z)). Qed.
Lemma lem1602173 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term74 z x y) (h3 : term37 z x y) : term62 x y z.
Proof. exact (EQ_MP (@lem1602172 x y z) (@lem1602169 z x y h1 h2 h3)). Qed.
Lemma lem1602191 (q : Prop) (p : Prop) (r : Prop) : (term107 p q r) = (term107 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1602192 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term99 _25279 _25280 _25277 _25278) = (term108 _25279 _25280 _25277 _25278).
Proof. exact (@lem1602191 (real_le _25279 _25280) (term109 _25278 _25280) (term90 _25277 _25278)). Qed.
Lemma lem1602210 (_25277 : real) (_25279 : real) : (term110 _25277 _25279) = (term110 _25277 _25279).
Proof. exact (eq_refl (term110 _25277 _25279)). Qed.
Lemma lem1602211 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term101 _25279 _25280 _25277 _25278) = (term111 _25279 _25280 _25277 _25278).
Proof. exact (MK_COMB (@lem1602210 _25277 _25279) (@lem1602192 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602215 (q : Prop) (p : Prop) (r : Prop) : (term107 p q r) = (term107 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1602216 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term111 _25279 _25280 _25277 _25278) = (term112 _25279 _25280 _25277 _25278).
Proof. exact (@lem1602215 (real_le _25279 _25280) (term109 _25277 _25279) (term113 _25280 _25277 _25278)). Qed.
Lemma lem1602246 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term101 _25279 _25280 _25277 _25278) = (term112 _25279 _25280 _25277 _25278).
Proof. exact (TRANS (@lem1602211 _25279 _25280 _25277 _25278) (@lem1602216 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1602248 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term114 _25279 _25280 _25277 _25278) = (term115 _25279 _25280 _25277 _25278).
Proof. exact (MK_COMB (@lem1602247) (@lem1602246 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602278 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term112 _25279 _25280 _25277 _25278) = (term112 _25279 _25280 _25277 _25278).
Proof. exact (eq_refl (term112 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602279 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : ((term101 _25279 _25280 _25277 _25278) = (term112 _25279 _25280 _25277 _25278)) = ((term112 _25279 _25280 _25277 _25278) = (term112 _25279 _25280 _25277 _25278)).
Proof. exact (MK_COMB (@lem1602248 _25279 _25280 _25277 _25278) (@lem1602278 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602281 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1602282 (x : Prop) : (x = x) = True.
Proof. exact (@lem1602281 Prop x). Qed.
Lemma lem1602283 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : ((term112 _25279 _25280 _25277 _25278) = (term112 _25279 _25280 _25277 _25278)) = True.
Proof. exact (@lem1602282 (term112 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602284 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : ((term101 _25279 _25280 _25277 _25278) = (term112 _25279 _25280 _25277 _25278)) = True.
Proof. exact (TRANS (@lem1602279 _25279 _25280 _25277 _25278) (@lem1602283 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602285 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : True = ((term101 _25279 _25280 _25277 _25278) = (term112 _25279 _25280 _25277 _25278)).
Proof. exact (SYM (@lem1602284 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602286 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term101 _25279 _25280 _25277 _25278) = (term112 _25279 _25280 _25277 _25278).
Proof. exact (EQ_MP (@lem1602285 _25279 _25280 _25277 _25278) (@lem0)). Qed.
Lemma lem1602287 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : term112 _25279 _25280 _25277 _25278.
Proof. exact (EQ_MP (@lem1602286 _25279 _25280 _25277 _25278) (@lem1601972 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602289 (b : Prop) (a : Prop) : (a \/ b) = (term116 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1602290 (_25277 : real) (_25278 : real) (_25279 : real) (_25280 : real) : (term112 _25279 _25280 _25277 _25278) = (term117 _25277 _25278 _25279 _25280).
Proof. exact (@lem1602289 (term118 _25279 _25280 _25277 _25278) (real_le _25279 _25280)). Qed.
Lemma lem1602292 (a : Prop) (b : Prop) : (term119 a b) = (term120 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1602293 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term121 _25279 _25280 _25277 _25278) = (term122 _25279 _25280 _25277 _25278).
Proof. exact (@lem1602292 (term109 _25277 _25279) (term113 _25280 _25277 _25278)). Qed.
Lemma lem1602295 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1602296 (_25277 : real) (_25279 : real) : (term124 _25277 _25279) = (_25277 = _25279).
Proof. exact (@lem1602295 (_25277 = _25279)). Qed.
Lemma lem1602297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1602298 (_25277 : real) (_25279 : real) : (term125 _25277 _25279) = (term126 _25277 _25279).
Proof. exact (MK_COMB (@lem1602297) (@lem1602296 _25277 _25279)). Qed.
Lemma lem1602300 (a : Prop) (b : Prop) : (term119 a b) = (term120 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1602301 (_25280 : real) (_25277 : real) (_25278 : real) : (term127 _25280 _25277 _25278) = (term128 _25280 _25277 _25278).
Proof. exact (@lem1602300 (term109 _25278 _25280) (term90 _25277 _25278)). Qed.
Lemma lem1602303 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1602304 (_25278 : real) (_25280 : real) : (term124 _25278 _25280) = (_25278 = _25280).
Proof. exact (@lem1602303 (_25278 = _25280)). Qed.
Lemma lem1602305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1602306 (_25278 : real) (_25280 : real) : (term125 _25278 _25280) = (term126 _25278 _25280).
Proof. exact (MK_COMB (@lem1602305) (@lem1602304 _25278 _25280)). Qed.
Lemma lem1602308 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1602309 (_25277 : real) (_25278 : real) : (term129 _25277 _25278) = (real_le _25277 _25278).
Proof. exact (@lem1602308 (real_le _25277 _25278)). Qed.
Lemma lem1602310 (_25280 : real) (_25277 : real) (_25278 : real) : (term128 _25280 _25277 _25278) = (term130 _25280 _25277 _25278).
Proof. exact (MK_COMB (@lem1602306 _25278 _25280) (@lem1602309 _25277 _25278)). Qed.
Lemma lem1602311 (_25280 : real) (_25277 : real) (_25278 : real) : (term127 _25280 _25277 _25278) = (term130 _25280 _25277 _25278).
Proof. exact (TRANS (@lem1602301 _25280 _25277 _25278) (@lem1602310 _25280 _25277 _25278)). Qed.
Lemma lem1602312 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term122 _25279 _25280 _25277 _25278) = (term131 _25279 _25280 _25277 _25278).
Proof. exact (MK_COMB (@lem1602298 _25277 _25279) (@lem1602311 _25280 _25277 _25278)). Qed.
Lemma lem1602313 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term121 _25279 _25280 _25277 _25278) = (term131 _25279 _25280 _25277 _25278).
Proof. exact (TRANS (@lem1602293 _25279 _25280 _25277 _25278) (@lem1602312 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602314 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1602315 (_25279 : real) (_25280 : real) (_25277 : real) (_25278 : real) : (term132 _25279 _25280 _25277 _25278) = (term133 _25279 _25280 _25277 _25278).
Proof. exact (MK_COMB (@lem1602314) (@lem1602313 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602316 (_25279 : real) (_25280 : real) : (real_le _25279 _25280) = (real_le _25279 _25280).
Proof. exact (eq_refl (real_le _25279 _25280)). Qed.
Lemma lem1602317 (_25277 : real) (_25278 : real) (_25279 : real) (_25280 : real) : (term117 _25277 _25278 _25279 _25280) = (term134 _25277 _25278 _25279 _25280).
Proof. exact (MK_COMB (@lem1602315 _25279 _25280 _25277 _25278) (@lem1602316 _25279 _25280)). Qed.
Lemma lem1602318 (_25277 : real) (_25278 : real) (_25279 : real) (_25280 : real) : (term112 _25279 _25280 _25277 _25278) = (term134 _25277 _25278 _25279 _25280).
Proof. exact (TRANS (@lem1602290 _25277 _25278 _25279 _25280) (@lem1602317 _25277 _25278 _25279 _25280)). Qed.
Lemma lem1602320 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term74 z x y) (h4 : term37 z x y) : term179 x y z.
Proof. exact (conj (@lem1602042 z y h2) (@lem1602173 z x y h1 h3 h4)). Qed.
Lemma lem1602321 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term74 z x y) (h4 : term37 z x y) : term180 x y z.
Proof. exact (conj (@lem1602034 z x h2) (@lem1602320 z x y h1 h2 h3 h4)). Qed.
Lemma lem1602323 (_25277 : real) (_25278 : real) (_25279 : real) (_25280 : real) : term134 _25277 _25278 _25279 _25280.
Proof. exact (EQ_MP (@lem1602318 _25277 _25278 _25279 _25280) (@lem1602287 _25279 _25280 _25277 _25278)). Qed.
Lemma lem1602324 (x : real) (z : real) (y : real) : term181 x z y.
Proof. exact (@lem1602323 (real_mul x z) (real_mul y z) (real_mul z x) (real_mul z y)). Qed.
Lemma lem1602327 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term74 z x y) (h4 : term37 z x y) : term34 x z y.
Proof. exact (@lem1602324 x z y (@lem1602321 z x y h1 h2 h3 h4)). Qed.
Lemma lem1602328 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term74 z x y) (h4 : term37 z x y) : term106 x z y.
Proof. exact (fun h0 : term92 x z y => @lem1602327 z x y h1 h2 h3 h4). Qed.
Lemma lem1602330 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1602331 (x : real) (z : real) (y : real) : (term106 x z y) = (term34 x z y).
Proof. exact (@lem1602330 (term34 x z y)). Qed.
Lemma lem1602332 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term74 z x y) (h4 : term37 z x y) : term34 x z y.
Proof. exact (EQ_MP (@lem1602331 x z y) (@lem1602328 z x y h1 h2 h3 h4)). Qed.
Lemma lem1602335 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1602337 (x : real) (z : real) (y : real) : (term92 x z y) = (term182 x z y).
Proof. exact (@lem1602335 (term34 x z y)). Qed.
Lemma lem1602340 (z : real) (x : real) (y : real) (h1 : term74 z x y) : term182 x z y.
Proof. exact (EQ_MP (@lem1602337 x z y) (@lem1601525 z x y h1)). Qed.
Lemma lem1602343 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term74 z x y) (h4 : term37 z x y) : False.
Proof. exact (@lem1602340 z x y h3 (@lem1602332 z x y h1 h2 h3 h4)). Qed.
Lemma lem1602344 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term74 z x y) (h4 : term37 z x y) : term164.
Proof. exact (fun h0 : ~ False => @lem1602343 z x y h1 h2 h3 h4). Qed.
Lemma lem1602346 (p : Prop) : (term103 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1602347 : term164 = False.
Proof. exact (@lem1602346 False). Qed.
Lemma lem1602348 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term74 z x y) (h4 : term37 z x y) : False.
Proof. exact (EQ_MP (@lem1602347) (@lem1602344 z x y h1 h2 h3 h4)). Qed.
Lemma lem1602349 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term74 z x y) (h4 : term37 z x y) : term25 = False.
Proof. exact (prop_ext (fun h5 : term25 => @lem1602348 z x y h1 h2 h3 h4) (fun h5 : False => @lem1601404 h2)). Qed.
Lemma lem1602350 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term74 z x y) (h4 : term37 z x y) : False.
Proof. exact (EQ_MP (@lem1602349 z x y h1 h2 h3 h4) (@lem1601404 h2)). Qed.
Lemma lem1602351 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term73 z x y) (h4 : term37 z x y) : term25 = False.
Proof. exact (prop_ext (fun h5 : term25 => @lem1601953 z x y h1 h2 h3 h4) (fun h5 : False => @lem1601341 h2)). Qed.
Lemma lem1602352 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term73 z x y) (h4 : term37 z x y) : False.
Proof. exact (EQ_MP (@lem1602351 z x y h1 h2 h3 h4) (@lem1601341 h2)). Qed.
Lemma lem1602353 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term37 z x y) : False.
Proof. exact (or_elim (@lem1601324 z x y h3) (fun h0 : term73 z x y => @lem1602352 z x y h1 h2 h0 h3) (fun h0 : term74 z x y => @lem1602350 z x y h1 h2 h0 h3)). Qed.
Lemma lem1602354 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term37 z x y) : (term37 z x y) = False.
Proof. exact (prop_ext (fun h4 : term37 z x y => @lem1602353 z x y h1 h2 h3) (fun h4 : False => @lem1601323 z x y h3)). Qed.
Lemma lem1602355 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term37 z x y) : False.
Proof. exact (EQ_MP (@lem1602354 z x y h1 h2 h3) (@lem1601323 z x y h3)). Qed.
Lemma lem1602356 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term37 z x y) : term25 = False.
Proof. exact (prop_ext (fun h4 : term25 => @lem1602355 z x y h1 h2 h3) (fun h4 : False => @lem1601188 h2)). Qed.
Lemma lem1602357 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term37 z x y) : False.
Proof. exact (EQ_MP (@lem1602356 z x y h1 h2 h3) (@lem1601188 h2)). Qed.
Lemma lem1602358 (x : real) (y : real) (h1 : term10) (h2 : term25) (h3 : term48 x y) : False.
Proof. exact (ex_elim (@lem1601167 x y h3) (fun z : real => fun h0 : term47 x y z => @lem1602357 z x y h1 h2 h0)). Qed.
Lemma lem1602359 (x : real) (h1 : term10) (h2 : term25) (h3 : term55 x) : False.
Proof. exact (ex_elim (@lem1601166 x h3) (fun y : real => fun h0 : term54 x y => @lem1602358 x y h1 h2 h0)). Qed.
Lemma lem1602360 (h1 : term10) (h2 : term25) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1601054 h3) (fun x : real => fun h0 : term60 x => @lem1602359 x h1 h2 h0)). Qed.
Lemma lem1602361 (h1 : term10) (h2 : term25) (h3 : term3) : term25 = False.
Proof. exact (prop_ext (fun h4 : term25 => @lem1602360 h1 h2 h3) (fun h4 : False => @lem1601074 h2)). Qed.
Lemma lem1602362 (h1 : term10) (h2 : term25) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1602361 h1 h2 h3) (@lem1601074 h2)). Qed.
Lemma lem1602363 (h1 : term25) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1602362 h0 h1 h2). Qed.
Lemma lem1602364 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1602365 (h1 : term25) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1602364) (@lem1602363 h1 h2)). Qed.
Lemma lem1602366 (h1 : term3) : term13.
Proof. exact (fun h0 : term25 => @lem1602365 h0 h1). Qed.
Lemma lem1602367 : term15.
Proof. exact (fun h0 : term3 => @lem1602366 h0). Qed.
Lemma lem1602368 : term4.
Proof. exact (EQ_MP (@lem1600939) (@lem1602367)). Qed.
Lemma lem1602370 : term4.
Proof. exact (@lem1600771 (@lem1602368)). Qed.
Lemma lem1602371 (h1 : term3) : term12.
Proof. exact (@lem1602370 (@lem1600756 h1)). Qed.
Lemma lem1602372 (h1 : term3) : term8.
Proof. exact (@lem1602371 h1 (@lem1338712)). Qed.
Lemma lem1602373 (h1 : term3) : False.
Proof. exact (@lem1602372 h1 (@lem1600741)). Qed.
Lemma lem1602374 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1602373 h1) (fun h2 : False => @lem1600756 h1)). Qed.
Lemma lem1602375 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1602374 h1) (@lem1600756 h1)). Qed.
Lemma lem1602376 : term2.
Proof. exact (fun h0 : term3 => @lem1602375 h0). Qed.
Lemma lem1602377 : term1.
Proof. exact (EQ_MP (@lem1600755) (@lem1602376)). Qed.
