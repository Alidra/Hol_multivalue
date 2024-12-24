Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_POW2_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_LE_SQUARE_spec.
Require Import REAL_POW_2_spec.
Require Import SQRT_POW_2_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1945860 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1945861 : term1 = term2.
Proof. exact (@lem1945860 term1). Qed.
Lemma lem1945862 : term2 = term1.
Proof. exact (SYM (@lem1945861)). Qed.
Lemma lem1945863 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1945866 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1945867 : term5.
Proof. exact (fun h0 : term4 => @lem1945866 h0). Qed.
Lemma lem1945868 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1945869 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1945870 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1945868 h2 (@lem1945869 h1)). Qed.
Lemma lem1945871 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1945870 h1 h0). Qed.
Lemma lem1945872 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1945873 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1945871 h1 (@lem1945872 h2)). Qed.
Lemma lem1945874 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1945873 h0 h1). Qed.
Lemma lem1945875 : term7.
Proof. exact (fun h0 : term5 => @lem1945874 h0). Qed.
Lemma lem1945878 : term5.
Proof. exact (@lem1945875 (@lem1945867)). Qed.
Lemma lem1945900 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1945901 : term8 = term9.
Proof. exact (@lem1945900 term10). Qed.
Lemma lem1945906 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1945907 : term12 = term13.
Proof. exact (MK_COMB (@lem1945906) (@lem1945901)). Qed.
Lemma lem1945910 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1945911 : term15 = term16.
Proof. exact (MK_COMB (@lem1945910) (@lem1945907)). Qed.
Lemma lem1945914 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1945921 : term4 = term18.
Proof. exact (MK_COMB (@lem1945914) (@lem1945911)). Qed.
Lemma lem1945922 (x : real) : ((term19 x) = (real_mul x x)) = ((term19 x) = (real_mul x x)).
Proof. exact (eq_refl ((term19 x) = (real_mul x x))). Qed.
Lemma lem1945923 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1945922 x)). Qed.
Lemma lem1945924 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1945925 : term10 = term10.
Proof. exact (MK_COMB (@lem1945924) (@lem1945923)). Qed.
Lemma lem1945926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1945927 : term9 = term9.
Proof. exact (MK_COMB (@lem1945926) (@lem1945925)). Qed.
Lemma lem1945928 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1945929 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem1945928 x)). Qed.
Lemma lem1945930 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1945931 : term23 = term23.
Proof. exact (MK_COMB (@lem1945930) (@lem1945929)). Qed.
Lemma lem1945932 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1945933 : term11 = term11.
Proof. exact (MK_COMB (@lem1945932) (@lem1945931)). Qed.
Lemma lem1945934 : term13 = term13.
Proof. exact (MK_COMB (@lem1945933) (@lem1945927)). Qed.
Lemma lem1945939 (x : real) : (term24 x) = (term24 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1945940 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1945939 x)). Qed.
Lemma lem1945941 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1945942 : term26 = term26.
Proof. exact (MK_COMB (@lem1945941) (@lem1945940)). Qed.
Lemma lem1945943 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1945944 : term14 = term14.
Proof. exact (MK_COMB (@lem1945943) (@lem1945942)). Qed.
Lemma lem1945945 : term16 = term16.
Proof. exact (MK_COMB (@lem1945944) (@lem1945934)). Qed.
Lemma lem1945950 (x : real) : (((term27 x) = x) = (term28 x)) = (((term27 x) = x) = (term28 x)).
Proof. exact (eq_refl (((term27 x) = x) = (term28 x))). Qed.
Lemma lem1945951 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1945950 x)). Qed.
Lemma lem1945952 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1945953 : term1 = term1.
Proof. exact (MK_COMB (@lem1945952) (@lem1945951)). Qed.
Lemma lem1945954 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1945955 : term3 = term3.
Proof. exact (MK_COMB (@lem1945954) (@lem1945953)). Qed.
Lemma lem1945956 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1945957 : term17 = term17.
Proof. exact (MK_COMB (@lem1945956) (@lem1945955)). Qed.
Lemma lem1945958 : term18 = term18.
Proof. exact (MK_COMB (@lem1945957) (@lem1945945)). Qed.
Lemma lem1945993 : term4 = term18.
Proof. exact (TRANS (@lem1945921) (@lem1945958)). Qed.
Lemma lem1945994 : term18 = term4.
Proof. exact (SYM (@lem1945993)). Qed.
Lemma lem1945995 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1945996 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem1945997 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1945998 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1946013 (x : real) : (term30 x) = (term31 x).
Proof. exact (@lem17646 ((term27 x) = x) (term28 x)). Qed.
Lemma lem1946014 (P : real -> Prop) : (term32 P) = (term33 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1946015 : term3 = term34.
Proof. exact (@lem1946014 term29). Qed.
Lemma lem1946016 (x : real) : (term35 x) = (((term27 x) = x) = (term28 x)).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1946017 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1946018 (x : real) : (term36 x) = (term30 x).
Proof. exact (MK_COMB (@lem1946017) (@lem1946016 x)). Qed.
Lemma lem1946019 (x : real) : (term36 x) = (term31 x).
Proof. exact (TRANS (@lem1946018 x) (@lem1946013 x)). Qed.
Lemma lem1946020 : term37 = term38.
Proof. exact (fun_ext (fun x : real => @lem1946019 x)). Qed.
Lemma lem1946021 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1946022 : term34 = term39.
Proof. exact (MK_COMB (@lem1946021) (@lem1946020)). Qed.
Lemma lem1946023 : term3 = term39.
Proof. exact (TRANS (@lem1946015) (@lem1946022)). Qed.
Lemma lem1946025 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term40 A P Q) = (term41 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1946026 (P : real -> Prop) (Q : real -> Prop) : (term42 P Q) = (term43 P Q).
Proof. exact (@lem1946025 real P Q). Qed.
Lemma lem1946027 : term44 = term45.
Proof. exact (@lem1946026 term46 term47). Qed.
Lemma lem1946028 (x : real) : (term48 x) = (term49 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1946029 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1946030 (x : real) : (term50 x) = (term51 x).
Proof. exact (MK_COMB (@lem1946029) (@lem1946028 x)). Qed.
Lemma lem1946031 (x : real) : (term52 x) = (term53 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1946032 (x : real) : (term54 x) = (term31 x).
Proof. exact (MK_COMB (@lem1946030 x) (@lem1946031 x)). Qed.
Lemma lem1946033 : term55 = term38.
Proof. exact (fun_ext (fun x : real => @lem1946032 x)). Qed.
Lemma lem1946034 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1946035 : term44 = term39.
Proof. exact (MK_COMB (@lem1946034) (@lem1946033)). Qed.
Lemma lem1946036 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1946037 : term56 = term57.
Proof. exact (MK_COMB (@lem1946036) (@lem1946035)). Qed.
Lemma lem1946038 (x : real) : (term48 x) = (term49 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1946039 : term58 = term46.
Proof. exact (fun_ext (fun x : real => @lem1946038 x)). Qed.
Lemma lem1946040 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1946041 : term59 = term60.
Proof. exact (MK_COMB (@lem1946040) (@lem1946039)). Qed.
Lemma lem1946042 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1946043 : term61 = term62.
Proof. exact (MK_COMB (@lem1946042) (@lem1946041)). Qed.
Lemma lem1946044 (x : real) : (term52 x) = (term53 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1946045 : term63 = term47.
Proof. exact (fun_ext (fun x : real => @lem1946044 x)). Qed.
Lemma lem1946046 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1946047 : term64 = term65.
Proof. exact (MK_COMB (@lem1946046) (@lem1946045)). Qed.
Lemma lem1946048 : term45 = term66.
Proof. exact (MK_COMB (@lem1946043) (@lem1946047)). Qed.
Lemma lem1946049 : (term44 = term45) = (term39 = term66).
Proof. exact (MK_COMB (@lem1946037) (@lem1946048)). Qed.
Lemma lem1946050 : term39 = term66.
Proof. exact (EQ_MP (@lem1946049) (@lem1946027)). Qed.
Lemma lem1946148 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term41 A P Q) = (term40 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1946149 (P : real -> Prop) (Q : real -> Prop) : (term43 P Q) = (term42 P Q).
Proof. exact (@lem1946148 real P Q). Qed.
Lemma lem1946150 : term45 = term44.
Proof. exact (@lem1946149 term46 term47). Qed.
Lemma lem1946151 (x : real) : (term48 x) = (term49 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1946152 : term58 = term46.
Proof. exact (fun_ext (fun x : real => @lem1946151 x)). Qed.
Lemma lem1946153 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1946154 : term59 = term60.
Proof. exact (MK_COMB (@lem1946153) (@lem1946152)). Qed.
Lemma lem1946155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1946156 : term61 = term62.
Proof. exact (MK_COMB (@lem1946155) (@lem1946154)). Qed.
Lemma lem1946157 (x : real) : (term52 x) = (term53 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1946158 : term63 = term47.
Proof. exact (fun_ext (fun x : real => @lem1946157 x)). Qed.
Lemma lem1946159 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1946160 : term64 = term65.
Proof. exact (MK_COMB (@lem1946159) (@lem1946158)). Qed.
Lemma lem1946161 : term45 = term66.
Proof. exact (MK_COMB (@lem1946156) (@lem1946160)). Qed.
Lemma lem1946162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1946163 : term67 = term68.
Proof. exact (MK_COMB (@lem1946162) (@lem1946161)). Qed.
Lemma lem1946164 (x : real) : (term48 x) = (term49 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1946165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1946166 (x : real) : (term50 x) = (term51 x).
Proof. exact (MK_COMB (@lem1946165) (@lem1946164 x)). Qed.
Lemma lem1946167 (x : real) : (term52 x) = (term53 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1946168 (x : real) : (term54 x) = (term31 x).
Proof. exact (MK_COMB (@lem1946166 x) (@lem1946167 x)). Qed.
Lemma lem1946169 : term55 = term38.
Proof. exact (fun_ext (fun x : real => @lem1946168 x)). Qed.
Lemma lem1946170 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1946171 : term44 = term39.
Proof. exact (MK_COMB (@lem1946170) (@lem1946169)). Qed.
Lemma lem1946172 : (term45 = term44) = (term66 = term39).
Proof. exact (MK_COMB (@lem1946163) (@lem1946171)). Qed.
Lemma lem1946173 : term66 = term39.
Proof. exact (EQ_MP (@lem1946172) (@lem1946150)). Qed.
Lemma lem1946174 : term39 = term39.
Proof. exact (TRANS (@lem1946050) (@lem1946173)). Qed.
Lemma lem1946175 : term3 = term39.
Proof. exact (TRANS (@lem1946023) (@lem1946174)). Qed.
Lemma lem1946176 (h1 : term3) : term39.
Proof. exact (EQ_MP (@lem1946175) (@lem1945995 h1)). Qed.
Lemma lem1946183 (x : real) : (term24 x) = (term69 x).
Proof. exact (@lem17265 (term28 x) ((term27 x) = x)). Qed.
Lemma lem1946184 : term25 = term70.
Proof. exact (fun_ext (fun x : real => @lem1946183 x)). Qed.
Lemma lem1946185 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1946238 : term26 = term71.
Proof. exact (MK_COMB (@lem1946185) (@lem1946184)). Qed.
Lemma lem1946239 (h1 : term26) : term71.
Proof. exact (EQ_MP (@lem1946238) (@lem1945996 h1)). Qed.
Lemma lem1946240 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1946241 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem1946240 x)). Qed.
Lemma lem1946242 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1946251 : term23 = term23.
Proof. exact (MK_COMB (@lem1946242) (@lem1946241)). Qed.
Lemma lem1946252 (h1 : term23) : term23.
Proof. exact (EQ_MP (@lem1946251) (@lem1945997 h1)). Qed.
Lemma lem1946253 (x : real) : ((term19 x) = (real_mul x x)) = ((term19 x) = (real_mul x x)).
Proof. exact (eq_refl ((term19 x) = (real_mul x x))). Qed.
Lemma lem1946254 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1946253 x)). Qed.
Lemma lem1946255 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1946264 : term10 = term10.
Proof. exact (MK_COMB (@lem1946255) (@lem1946254)). Qed.
Lemma lem1946265 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1946264) (@lem1945998 h1)). Qed.
Lemma lem1946297 (x : real) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem1946298 : term70 = term70.
Proof. exact (fun_ext (fun x : real => @lem1946297 x)). Qed.
Lemma lem1946299 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1946300 : term71 = term71.
Proof. exact (MK_COMB (@lem1946299) (@lem1946298)). Qed.
Lemma lem1946301 (h1 : term26) : term71.
Proof. exact (EQ_MP (@lem1946300) (@lem1946239 h1)). Qed.
Lemma lem1946314 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1946315 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem1946314 x)). Qed.
Lemma lem1946316 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1946317 : term23 = term23.
Proof. exact (MK_COMB (@lem1946316) (@lem1946315)). Qed.
Lemma lem1946318 (h1 : term23) : term23.
Proof. exact (EQ_MP (@lem1946317) (@lem1946252 h1)). Qed.
Lemma lem1946337 (x : real) : ((term19 x) = (real_mul x x)) = ((term19 x) = (real_mul x x)).
Proof. exact (eq_refl ((term19 x) = (real_mul x x))). Qed.
Lemma lem1946338 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1946337 x)). Qed.
Lemma lem1946339 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1946340 : term10 = term10.
Proof. exact (MK_COMB (@lem1946339) (@lem1946338)). Qed.
Lemma lem1946341 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1946340) (@lem1946265 h1)). Qed.
Lemma lem1946407 (x : real) (h1 : term31 x) : term31 x.
Proof. exact (h1). Qed.
Lemma lem1946408 (x : real) (h1 : term49 x) : term49 x.
Proof. exact (h1). Qed.
Lemma lem1946409 (x : real) (h1 : term53 x) : term53 x.
Proof. exact (h1). Qed.
Lemma lem1946428 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1946429 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem1946428 x)). Qed.
Lemma lem1946430 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1946432 : term23 = term23.
Proof. exact (MK_COMB (@lem1946430) (@lem1946429)). Qed.
Lemma lem1946433 (h1 : term23) : term23.
Proof. exact (EQ_MP (@lem1946432) (@lem1946318 h1)). Qed.
Lemma lem1946435 (x : real) : ((term19 x) = (real_mul x x)) = ((term19 x) = (real_mul x x)).
Proof. exact (eq_refl ((term19 x) = (real_mul x x))). Qed.
Lemma lem1946436 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1946435 x)). Qed.
Lemma lem1946437 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1946439 : term10 = term10.
Proof. exact (MK_COMB (@lem1946437) (@lem1946436)). Qed.
Lemma lem1946440 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1946439) (@lem1946341 h1)). Qed.
Lemma lem1946456 (x : real) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem1946457 : term70 = term70.
Proof. exact (fun_ext (fun x : real => @lem1946456 x)). Qed.
Lemma lem1946458 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1946460 : term71 = term71.
Proof. exact (MK_COMB (@lem1946458) (@lem1946457)). Qed.
Lemma lem1946461 (h1 : term26) : term71.
Proof. exact (EQ_MP (@lem1946460) (@lem1946301 h1)). Qed.
Lemma lem1946487 (_27321 : real) (h1 : term23) : term72 _27321.
Proof. exact (@lem1946433 h1 _27321). Qed.
Lemma lem1946488 (_27321 : real) : (term72 _27321) = (term21 _27321).
Proof. exact (eq_refl (term72 _27321)). Qed.
Lemma lem1946490 (_27322 : real) (h1 : term10) : term73 _27322.
Proof. exact (@lem1946440 h1 _27322). Qed.
Lemma lem1946491 (_27322 : real) : (term73 _27322) = ((term19 _27322) = (real_mul _27322 _27322)).
Proof. exact (eq_refl (term73 _27322)). Qed.
Lemma lem1946493 (_27323 : real) (h1 : term26) : term74 _27323.
Proof. exact (@lem1946461 h1 _27323). Qed.
Lemma lem1946494 (_27323 : real) : (term74 _27323) = (term69 _27323).
Proof. exact (eq_refl (term74 _27323)). Qed.
Lemma lem1946515 (x : real) (h1 : term49 x) : term75 x.
Proof. exact (proj2 (@lem1946408 x h1)). Qed.
Lemma lem1946521 (_27323 : real) (h1 : term26) : term69 _27323.
Proof. exact (EQ_MP (@lem1946494 _27323) (@lem1946493 _27323 h1)). Qed.
Lemma lem1946527 (x : real) (h1 : term53 x) : term76 x.
Proof. exact (proj1 (@lem1946409 x h1)). Qed.
Lemma lem1946530 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1946531 (_27326 : real) (_27328 : real) (h1 : _27326 = _27328) : _27326 = _27328.
Proof. exact (h1). Qed.
Lemma lem1946532 (_27327 : real) (_27329 : real) (h1 : _27327 = _27329) : _27327 = _27329.
Proof. exact (h1). Qed.
Lemma lem1946533 (_27326 : real) (_27328 : real) (h1 : _27326 = _27328) : (real_le _27326) = (real_le _27328).
Proof. exact (MK_COMB (@lem1946530) (@lem1946531 _27326 _27328 h1)). Qed.
Lemma lem1946534 (_27326 : real) (_27328 : real) (_27327 : real) (_27329 : real) (h1 : _27326 = _27328) (h2 : _27327 = _27329) : (real_le _27326 _27327) = (real_le _27328 _27329).
Proof. exact (MK_COMB (@lem1946533 _27326 _27328 h1) (@lem1946532 _27327 _27329 h2)). Qed.
Lemma lem1946536 (b : Prop) (a : Prop) : term77 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1946537 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : term78 _27328 _27329 _27326 _27327.
Proof. exact (@lem1946536 (real_le _27328 _27329) (real_le _27326 _27327)). Qed.
Lemma lem1946538 (_27326 : real) (_27328 : real) (_27327 : real) (_27329 : real) (h1 : _27326 = _27328) (h2 : _27327 = _27329) : term79 _27328 _27329 _27326 _27327.
Proof. exact (@lem1946537 _27328 _27329 _27326 _27327 (@lem1946534 _27326 _27328 _27327 _27329 h1 h2)). Qed.
Lemma lem1946539 (_27329 : real) (_27327 : real) (_27326 : real) (_27328 : real) (h1 : _27326 = _27328) : term80 _27328 _27329 _27326 _27327.
Proof. exact (fun h0 : _27327 = _27329 => @lem1946538 _27326 _27328 _27327 _27329 h1 h0). Qed.
Lemma lem1946541 (a : Prop) (b : Prop) : (a -> b) = (term81 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1946542 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term80 _27328 _27329 _27326 _27327) = (term82 _27328 _27329 _27326 _27327).
Proof. exact (@lem1946541 (_27327 = _27329) (term79 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946543 (_27329 : real) (_27327 : real) (_27326 : real) (_27328 : real) (h1 : _27326 = _27328) : term82 _27328 _27329 _27326 _27327.
Proof. exact (EQ_MP (@lem1946542 _27328 _27329 _27326 _27327) (@lem1946539 _27329 _27327 _27326 _27328 h1)). Qed.
Lemma lem1946544 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : term83 _27328 _27329 _27326 _27327.
Proof. exact (fun h0 : _27326 = _27328 => @lem1946543 _27329 _27327 _27326 _27328 h0). Qed.
Lemma lem1946546 (a : Prop) (b : Prop) : (a -> b) = (term81 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1946547 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term83 _27328 _27329 _27326 _27327) = (term84 _27328 _27329 _27326 _27327).
Proof. exact (@lem1946546 (_27326 = _27328) (term82 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946548 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : term84 _27328 _27329 _27326 _27327.
Proof. exact (EQ_MP (@lem1946547 _27328 _27329 _27326 _27327) (@lem1946544 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946620 (x : real) (y : real) (z : real) : term85 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1946624 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1946625 : term86 = term86.
Proof. exact (@lem1946624 term86). Qed.
Lemma lem1946626 : term87.
Proof. exact (fun h0 : term88 => @lem1946625). Qed.
Lemma lem1946628 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1946629 : term87 = (term86 = term86).
Proof. exact (@lem1946628 (term86 = term86)). Qed.
Lemma lem1946630 : term86 = term86.
Proof. exact (EQ_MP (@lem1946629) (@lem1946626)). Qed.
Lemma lem1946632 (_27322 : real) (h1 : term10) : (term19 _27322) = (real_mul _27322 _27322).
Proof. exact (EQ_MP (@lem1946491 _27322) (@lem1946490 _27322 h1)). Qed.
Lemma lem1946633 (x : real) (h1 : term10) : (term27 x) = (term90 x).
Proof. exact (@lem1946632 (sqrt x) h1). Qed.
Lemma lem1946634 (x : real) (h1 : term10) : term91 x.
Proof. exact (fun h0 : term92 x => @lem1946633 x h1). Qed.
Lemma lem1946636 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1946637 (x : real) : (term91 x) = ((term27 x) = (term90 x)).
Proof. exact (@lem1946636 ((term27 x) = (term90 x))). Qed.
Lemma lem1946638 (x : real) (h1 : term10) : (term27 x) = (term90 x).
Proof. exact (EQ_MP (@lem1946637 x) (@lem1946634 x h1)). Qed.
Lemma lem1946640 (x : real) (h1 : term49 x) : (term27 x) = x.
Proof. exact (proj1 (@lem1946408 x h1)). Qed.
Lemma lem1946641 (x : real) (h1 : term49 x) : term93 x.
Proof. exact (fun h0 : term76 x => @lem1946640 x h1). Qed.
Lemma lem1946643 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1946644 (x : real) : (term93 x) = ((term27 x) = x).
Proof. exact (@lem1946643 ((term27 x) = x)). Qed.
Lemma lem1946645 (x : real) (h1 : term49 x) : (term27 x) = x.
Proof. exact (EQ_MP (@lem1946644 x) (@lem1946641 x h1)). Qed.
Lemma lem1946663 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1946664 (y : real) (x : real) (z : real) : (term94 x y z) = (term95 y x z).
Proof. exact (@lem1946663 (y = z) (term96 x z)). Qed.
Lemma lem1946674 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (eq_refl (term97 x y)). Qed.
Lemma lem1946675 (y : real) (x : real) (z : real) : (term85 x y z) = (term98 y x z).
Proof. exact (MK_COMB (@lem1946674 x y) (@lem1946664 y x z)). Qed.
Lemma lem1946679 (q : Prop) (p : Prop) (r : Prop) : (term99 p q r) = (term99 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1946680 (y : real) (x : real) (z : real) : (term98 y x z) = (term100 y x z).
Proof. exact (@lem1946679 (y = z) (term96 x y) (term96 x z)). Qed.
Lemma lem1946702 (y : real) (x : real) (z : real) : (term85 x y z) = (term100 y x z).
Proof. exact (TRANS (@lem1946675 y x z) (@lem1946680 y x z)). Qed.
Lemma lem1946703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1946704 (y : real) (x : real) (z : real) : (term101 x y z) = (term102 y x z).
Proof. exact (MK_COMB (@lem1946703) (@lem1946702 y x z)). Qed.
Lemma lem1946726 (y : real) (x : real) (z : real) : (term100 y x z) = (term100 y x z).
Proof. exact (eq_refl (term100 y x z)). Qed.
Lemma lem1946727 (y : real) (x : real) (z : real) : ((term85 x y z) = (term100 y x z)) = ((term100 y x z) = (term100 y x z)).
Proof. exact (MK_COMB (@lem1946704 y x z) (@lem1946726 y x z)). Qed.
Lemma lem1946729 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1946730 (x : Prop) : (x = x) = True.
Proof. exact (@lem1946729 Prop x). Qed.
Lemma lem1946731 (y : real) (x : real) (z : real) : ((term100 y x z) = (term100 y x z)) = True.
Proof. exact (@lem1946730 (term100 y x z)). Qed.
Lemma lem1946732 (y : real) (x : real) (z : real) : ((term85 x y z) = (term100 y x z)) = True.
Proof. exact (TRANS (@lem1946727 y x z) (@lem1946731 y x z)). Qed.
Lemma lem1946733 (y : real) (x : real) (z : real) : True = ((term85 x y z) = (term100 y x z)).
Proof. exact (SYM (@lem1946732 y x z)). Qed.
Lemma lem1946734 (y : real) (x : real) (z : real) : (term85 x y z) = (term100 y x z).
Proof. exact (EQ_MP (@lem1946733 y x z) (@lem0)). Qed.
Lemma lem1946735 (y : real) (x : real) (z : real) : term100 y x z.
Proof. exact (EQ_MP (@lem1946734 y x z) (@lem1946620 x y z)). Qed.
Lemma lem1946737 (b : Prop) (a : Prop) : (a \/ b) = (term103 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1946738 (x : real) (y : real) (z : real) : (term100 y x z) = (term104 x y z).
Proof. exact (@lem1946737 (term105 y x z) (y = z)). Qed.
Lemma lem1946740 (a : Prop) (b : Prop) : (term106 a b) = (term107 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1946741 (y : real) (x : real) (z : real) : (term108 y x z) = (term109 y x z).
Proof. exact (@lem1946740 (term96 x y) (term96 x z)). Qed.
Lemma lem1946743 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1946744 (x : real) (y : real) : (term111 x y) = (x = y).
Proof. exact (@lem1946743 (x = y)). Qed.
Lemma lem1946745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1946746 (x : real) (y : real) : (term112 x y) = (term113 x y).
Proof. exact (MK_COMB (@lem1946745) (@lem1946744 x y)). Qed.
Lemma lem1946748 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1946749 (x : real) (z : real) : (term111 x z) = (x = z).
Proof. exact (@lem1946748 (x = z)). Qed.
Lemma lem1946750 (y : real) (x : real) (z : real) : (term109 y x z) = (term114 y x z).
Proof. exact (MK_COMB (@lem1946746 x y) (@lem1946749 x z)). Qed.
Lemma lem1946751 (y : real) (x : real) (z : real) : (term108 y x z) = (term114 y x z).
Proof. exact (TRANS (@lem1946741 y x z) (@lem1946750 y x z)). Qed.
Lemma lem1946752 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1946753 (y : real) (x : real) (z : real) : (term115 y x z) = (term116 y x z).
Proof. exact (MK_COMB (@lem1946752) (@lem1946751 y x z)). Qed.
Lemma lem1946754 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1946755 (x : real) (y : real) (z : real) : (term104 x y z) = (term117 x y z).
Proof. exact (MK_COMB (@lem1946753 y x z) (@lem1946754 y z)). Qed.
Lemma lem1946756 (x : real) (y : real) (z : real) : (term100 y x z) = (term117 x y z).
Proof. exact (TRANS (@lem1946738 x y z) (@lem1946755 x y z)). Qed.
Lemma lem1946758 (x : real) (h1 : term10) (h2 : term49 x) : term118 x.
Proof. exact (conj (@lem1946638 x h1) (@lem1946645 x h2)). Qed.
Lemma lem1946760 (x : real) (y : real) (z : real) : term117 x y z.
Proof. exact (EQ_MP (@lem1946756 x y z) (@lem1946735 y x z)). Qed.
Lemma lem1946761 (x : real) : term119 x.
Proof. exact (@lem1946760 (term27 x) (term90 x) x). Qed.
Lemma lem1946764 (x : real) (h1 : term10) (h2 : term49 x) : (term90 x) = x.
Proof. exact (@lem1946761 x (@lem1946758 x h1 h2)). Qed.
Lemma lem1946765 (x : real) (h1 : term10) (h2 : term49 x) : term120 x.
Proof. exact (fun h0 : term121 x => @lem1946764 x h1 h2). Qed.
Lemma lem1946767 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1946768 (x : real) : (term120 x) = ((term90 x) = x).
Proof. exact (@lem1946767 ((term90 x) = x)). Qed.
Lemma lem1946769 (x : real) (h1 : term10) (h2 : term49 x) : (term90 x) = x.
Proof. exact (EQ_MP (@lem1946768 x) (@lem1946765 x h1 h2)). Qed.
Lemma lem1946771 (_27321 : real) (h1 : term23) : term21 _27321.
Proof. exact (EQ_MP (@lem1946488 _27321) (@lem1946487 _27321 h1)). Qed.
Lemma lem1946772 (x : real) (h1 : term23) : term122 x.
Proof. exact (@lem1946771 (sqrt x) h1). Qed.
Lemma lem1946773 (x : real) (h1 : term23) : term123 x.
Proof. exact (fun h0 : term124 x => @lem1946772 x h1). Qed.
Lemma lem1946775 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1946776 (x : real) : (term123 x) = (term122 x).
Proof. exact (@lem1946775 (term122 x)). Qed.
Lemma lem1946777 (x : real) (h1 : term23) : term122 x.
Proof. exact (EQ_MP (@lem1946776 x) (@lem1946773 x h1)). Qed.
Lemma lem1946795 (q : Prop) (p : Prop) (r : Prop) : (term99 p q r) = (term99 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1946796 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term82 _27328 _27329 _27326 _27327) = (term125 _27328 _27329 _27326 _27327).
Proof. exact (@lem1946795 (real_le _27328 _27329) (term96 _27327 _27329) (term126 _27326 _27327)). Qed.
Lemma lem1946814 (_27326 : real) (_27328 : real) : (term97 _27326 _27328) = (term97 _27326 _27328).
Proof. exact (eq_refl (term97 _27326 _27328)). Qed.
Lemma lem1946815 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term84 _27328 _27329 _27326 _27327) = (term127 _27328 _27329 _27326 _27327).
Proof. exact (MK_COMB (@lem1946814 _27326 _27328) (@lem1946796 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946819 (q : Prop) (p : Prop) (r : Prop) : (term99 p q r) = (term99 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1946820 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term127 _27328 _27329 _27326 _27327) = (term128 _27328 _27329 _27326 _27327).
Proof. exact (@lem1946819 (real_le _27328 _27329) (term96 _27326 _27328) (term129 _27329 _27326 _27327)). Qed.
Lemma lem1946850 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term84 _27328 _27329 _27326 _27327) = (term128 _27328 _27329 _27326 _27327).
Proof. exact (TRANS (@lem1946815 _27328 _27329 _27326 _27327) (@lem1946820 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946851 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1946852 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term130 _27328 _27329 _27326 _27327) = (term131 _27328 _27329 _27326 _27327).
Proof. exact (MK_COMB (@lem1946851) (@lem1946850 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946882 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term128 _27328 _27329 _27326 _27327) = (term128 _27328 _27329 _27326 _27327).
Proof. exact (eq_refl (term128 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946883 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : ((term84 _27328 _27329 _27326 _27327) = (term128 _27328 _27329 _27326 _27327)) = ((term128 _27328 _27329 _27326 _27327) = (term128 _27328 _27329 _27326 _27327)).
Proof. exact (MK_COMB (@lem1946852 _27328 _27329 _27326 _27327) (@lem1946882 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946885 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1946886 (x : Prop) : (x = x) = True.
Proof. exact (@lem1946885 Prop x). Qed.
Lemma lem1946887 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : ((term128 _27328 _27329 _27326 _27327) = (term128 _27328 _27329 _27326 _27327)) = True.
Proof. exact (@lem1946886 (term128 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946888 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : ((term84 _27328 _27329 _27326 _27327) = (term128 _27328 _27329 _27326 _27327)) = True.
Proof. exact (TRANS (@lem1946883 _27328 _27329 _27326 _27327) (@lem1946887 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946889 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : True = ((term84 _27328 _27329 _27326 _27327) = (term128 _27328 _27329 _27326 _27327)).
Proof. exact (SYM (@lem1946888 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946890 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term84 _27328 _27329 _27326 _27327) = (term128 _27328 _27329 _27326 _27327).
Proof. exact (EQ_MP (@lem1946889 _27328 _27329 _27326 _27327) (@lem0)). Qed.
Lemma lem1946891 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : term128 _27328 _27329 _27326 _27327.
Proof. exact (EQ_MP (@lem1946890 _27328 _27329 _27326 _27327) (@lem1946548 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946893 (b : Prop) (a : Prop) : (a \/ b) = (term103 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1946894 (_27326 : real) (_27327 : real) (_27328 : real) (_27329 : real) : (term128 _27328 _27329 _27326 _27327) = (term132 _27326 _27327 _27328 _27329).
Proof. exact (@lem1946893 (term133 _27328 _27329 _27326 _27327) (real_le _27328 _27329)). Qed.
Lemma lem1946896 (a : Prop) (b : Prop) : (term106 a b) = (term107 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1946897 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term134 _27328 _27329 _27326 _27327) = (term135 _27328 _27329 _27326 _27327).
Proof. exact (@lem1946896 (term96 _27326 _27328) (term129 _27329 _27326 _27327)). Qed.
Lemma lem1946899 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1946900 (_27326 : real) (_27328 : real) : (term111 _27326 _27328) = (_27326 = _27328).
Proof. exact (@lem1946899 (_27326 = _27328)). Qed.
Lemma lem1946901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1946902 (_27326 : real) (_27328 : real) : (term112 _27326 _27328) = (term113 _27326 _27328).
Proof. exact (MK_COMB (@lem1946901) (@lem1946900 _27326 _27328)). Qed.
Lemma lem1946904 (a : Prop) (b : Prop) : (term106 a b) = (term107 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1946905 (_27329 : real) (_27326 : real) (_27327 : real) : (term136 _27329 _27326 _27327) = (term137 _27329 _27326 _27327).
Proof. exact (@lem1946904 (term96 _27327 _27329) (term126 _27326 _27327)). Qed.
Lemma lem1946907 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1946908 (_27327 : real) (_27329 : real) : (term111 _27327 _27329) = (_27327 = _27329).
Proof. exact (@lem1946907 (_27327 = _27329)). Qed.
Lemma lem1946909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1946910 (_27327 : real) (_27329 : real) : (term112 _27327 _27329) = (term113 _27327 _27329).
Proof. exact (MK_COMB (@lem1946909) (@lem1946908 _27327 _27329)). Qed.
Lemma lem1946912 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1946913 (_27326 : real) (_27327 : real) : (term138 _27326 _27327) = (real_le _27326 _27327).
Proof. exact (@lem1946912 (real_le _27326 _27327)). Qed.
Lemma lem1946914 (_27329 : real) (_27326 : real) (_27327 : real) : (term137 _27329 _27326 _27327) = (term139 _27329 _27326 _27327).
Proof. exact (MK_COMB (@lem1946910 _27327 _27329) (@lem1946913 _27326 _27327)). Qed.
Lemma lem1946915 (_27329 : real) (_27326 : real) (_27327 : real) : (term136 _27329 _27326 _27327) = (term139 _27329 _27326 _27327).
Proof. exact (TRANS (@lem1946905 _27329 _27326 _27327) (@lem1946914 _27329 _27326 _27327)). Qed.
Lemma lem1946916 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term135 _27328 _27329 _27326 _27327) = (term140 _27328 _27329 _27326 _27327).
Proof. exact (MK_COMB (@lem1946902 _27326 _27328) (@lem1946915 _27329 _27326 _27327)). Qed.
Lemma lem1946917 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term134 _27328 _27329 _27326 _27327) = (term140 _27328 _27329 _27326 _27327).
Proof. exact (TRANS (@lem1946897 _27328 _27329 _27326 _27327) (@lem1946916 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946918 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1946919 (_27328 : real) (_27329 : real) (_27326 : real) (_27327 : real) : (term141 _27328 _27329 _27326 _27327) = (term142 _27328 _27329 _27326 _27327).
Proof. exact (MK_COMB (@lem1946918) (@lem1946917 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946920 (_27328 : real) (_27329 : real) : (real_le _27328 _27329) = (real_le _27328 _27329).
Proof. exact (eq_refl (real_le _27328 _27329)). Qed.
Lemma lem1946921 (_27326 : real) (_27327 : real) (_27328 : real) (_27329 : real) : (term132 _27326 _27327 _27328 _27329) = (term143 _27326 _27327 _27328 _27329).
Proof. exact (MK_COMB (@lem1946919 _27328 _27329 _27326 _27327) (@lem1946920 _27328 _27329)). Qed.
Lemma lem1946922 (_27326 : real) (_27327 : real) (_27328 : real) (_27329 : real) : (term128 _27328 _27329 _27326 _27327) = (term143 _27326 _27327 _27328 _27329).
Proof. exact (TRANS (@lem1946894 _27326 _27327 _27328 _27329) (@lem1946921 _27326 _27327 _27328 _27329)). Qed.
Lemma lem1946924 (x : real) (h1 : term10) (h2 : term23) (h3 : term49 x) : term144 x.
Proof. exact (conj (@lem1946769 x h1 h3) (@lem1946777 x h2)). Qed.
Lemma lem1946925 (x : real) (h1 : term10) (h2 : term23) (h3 : term49 x) : term145 x.
Proof. exact (conj (@lem1946630) (@lem1946924 x h1 h2 h3)). Qed.
Lemma lem1946927 (_27326 : real) (_27327 : real) (_27328 : real) (_27329 : real) : term143 _27326 _27327 _27328 _27329.
Proof. exact (EQ_MP (@lem1946922 _27326 _27327 _27328 _27329) (@lem1946891 _27328 _27329 _27326 _27327)). Qed.
Lemma lem1946928 (x : real) : term146 x.
Proof. exact (@lem1946927 term86 (term90 x) term86 x). Qed.
Lemma lem1946931 (x : real) (h1 : term10) (h2 : term23) (h3 : term49 x) : term28 x.
Proof. exact (@lem1946928 x (@lem1946925 x h1 h2 h3)). Qed.
Lemma lem1946932 (x : real) (h1 : term10) (h2 : term23) (h3 : term49 x) : term147 x.
Proof. exact (fun h0 : term75 x => @lem1946931 x h1 h2 h3). Qed.
Lemma lem1946934 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1946935 (x : real) : (term147 x) = (term28 x).
Proof. exact (@lem1946934 (term28 x)). Qed.
Lemma lem1946936 (x : real) (h1 : term10) (h2 : term23) (h3 : term49 x) : term28 x.
Proof. exact (EQ_MP (@lem1946935 x) (@lem1946932 x h1 h2 h3)). Qed.
Lemma lem1946939 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1946941 (x : real) : (term75 x) = (term148 x).
Proof. exact (@lem1946939 (term28 x)). Qed.
Lemma lem1946944 (x : real) (h1 : term49 x) : term148 x.
Proof. exact (EQ_MP (@lem1946941 x) (@lem1946515 x h1)). Qed.
Lemma lem1946947 (x : real) (h1 : term10) (h2 : term23) (h3 : term49 x) : False.
Proof. exact (@lem1946944 x h3 (@lem1946936 x h1 h2 h3)). Qed.
Lemma lem1946948 (x : real) (h1 : term10) (h2 : term23) (h3 : term49 x) : term149.
Proof. exact (fun h0 : ~ False => @lem1946947 x h1 h2 h3). Qed.
Lemma lem1946950 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1946951 : term149 = False.
Proof. exact (@lem1946950 False). Qed.
Lemma lem1946952 (x : real) (h1 : term10) (h2 : term23) (h3 : term49 x) : False.
Proof. exact (EQ_MP (@lem1946951) (@lem1946948 x h1 h2 h3)). Qed.
Lemma lem1947047 (x : real) (h1 : term53 x) : term28 x.
Proof. exact (proj2 (@lem1946409 x h1)). Qed.
Lemma lem1947048 (x : real) (h1 : term53 x) : term147 x.
Proof. exact (fun h0 : term75 x => @lem1947047 x h1). Qed.
Lemma lem1947050 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1947051 (x : real) : (term147 x) = (term28 x).
Proof. exact (@lem1947050 (term28 x)). Qed.
Lemma lem1947052 (x : real) (h1 : term53 x) : term28 x.
Proof. exact (EQ_MP (@lem1947051 x) (@lem1947048 x h1)). Qed.
Lemma lem1947058 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1947059 (_27323 : real) : (term69 _27323) = (term150 _27323).
Proof. exact (@lem1947058 ((term27 _27323) = _27323) (term75 _27323)). Qed.
Lemma lem1947067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1947068 (_27323 : real) : (term151 _27323) = (term152 _27323).
Proof. exact (MK_COMB (@lem1947067) (@lem1947059 _27323)). Qed.
Lemma lem1947076 (_27323 : real) : (term150 _27323) = (term150 _27323).
Proof. exact (eq_refl (term150 _27323)). Qed.
Lemma lem1947077 (_27323 : real) : ((term69 _27323) = (term150 _27323)) = ((term150 _27323) = (term150 _27323)).
Proof. exact (MK_COMB (@lem1947068 _27323) (@lem1947076 _27323)). Qed.
Lemma lem1947079 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1947080 (x : Prop) : (x = x) = True.
Proof. exact (@lem1947079 Prop x). Qed.
Lemma lem1947081 (_27323 : real) : ((term150 _27323) = (term150 _27323)) = True.
Proof. exact (@lem1947080 (term150 _27323)). Qed.
Lemma lem1947082 (_27323 : real) : ((term69 _27323) = (term150 _27323)) = True.
Proof. exact (TRANS (@lem1947077 _27323) (@lem1947081 _27323)). Qed.
Lemma lem1947083 (_27323 : real) : True = ((term69 _27323) = (term150 _27323)).
Proof. exact (SYM (@lem1947082 _27323)). Qed.
Lemma lem1947084 (_27323 : real) : (term69 _27323) = (term150 _27323).
Proof. exact (EQ_MP (@lem1947083 _27323) (@lem0)). Qed.
Lemma lem1947085 (_27323 : real) (h1 : term26) : term150 _27323.
Proof. exact (EQ_MP (@lem1947084 _27323) (@lem1946521 _27323 h1)). Qed.
Lemma lem1947087 (b : Prop) (a : Prop) : (a \/ b) = (term103 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1947088 (_27323 : real) : (term150 _27323) = (term153 _27323).
Proof. exact (@lem1947087 (term75 _27323) ((term27 _27323) = _27323)). Qed.
Lemma lem1947090 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1947091 (_27323 : real) : (term154 _27323) = (term28 _27323).
Proof. exact (@lem1947090 (term28 _27323)). Qed.
Lemma lem1947092 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1947093 (_27323 : real) : (term155 _27323) = (term156 _27323).
Proof. exact (MK_COMB (@lem1947092) (@lem1947091 _27323)). Qed.
Lemma lem1947094 (_27323 : real) : ((term27 _27323) = _27323) = ((term27 _27323) = _27323).
Proof. exact (eq_refl ((term27 _27323) = _27323)). Qed.
Lemma lem1947095 (_27323 : real) : (term153 _27323) = (term24 _27323).
Proof. exact (MK_COMB (@lem1947093 _27323) (@lem1947094 _27323)). Qed.
Lemma lem1947096 (_27323 : real) : (term150 _27323) = (term24 _27323).
Proof. exact (TRANS (@lem1947088 _27323) (@lem1947095 _27323)). Qed.
Lemma lem1947099 (_27323 : real) (h1 : term26) : term24 _27323.
Proof. exact (EQ_MP (@lem1947096 _27323) (@lem1947085 _27323 h1)). Qed.
Lemma lem1947100 (x : real) (h1 : term26) : term24 x.
Proof. exact (@lem1947099 x h1). Qed.
Lemma lem1947103 (x : real) (h1 : term26) (h2 : term53 x) : (term27 x) = x.
Proof. exact (@lem1947100 x h1 (@lem1947052 x h2)). Qed.
Lemma lem1947104 (x : real) (h1 : term26) (h2 : term53 x) : term93 x.
Proof. exact (fun h0 : term76 x => @lem1947103 x h1 h2). Qed.
Lemma lem1947106 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1947107 (x : real) : (term93 x) = ((term27 x) = x).
Proof. exact (@lem1947106 ((term27 x) = x)). Qed.
Lemma lem1947108 (x : real) (h1 : term26) (h2 : term53 x) : (term27 x) = x.
Proof. exact (EQ_MP (@lem1947107 x) (@lem1947104 x h1 h2)). Qed.
Lemma lem1947111 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1947113 (x : real) : (term76 x) = (term157 x).
Proof. exact (@lem1947111 ((term27 x) = x)). Qed.
Lemma lem1947116 (x : real) (h1 : term53 x) : term157 x.
Proof. exact (EQ_MP (@lem1947113 x) (@lem1946527 x h1)). Qed.
Lemma lem1947119 (x : real) (h1 : term26) (h2 : term53 x) : False.
Proof. exact (@lem1947116 x h2 (@lem1947108 x h1 h2)). Qed.
Lemma lem1947120 (x : real) (h1 : term26) (h2 : term53 x) : term149.
Proof. exact (fun h0 : ~ False => @lem1947119 x h1 h2). Qed.
Lemma lem1947122 (p : Prop) : (term89 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1947123 : term149 = False.
Proof. exact (@lem1947122 False). Qed.
Lemma lem1947124 (x : real) (h1 : term26) (h2 : term53 x) : False.
Proof. exact (EQ_MP (@lem1947123) (@lem1947120 x h1 h2)). Qed.
Lemma lem1947125 (x : real) (h1 : term10) (h2 : term23) (h3 : term49 x) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1946952 x h1 h2 h3) (fun h4 : False => @lem1946440 h1)). Qed.
Lemma lem1947126 (x : real) (h1 : term10) (h2 : term23) (h3 : term49 x) : False.
Proof. exact (EQ_MP (@lem1947125 x h1 h2 h3) (@lem1946440 h1)). Qed.
Lemma lem1947127 (x : real) (h1 : term10) (h2 : term23) (h3 : term49 x) : term23 = False.
Proof. exact (prop_ext (fun h4 : term23 => @lem1947126 x h1 h2 h3) (fun h4 : False => @lem1946433 h2)). Qed.
Lemma lem1947128 (x : real) (h1 : term10) (h2 : term23) (h3 : term49 x) : False.
Proof. exact (EQ_MP (@lem1947127 x h1 h2 h3) (@lem1946433 h2)). Qed.
Lemma lem1947129 (x : real) (h1 : term10) (h2 : term26) (h3 : term23) (h4 : term31 x) : False.
Proof. exact (or_elim (@lem1946407 x h4) (fun h0 : term49 x => @lem1947128 x h1 h3 h0) (fun h0 : term53 x => @lem1947124 x h2 h0)). Qed.
Lemma lem1947130 (x : real) (h1 : term10) (h2 : term26) (h3 : term23) (h4 : term31 x) : (term31 x) = False.
Proof. exact (prop_ext (fun h5 : term31 x => @lem1947129 x h1 h2 h3 h4) (fun h5 : False => @lem1946407 x h4)). Qed.
Lemma lem1947131 (x : real) (h1 : term10) (h2 : term26) (h3 : term23) (h4 : term31 x) : False.
Proof. exact (EQ_MP (@lem1947130 x h1 h2 h3 h4) (@lem1946407 x h4)). Qed.
Lemma lem1947132 (x : real) (h1 : term10) (h2 : term26) (h3 : term23) (h4 : term31 x) : term10 = False.
Proof. exact (prop_ext (fun h5 : term10 => @lem1947131 x h1 h2 h3 h4) (fun h5 : False => @lem1946341 h1)). Qed.
Lemma lem1947133 (x : real) (h1 : term10) (h2 : term26) (h3 : term23) (h4 : term31 x) : False.
Proof. exact (EQ_MP (@lem1947132 x h1 h2 h3 h4) (@lem1946341 h1)). Qed.
Lemma lem1947134 (x : real) (h1 : term10) (h2 : term26) (h3 : term23) (h4 : term31 x) : term23 = False.
Proof. exact (prop_ext (fun h5 : term23 => @lem1947133 x h1 h2 h3 h4) (fun h5 : False => @lem1946318 h3)). Qed.
Lemma lem1947135 (x : real) (h1 : term10) (h2 : term26) (h3 : term23) (h4 : term31 x) : False.
Proof. exact (EQ_MP (@lem1947134 x h1 h2 h3 h4) (@lem1946318 h3)). Qed.
Lemma lem1947136 (h1 : term10) (h2 : term26) (h3 : term23) (h4 : term3) : False.
Proof. exact (ex_elim (@lem1946176 h4) (fun x : real => fun h0 : term38 x => @lem1947135 x h1 h2 h3 h0)). Qed.
Lemma lem1947137 (h1 : term10) (h2 : term26) (h3 : term23) (h4 : term3) : term10 = False.
Proof. exact (prop_ext (fun h5 : term10 => @lem1947136 h1 h2 h3 h4) (fun h5 : False => @lem1946265 h1)). Qed.
Lemma lem1947138 (h1 : term10) (h2 : term26) (h3 : term23) (h4 : term3) : False.
Proof. exact (EQ_MP (@lem1947137 h1 h2 h3 h4) (@lem1946265 h1)). Qed.
Lemma lem1947139 (h1 : term10) (h2 : term26) (h3 : term23) (h4 : term3) : term23 = False.
Proof. exact (prop_ext (fun h5 : term23 => @lem1947138 h1 h2 h3 h4) (fun h5 : False => @lem1946252 h3)). Qed.
Lemma lem1947140 (h1 : term10) (h2 : term26) (h3 : term23) (h4 : term3) : False.
Proof. exact (EQ_MP (@lem1947139 h1 h2 h3 h4) (@lem1946252 h3)). Qed.
Lemma lem1947141 (h1 : term26) (h2 : term23) (h3 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1947140 h0 h1 h2 h3). Qed.
Lemma lem1947142 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1947143 (h1 : term26) (h2 : term23) (h3 : term3) : term9.
Proof. exact (EQ_MP (@lem1947142) (@lem1947141 h1 h2 h3)). Qed.
Lemma lem1947144 (h1 : term26) (h2 : term3) : term13.
Proof. exact (fun h0 : term23 => @lem1947143 h1 h0 h2). Qed.
Lemma lem1947145 (h1 : term3) : term16.
Proof. exact (fun h0 : term26 => @lem1947144 h0 h1). Qed.
Lemma lem1947146 : term18.
Proof. exact (fun h0 : term3 => @lem1947145 h0). Qed.
Lemma lem1947147 : term4.
Proof. exact (EQ_MP (@lem1945994) (@lem1947146)). Qed.
Lemma lem1947149 : term4.
Proof. exact (@lem1945878 (@lem1947147)). Qed.
Lemma lem1947150 (h1 : term3) : term15.
Proof. exact (@lem1947149 (@lem1945863 h1)). Qed.
Lemma lem1947151 (h1 : term3) : term12.
Proof. exact (@lem1947150 h1 (@lem1945848)). Qed.
Lemma lem1947152 (h1 : term3) : term8.
Proof. exact (@lem1947151 h1 (@lem1382902)). Qed.
Lemma lem1947153 (h1 : term3) : False.
Proof. exact (@lem1947152 h1 (@lem1383497)). Qed.
Lemma lem1947154 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1947153 h1) (fun h2 : False => @lem1945863 h1)). Qed.
Lemma lem1947155 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1947154 h1) (@lem1945863 h1)). Qed.
Lemma lem1947156 : term2.
Proof. exact (fun h0 : term3 => @lem1947155 h0). Qed.
Lemma lem1947157 : term1.
Proof. exact (EQ_MP (@lem1945862) (@lem1947156)). Qed.
