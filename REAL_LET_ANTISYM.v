Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LET_ANTISYM_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483523_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm16933_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Lemma lem1495953 (y : real) (x : real) : (term0 y x) = (term1 y x).
Proof. exact (@lem16933 (term1 y x)). Qed.
Lemma lem1495954 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1495955 (x : real) : (term4 x) = (term5 x).
Proof. exact (@lem1495954 (term6 x)). Qed.
Lemma lem1495956 (y : real) (x : real) : (term7 x y) = (term8 y x).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1495957 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1495958 (y : real) (x : real) : (term9 x y) = (term0 y x).
Proof. exact (MK_COMB (@lem1495957) (@lem1495956 y x)). Qed.
Lemma lem1495959 (y : real) (x : real) : (term9 x y) = (term1 y x).
Proof. exact (TRANS (@lem1495958 y x) (@lem1495953 y x)). Qed.
Lemma lem1495960 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1495959 y x)). Qed.
Lemma lem1495961 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495962 (x : real) : (term5 x) = (term12 x).
Proof. exact (MK_COMB (@lem1495961) (@lem1495960 x)). Qed.
Lemma lem1495963 (x : real) : (term4 x) = (term12 x).
Proof. exact (TRANS (@lem1495955 x) (@lem1495962 x)). Qed.
Lemma lem1495964 (P : real -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1495965 : term13 = term14.
Proof. exact (@lem1495964 term15). Qed.
Lemma lem1495966 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1495967 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1495968 (x : real) : (term18 x) = (term4 x).
Proof. exact (MK_COMB (@lem1495967) (@lem1495966 x)). Qed.
Lemma lem1495969 (x : real) : (term18 x) = (term12 x).
Proof. exact (TRANS (@lem1495968 x) (@lem1495963 x)). Qed.
Lemma lem1495970 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1495969 x)). Qed.
Lemma lem1495971 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495972 : term14 = term21.
Proof. exact (MK_COMB (@lem1495971) (@lem1495970)). Qed.
Lemma lem1495974 : term13 = term21.
Proof. exact (TRANS (@lem1495965) (@lem1495972)). Qed.
Lemma lem1495979 (y : real) (x : real) : (term1 y x) = (term1 y x).
Proof. exact (eq_refl (term1 y x)). Qed.
Lemma lem1495980 (x : real) : (term11 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1495979 y x)). Qed.
Lemma lem1495981 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495982 (x : real) : (term12 x) = (term12 x).
Proof. exact (MK_COMB (@lem1495981) (@lem1495980 x)). Qed.
Lemma lem1495983 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1495982 x)). Qed.
Lemma lem1495984 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495985 : term21 = term21.
Proof. exact (MK_COMB (@lem1495984) (@lem1495983)). Qed.
Lemma lem1495986 : term13 = term21.
Proof. exact (TRANS (@lem1495974) (@lem1495985)). Qed.
Lemma lem1495987 (y : real) (x : real) : (real_le x y) = (term22 y x).
Proof. exact (@lem1483523 y x). Qed.
Lemma lem1495993 (y : real) (x : real) : (real_sub y x) = (term23 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1495998 (x : real) (y : real) : (term23 y x) = (term24 x y).
Proof. exact (@lem1483488 (term25 x) y). Qed.
Lemma lem1496000 (x : real) (y : real) : (real_sub y x) = (term24 x y).
Proof. exact (TRANS (@lem1495993 y x) (@lem1495998 x y)). Qed.
Lemma lem1496001 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1496002 (x : real) (y : real) : (term26 y x) = (term27 x y).
Proof. exact (MK_COMB (@lem1496001) (@lem1496000 x y)). Qed.
Lemma lem1496003 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1496004 (x : real) (y : real) : (term22 y x) = (term29 x y).
Proof. exact (MK_COMB (@lem1496002 x y) (@lem1496003)). Qed.
Lemma lem1496005 (x : real) (y : real) : (real_le x y) = (term29 x y).
Proof. exact (TRANS (@lem1495987 y x) (@lem1496004 x y)). Qed.
Lemma lem1496006 (x : real) (y : real) : (real_lt y x) = (term30 x y).
Proof. exact (@lem1483521 x y). Qed.
Lemma lem1496019 (x : real) (y : real) : (real_sub x y) = (term23 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1496020 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1496021 (x : real) (y : real) : (term31 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1496020) (@lem1496019 x y)). Qed.
Lemma lem1496022 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1496023 (x : real) (y : real) : (term30 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1496021 x y) (@lem1496022)). Qed.
Lemma lem1496024 (x : real) (y : real) : (real_lt y x) = (term33 x y).
Proof. exact (TRANS (@lem1496006 x y) (@lem1496023 x y)). Qed.
Lemma lem1496025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1496026 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1496025) (@lem1496005 x y)). Qed.
Lemma lem1496027 (x : real) (y : real) : (term1 y x) = (term36 x y).
Proof. exact (MK_COMB (@lem1496026 x y) (@lem1496024 x y)). Qed.
Lemma lem1496028 (x : real) : (term11 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1496027 x y)). Qed.
Lemma lem1496029 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496030 (x : real) : (term12 x) = (term38 x).
Proof. exact (MK_COMB (@lem1496029) (@lem1496028 x)). Qed.
Lemma lem1496031 : term20 = term39.
Proof. exact (fun_ext (fun x : real => @lem1496030 x)). Qed.
Lemma lem1496032 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496033 : term21 = term40.
Proof. exact (MK_COMB (@lem1496032) (@lem1496031)). Qed.
Lemma lem1496092 : term13 = term40.
Proof. exact (TRANS (@lem1495986) (@lem1496033)). Qed.
Lemma lem1496099 (x : real) (y : real) : (term36 x y) = (term36 x y).
Proof. exact (eq_refl (term36 x y)). Qed.
Lemma lem1496100 (x : real) : (term37 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1496099 x y)). Qed.
Lemma lem1496101 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496102 (x : real) : (term38 x) = (term38 x).
Proof. exact (MK_COMB (@lem1496101) (@lem1496100 x)). Qed.
Lemma lem1496103 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1496102 x)). Qed.
Lemma lem1496104 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496105 : term40 = term40.
Proof. exact (MK_COMB (@lem1496104) (@lem1496103)). Qed.
Lemma lem1496106 : term13 = term40.
Proof. exact (TRANS (@lem1496092) (@lem1496105)). Qed.
Lemma lem1496110 (x : real) (y : real) (h1 : term36 x y) : term36 x y.
Proof. exact (h1). Qed.
Lemma lem1496111 (x : real) (y : real) (h1 : term36 x y) : term33 x y.
Proof. exact (proj2 (@lem1496110 x y h1)). Qed.
Lemma lem1496112 (x : real) (y : real) (h1 : term36 x y) : term29 x y.
Proof. exact (proj1 (@lem1496110 x y h1)). Qed.
Lemma lem1496114 (n : nat) (m : nat) : (term41 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1496115 : term42 = term43.
Proof. exact (@lem1496114 (NUMERAL 0) term44). Qed.
Lemma lem1496116 : term45 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1496117 (h1 : term45 = (BIT1 0)) : term43 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1496118 : (term45 = (BIT1 0)) = (term43 = True).
Proof. exact (prop_ext (fun h1 : term45 = (BIT1 0) => @lem1496117 h1) (fun h1 : term43 = True => @lem1496116)). Qed.
Lemma lem1496119 : term43 = True.
Proof. exact (EQ_MP (@lem1496118) (@lem1496116)). Qed.
Lemma lem1496120 : term42 = True.
Proof. exact (TRANS (@lem1496115) (@lem1496119)). Qed.
Lemma lem1496121 : True = term42.
Proof. exact (SYM (@lem1496120)). Qed.
Lemma lem1496122 : term42.
Proof. exact (EQ_MP (@lem1496121) (@lem0)). Qed.
Lemma lem1496123 (x : real) (y : real) (h1 : term36 x y) : term46 x y.
Proof. exact (conj (@lem1496122) (@lem1496112 x y h1)). Qed.
Lemma lem1496125 (x : real) (y : real) : term47 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1496126 (x : real) (y : real) : term48 x y.
Proof. exact (@lem1496125 term49 (term24 x y)). Qed.
Lemma lem1496127 (x : real) (y : real) (h1 : term36 x y) : term50 x y.
Proof. exact (@lem1496126 x y (@lem1496123 x y h1)). Qed.
Lemma lem1496128 (x : real) (y : real) : (term51 x y) = (term24 x y).
Proof. exact (@lem1483460 (term24 x y)). Qed.
Lemma lem1496129 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1496130 (x : real) (y : real) : (term52 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1496129) (@lem1496128 x y)). Qed.
Lemma lem1496131 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1496132 (x : real) (y : real) : (term50 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1496130 x y) (@lem1496131)). Qed.
Lemma lem1496133 (x : real) (y : real) (h1 : term36 x y) : term29 x y.
Proof. exact (EQ_MP (@lem1496132 x y) (@lem1496127 x y h1)). Qed.
Lemma lem1496135 (n : nat) (m : nat) : (term41 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1496136 : term42 = term43.
Proof. exact (@lem1496135 (NUMERAL 0) term44). Qed.
Lemma lem1496137 : term45 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1496138 (h1 : term45 = (BIT1 0)) : term43 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1496139 : (term45 = (BIT1 0)) = (term43 = True).
Proof. exact (prop_ext (fun h1 : term45 = (BIT1 0) => @lem1496138 h1) (fun h1 : term43 = True => @lem1496137)). Qed.
Lemma lem1496140 : term43 = True.
Proof. exact (EQ_MP (@lem1496139) (@lem1496137)). Qed.
Lemma lem1496141 : term42 = True.
Proof. exact (TRANS (@lem1496136) (@lem1496140)). Qed.
Lemma lem1496142 : True = term42.
Proof. exact (SYM (@lem1496141)). Qed.
Lemma lem1496143 : term42.
Proof. exact (EQ_MP (@lem1496142) (@lem0)). Qed.
Lemma lem1496144 (x : real) (y : real) (h1 : term36 x y) : term53 x y.
Proof. exact (conj (@lem1496143) (@lem1496111 x y h1)). Qed.
Lemma lem1496146 (x : real) (y : real) : term54 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1496147 (x : real) (y : real) : term55 x y.
Proof. exact (@lem1496146 term49 (term23 x y)). Qed.
Lemma lem1496148 (x : real) (y : real) (h1 : term36 x y) : term56 x y.
Proof. exact (@lem1496147 x y (@lem1496144 x y h1)). Qed.
Lemma lem1496149 (x : real) (y : real) : (term57 x y) = (term23 x y).
Proof. exact (@lem1483460 (term23 x y)). Qed.
Lemma lem1496150 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1496151 (x : real) (y : real) : (term58 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1496150) (@lem1496149 x y)). Qed.
Lemma lem1496152 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1496153 (x : real) (y : real) : (term56 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1496151 x y) (@lem1496152)). Qed.
Lemma lem1496154 (x : real) (y : real) (h1 : term36 x y) : term33 x y.
Proof. exact (EQ_MP (@lem1496153 x y) (@lem1496148 x y h1)). Qed.
Lemma lem1496155 (x : real) (y : real) (h1 : term36 x y) : term59 x y.
Proof. exact (conj (@lem1496154 x y h1) (@lem1496133 x y h1)). Qed.
Lemma lem1496157 (x : real) (y : real) : term60 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1496158 (x : real) (y : real) : term61 x y.
Proof. exact (@lem1496157 (term23 x y) (term24 x y)). Qed.
Lemma lem1496159 (x : real) (y : real) (h1 : term36 x y) : term62 x y.
Proof. exact (@lem1496158 x y (@lem1496155 x y h1)). Qed.
Lemma lem1496160 (x : real) (y : real) : (term63 x y) = (term64 x y).
Proof. exact (@lem1483480 x (term25 x) (term25 y) y). Qed.
Lemma lem1496161 (x : real) : (term65 x) = (term66 x).
Proof. exact (@lem1483442 term67 x). Qed.
Lemma lem1496163 (m : nat) : (term68 m) = term28.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1496164 : term69 = term28.
Proof. exact (@lem1496163 term44). Qed.
Lemma lem1496165 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1496166 : term70 = term71.
Proof. exact (MK_COMB (@lem1496165) (@lem1496164)). Qed.
Lemma lem1496167 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1496168 (x : real) : (term66 x) = (term72 x).
Proof. exact (MK_COMB (@lem1496166) (@lem1496167 x)). Qed.
Lemma lem1496169 (x : real) : (term65 x) = (term72 x).
Proof. exact (TRANS (@lem1496161 x) (@lem1496168 x)). Qed.
Lemma lem1496170 (x : real) : (term72 x) = term28.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1496171 (x : real) : (term65 x) = term28.
Proof. exact (TRANS (@lem1496169 x) (@lem1496170 x)). Qed.
Lemma lem1496172 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1496173 (x : real) : (term73 x) = term74.
Proof. exact (MK_COMB (@lem1496172) (@lem1496171 x)). Qed.
Lemma lem1496174 (y : real) : (term75 y) = (term66 y).
Proof. exact (@lem1483440 term67 y). Qed.
Lemma lem1496176 (m : nat) : (term68 m) = term28.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1496177 : term69 = term28.
Proof. exact (@lem1496176 term44). Qed.
Lemma lem1496178 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1496179 : term70 = term71.
Proof. exact (MK_COMB (@lem1496178) (@lem1496177)). Qed.
Lemma lem1496180 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1496181 (y : real) : (term66 y) = (term72 y).
Proof. exact (MK_COMB (@lem1496179) (@lem1496180 y)). Qed.
Lemma lem1496182 (y : real) : (term75 y) = (term72 y).
Proof. exact (TRANS (@lem1496174 y) (@lem1496181 y)). Qed.
Lemma lem1496183 (y : real) : (term72 y) = term28.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1496184 (y : real) : (term75 y) = term28.
Proof. exact (TRANS (@lem1496182 y) (@lem1496183 y)). Qed.
Lemma lem1496185 (x : real) (y : real) : (term64 x y) = term76.
Proof. exact (MK_COMB (@lem1496173 x) (@lem1496184 y)). Qed.
Lemma lem1496186 (x : real) (y : real) : (term63 x y) = term76.
Proof. exact (TRANS (@lem1496160 x y) (@lem1496185 x y)). Qed.
Lemma lem1496187 : term76 = term28.
Proof. exact (@lem1483448 term28). Qed.
Lemma lem1496188 (x : real) (y : real) : (term63 x y) = term28.
Proof. exact (TRANS (@lem1496186 x y) (@lem1496187)). Qed.
Lemma lem1496189 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1496190 (x : real) (y : real) : (term77 x y) = term78.
Proof. exact (MK_COMB (@lem1496189) (@lem1496188 x y)). Qed.
Lemma lem1496191 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1496192 (x : real) (y : real) : (term62 x y) = term79.
Proof. exact (MK_COMB (@lem1496190 x y) (@lem1496191)). Qed.
Lemma lem1496193 (x : real) (y : real) (h1 : term36 x y) : term79.
Proof. exact (EQ_MP (@lem1496192 x y) (@lem1496159 x y h1)). Qed.
Lemma lem1496195 (n : nat) (m : nat) : (term41 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1496196 : term79 = term80.
Proof. exact (@lem1496195 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1496197 : term80 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1496198 : term79 = False.
Proof. exact (TRANS (@lem1496196) (@lem1496197)). Qed.
Lemma lem1496199 (x : real) (y : real) (h1 : term36 x y) : False.
Proof. exact (EQ_MP (@lem1496198) (@lem1496193 x y h1)). Qed.
Lemma lem1496201 (x : real) (y : real) (h1 : term36 x y) : term36 x y.
Proof. exact (h1). Qed.
Lemma lem1496202 (x : real) (y : real) (h1 : term36 x y) : (term36 x y) = False.
Proof. exact (prop_ext (fun h2 : term36 x y => @lem1496199 x y h1) (fun h2 : False => @lem1496201 x y h1)). Qed.
Lemma lem1496203 (x : real) (y : real) (h1 : term36 x y) : False.
Proof. exact (EQ_MP (@lem1496202 x y h1) (@lem1496201 x y h1)). Qed.
Lemma lem1496204 (x : real) (h1 : term38 x) : term38 x.
Proof. exact (h1). Qed.
Lemma lem1496205 (x : real) (h1 : term38 x) : False.
Proof. exact (ex_elim (@lem1496204 x h1) (fun y : real => fun h0 : term37 x y => @lem1496203 x y h0)). Qed.
Lemma lem1496206 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1496207 (h1 : term40) : False.
Proof. exact (ex_elim (@lem1496206 h1) (fun x : real => fun h0 : term39 x => @lem1496205 x h0)). Qed.
Lemma lem1496208 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1496209 (h1 : term13) : term40.
Proof. exact (EQ_MP (@lem1496106) (@lem1496208 h1)). Qed.
Lemma lem1496210 (h1 : term13) : term40 = False.
Proof. exact (prop_ext (fun h2 : term40 => @lem1496207 h2) (fun h2 : False => @lem1496209 h1)). Qed.
Lemma lem1496211 (h1 : term13) : False.
Proof. exact (EQ_MP (@lem1496210 h1) (@lem1496209 h1)). Qed.
Lemma lem1496212 : term81.
Proof. exact (fun h0 : term13 => @lem1496211 h0). Qed.
Lemma lem1496213 : term82.
Proof. exact (@lem1386578 term83). Qed.
Lemma lem1496214 : term83.
Proof. exact (@lem1496213 (@lem1496212)). Qed.
