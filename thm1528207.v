Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1528207_term_abbrevs.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1482702_spec.
Require Import thm1482981_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483458_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483554_spec.
Lemma lem1527976 : term0 = term1.
Proof. exact (@lem1483554 term2 term3). Qed.
Lemma lem1527982 : term4 = term5.
Proof. exact (@lem1483519 term2 term3). Qed.
Lemma lem1527984 (x : nat) : (term6 x) = term3.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1527985 : term7 = term3.
Proof. exact (@lem1527984 term8). Qed.
Lemma lem1527986 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1527987 : term5 = term10.
Proof. exact (MK_COMB (@lem1527986) (@lem1527985)). Qed.
Lemma lem1527988 : term10 = term2.
Proof. exact (@lem1483450 term2). Qed.
Lemma lem1527989 : term5 = term2.
Proof. exact (TRANS (@lem1527987) (@lem1527988)). Qed.
Lemma lem1527991 : term4 = term2.
Proof. exact (TRANS (@lem1527982) (@lem1527989)). Qed.
Lemma lem1527992 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1527993 : term11 = term12.
Proof. exact (MK_COMB (@lem1527992) (@lem1527991)). Qed.
Lemma lem1527996 : term12 = term13.
Proof. exact (@lem1483512 term2). Qed.
Lemma lem1527997 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1527998 : (term11 = term12) = (term11 = term13).
Proof. exact (MK_COMB (@lem1527997) (@lem1527996)). Qed.
Lemma lem1527999 : term11 = term13.
Proof. exact (EQ_MP (@lem1527998) (@lem1527993)). Qed.
Lemma lem1528000 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528001 : term15 = term16.
Proof. exact (MK_COMB (@lem1528000) (@lem1527999)). Qed.
Lemma lem1528002 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1528003 : term17 = term18.
Proof. exact (MK_COMB (@lem1528001) (@lem1528002)). Qed.
Lemma lem1528004 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528005 : term19 = term20.
Proof. exact (MK_COMB (@lem1528004) (@lem1527991)). Qed.
Lemma lem1528006 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1528007 : term21 = term22.
Proof. exact (MK_COMB (@lem1528005) (@lem1528006)). Qed.
Lemma lem1528008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1528009 : term23 = term24.
Proof. exact (MK_COMB (@lem1528008) (@lem1528007)). Qed.
Lemma lem1528010 : term1 = term25.
Proof. exact (MK_COMB (@lem1528009) (@lem1528003)). Qed.
Lemma lem1528024 : term0 = term25.
Proof. exact (TRANS (@lem1527976) (@lem1528010)). Qed.
Lemma lem1528026 : term26 = term22.
Proof. exact (eq_refl term26). Qed.
Lemma lem1528027 : term22 = term26.
Proof. exact (SYM (@lem1528026)). Qed.
Lemma lem1528028 : term26 = term27.
Proof. exact (@lem1482981 term28 term3). Qed.
Lemma lem1528029 : term22 = term27.
Proof. exact (TRANS (@lem1528027) (@lem1528028)). Qed.
Lemma lem1528030 : term29 = term30.
Proof. exact (eq_refl term29). Qed.
Lemma lem1528031 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1528032 : term32 = term33.
Proof. exact (MK_COMB (@lem1528031) (@lem1528030)). Qed.
Lemma lem1528033 : term34 = term35.
Proof. exact (eq_refl term34). Qed.
Lemma lem1528034 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1528035 : term37 = term38.
Proof. exact (MK_COMB (@lem1528034) (@lem1528033)). Qed.
Lemma lem1528036 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1528037 : term39 = term40.
Proof. exact (MK_COMB (@lem1528036) (@lem1528035)). Qed.
Lemma lem1528038 : term27 = term41.
Proof. exact (MK_COMB (@lem1528037) (@lem1528032)). Qed.
Lemma lem1528039 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1528040 : (term22 = term27) = (term22 = term41).
Proof. exact (MK_COMB (@lem1528039) (@lem1528038)). Qed.
Lemma lem1528041 : term22 = term41.
Proof. exact (EQ_MP (@lem1528040) (@lem1528029)). Qed.
Lemma lem1528042 : term43 = term44.
Proof. exact (@lem1483527 term3 term3). Qed.
Lemma lem1528048 : term45 = term46.
Proof. exact (@lem1483519 term3 term3). Qed.
Lemma lem1528050 (x : nat) : (term6 x) = term3.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1528051 : term7 = term3.
Proof. exact (@lem1528050 term8). Qed.
Lemma lem1528052 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1528053 : term46 = term48.
Proof. exact (MK_COMB (@lem1528052) (@lem1528051)). Qed.
Lemma lem1528054 : term48 = term3.
Proof. exact (@lem1483448 term3). Qed.
Lemma lem1528055 : term46 = term3.
Proof. exact (TRANS (@lem1528053) (@lem1528054)). Qed.
Lemma lem1528057 : term45 = term3.
Proof. exact (TRANS (@lem1528048) (@lem1528055)). Qed.
Lemma lem1528058 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1528059 : term49 = term50.
Proof. exact (MK_COMB (@lem1528058) (@lem1528057)). Qed.
Lemma lem1528060 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1528061 : term44 = term43.
Proof. exact (MK_COMB (@lem1528059) (@lem1528060)). Qed.
Lemma lem1528062 : term43 = term43.
Proof. exact (TRANS (@lem1528042) (@lem1528061)). Qed.
Lemma lem1528063 : term35 = term51.
Proof. exact (@lem1483525 term3 term3). Qed.
Lemma lem1528069 : term45 = term46.
Proof. exact (@lem1483519 term3 term3). Qed.
Lemma lem1528071 (x : nat) : (term6 x) = term3.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1528072 : term7 = term3.
Proof. exact (@lem1528071 term8). Qed.
Lemma lem1528073 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1528074 : term46 = term48.
Proof. exact (MK_COMB (@lem1528073) (@lem1528072)). Qed.
Lemma lem1528075 : term48 = term3.
Proof. exact (@lem1483448 term3). Qed.
Lemma lem1528076 : term46 = term3.
Proof. exact (TRANS (@lem1528074) (@lem1528075)). Qed.
Lemma lem1528078 : term45 = term3.
Proof. exact (TRANS (@lem1528069) (@lem1528076)). Qed.
Lemma lem1528079 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528080 : term52 = term53.
Proof. exact (MK_COMB (@lem1528079) (@lem1528078)). Qed.
Lemma lem1528081 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1528082 : term51 = term35.
Proof. exact (MK_COMB (@lem1528080) (@lem1528081)). Qed.
Lemma lem1528083 : term35 = term35.
Proof. exact (TRANS (@lem1528063) (@lem1528082)). Qed.
Lemma lem1528084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1528085 : term36 = term36.
Proof. exact (MK_COMB (@lem1528084) (@lem1528062)). Qed.
Lemma lem1528086 : term38 = term38.
Proof. exact (MK_COMB (@lem1528085) (@lem1528083)). Qed.
Lemma lem1528087 : term30 = term54.
Proof. exact (@lem1483525 term55 term3). Qed.
Lemma lem1528088 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1528092 : term55 = term7.
Proof. exact (@lem1483512 term3). Qed.
Lemma lem1528094 (x : nat) : (term6 x) = term3.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1528095 : term7 = term3.
Proof. exact (@lem1528094 term8). Qed.
Lemma lem1528097 : term55 = term3.
Proof. exact (TRANS (@lem1528092) (@lem1528095)). Qed.
Lemma lem1528098 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1528099 : term56 = term57.
Proof. exact (MK_COMB (@lem1528098) (@lem1528097)). Qed.
Lemma lem1528100 : term58 = term45.
Proof. exact (MK_COMB (@lem1528099) (@lem1528088)). Qed.
Lemma lem1528101 : term45 = term46.
Proof. exact (@lem1483519 term3 term3). Qed.
Lemma lem1528103 (x : nat) : (term6 x) = term3.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1528104 : term7 = term3.
Proof. exact (@lem1528103 term8). Qed.
Lemma lem1528105 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1528106 : term46 = term48.
Proof. exact (MK_COMB (@lem1528105) (@lem1528104)). Qed.
Lemma lem1528107 : term48 = term3.
Proof. exact (@lem1483448 term3). Qed.
Lemma lem1528108 : term46 = term3.
Proof. exact (TRANS (@lem1528106) (@lem1528107)). Qed.
Lemma lem1528109 : term45 = term3.
Proof. exact (TRANS (@lem1528101) (@lem1528108)). Qed.
Lemma lem1528110 : term58 = term3.
Proof. exact (TRANS (@lem1528100) (@lem1528109)). Qed.
Lemma lem1528111 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528112 : term59 = term53.
Proof. exact (MK_COMB (@lem1528111) (@lem1528110)). Qed.
Lemma lem1528113 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1528114 : term54 = term35.
Proof. exact (MK_COMB (@lem1528112) (@lem1528113)). Qed.
Lemma lem1528115 : term30 = term35.
Proof. exact (TRANS (@lem1528087) (@lem1528114)). Qed.
Lemma lem1528116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1528117 : term31 = term31.
Proof. exact (MK_COMB (@lem1528116) (@lem1528083)). Qed.
Lemma lem1528118 : term33 = term60.
Proof. exact (MK_COMB (@lem1528117) (@lem1528115)). Qed.
Lemma lem1528119 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1528120 : term40 = term40.
Proof. exact (MK_COMB (@lem1528119) (@lem1528086)). Qed.
Lemma lem1528121 : term41 = term61.
Proof. exact (MK_COMB (@lem1528120) (@lem1528118)). Qed.
Lemma lem1528133 : term22 = term61.
Proof. exact (TRANS (@lem1528041) (@lem1528121)). Qed.
Lemma lem1528135 (x : real) (r : real) : (term62 x r) = (term63 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1528136 : term18 = term64.
Proof. exact (@lem1528135 term3 term3). Qed.
Lemma lem1528143 : term65 = term3.
Proof. exact (@lem1483458 term66). Qed.
Lemma lem1528144 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528145 : term67 = term53.
Proof. exact (MK_COMB (@lem1528144) (@lem1528143)). Qed.
Lemma lem1528146 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1528147 : term68 = term35.
Proof. exact (MK_COMB (@lem1528145) (@lem1528146)). Qed.
Lemma lem1528154 : term7 = term3.
Proof. exact (@lem1483458 term69). Qed.
Lemma lem1528155 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528156 : term70 = term53.
Proof. exact (MK_COMB (@lem1528155) (@lem1528154)). Qed.
Lemma lem1528157 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1528158 : term71 = term35.
Proof. exact (MK_COMB (@lem1528156) (@lem1528157)). Qed.
Lemma lem1528159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1528160 : term72 = term31.
Proof. exact (MK_COMB (@lem1528159) (@lem1528158)). Qed.
Lemma lem1528161 : term64 = term60.
Proof. exact (MK_COMB (@lem1528160) (@lem1528147)). Qed.
Lemma lem1528164 : term18 = term60.
Proof. exact (TRANS (@lem1528136) (@lem1528161)). Qed.
Lemma lem1528165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1528166 : term24 = term73.
Proof. exact (MK_COMB (@lem1528165) (@lem1528133)). Qed.
Lemma lem1528167 : term25 = term74.
Proof. exact (MK_COMB (@lem1528166) (@lem1528164)). Qed.
Lemma lem1528168 (h1 : term74) : term74.
Proof. exact (h1). Qed.
Lemma lem1528169 (h1 : term61) : term61.
Proof. exact (h1). Qed.
Lemma lem1528170 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1528171 (h1 : term38) : term35.
Proof. exact (proj2 (@lem1528170 h1)). Qed.
Lemma lem1528174 (n : nat) (m : nat) : (term75 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1528175 : term35 = term76.
Proof. exact (@lem1528174 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1528176 : term76 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1528177 : term35 = False.
Proof. exact (TRANS (@lem1528175) (@lem1528176)). Qed.
Lemma lem1528178 (h1 : term38) : False.
Proof. exact (EQ_MP (@lem1528177) (@lem1528171 h1)). Qed.
Lemma lem1528179 (h1 : term60) : term60.
Proof. exact (h1). Qed.
Lemma lem1528180 (h1 : term60) : term35.
Proof. exact (proj2 (@lem1528179 h1)). Qed.
Lemma lem1528183 (n : nat) (m : nat) : (term75 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1528184 : term35 = term76.
Proof. exact (@lem1528183 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1528185 : term76 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1528186 : term35 = False.
Proof. exact (TRANS (@lem1528184) (@lem1528185)). Qed.
Lemma lem1528187 (h1 : term60) : False.
Proof. exact (EQ_MP (@lem1528186) (@lem1528180 h1)). Qed.
Lemma lem1528188 (h1 : term61) : False.
Proof. exact (or_elim (@lem1528169 h1) (fun h0 : term38 => @lem1528178 h0) (fun h0 : term60 => @lem1528187 h0)). Qed.
Lemma lem1528189 (h1 : term60) : term60.
Proof. exact (h1). Qed.
Lemma lem1528190 (h1 : term60) : term35.
Proof. exact (proj2 (@lem1528189 h1)). Qed.
Lemma lem1528193 (n : nat) (m : nat) : (term75 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1528194 : term35 = term76.
Proof. exact (@lem1528193 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1528195 : term76 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1528196 : term35 = False.
Proof. exact (TRANS (@lem1528194) (@lem1528195)). Qed.
Lemma lem1528197 (h1 : term60) : False.
Proof. exact (EQ_MP (@lem1528196) (@lem1528190 h1)). Qed.
Lemma lem1528198 (h1 : term74) : False.
Proof. exact (or_elim (@lem1528168 h1) (fun h0 : term61 => @lem1528188 h0) (fun h0 : term60 => @lem1528197 h0)). Qed.
Lemma lem1528199 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem1528200 (h1 : term25) : term74.
Proof. exact (EQ_MP (@lem1528167) (@lem1528199 h1)). Qed.
Lemma lem1528201 (h1 : term25) : term74 = False.
Proof. exact (prop_ext (fun h2 : term74 => @lem1528198 h2) (fun h2 : False => @lem1528200 h1)). Qed.
Lemma lem1528202 (h1 : term25) : False.
Proof. exact (EQ_MP (@lem1528201 h1) (@lem1528200 h1)). Qed.
Lemma lem1528203 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1528204 (h1 : term0) : term25.
Proof. exact (EQ_MP (@lem1528024) (@lem1528203 h1)). Qed.
Lemma lem1528205 (h1 : term0) : term25 = False.
Proof. exact (prop_ext (fun h2 : term25 => @lem1528202 h2) (fun h2 : False => @lem1528204 h1)). Qed.
Lemma lem1528206 (h1 : term0) : False.
Proof. exact (EQ_MP (@lem1528205 h1) (@lem1528204 h1)). Qed.
Lemma lem1528207 : term77.
Proof. exact (fun h0 : term0 => @lem1528206 h0). Qed.
