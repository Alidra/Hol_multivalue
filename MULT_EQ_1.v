Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MULT_EQ_1_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import ADD_EQ_0_spec.
Require Import BIT1_THM_spec.
Require Import BOOL_CASES_AX_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_EQ_0_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem84997 (m : nat) : term0 m.
Proof. exact (@lem83870 m). Qed.
Lemma lem84998 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem84999 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem84998 m) (@lem84997 m)). Qed.
Lemma lem85000 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem84999 m n). Qed.
Lemma lem85001 (m : nat) (n : nat) : (term2 m n) = (((Nat.mul m n) = (NUMERAL 0)) = (term3 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem85003 (m : nat) : term4 m.
Proof. exact (@lem79432 m). Qed.
Lemma lem85004 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem85005 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem85004 m) (@lem85003 m)). Qed.
Lemma lem85006 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem85005 m n). Qed.
Lemma lem85007 (m : nat) (n : nat) : (term6 m n) = (((Nat.add m n) = (NUMERAL 0)) = (term7 m n)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem85009 (m : nat) : term8 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem85010 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem85011 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem85010 m) (@lem85009 m)). Qed.
Lemma lem85012 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem85011 m n). Qed.
Lemma lem85013 (m : nat) (n : nat) : (term10 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem85017 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem85018 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem85017 n h1)). Qed.
Lemma lem85019 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem85020 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem85019 n h1)). Qed.
Lemma lem85021 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem85018 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem85020 n h1)). Qed.
Lemma lem85022 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem85023 (n : nat) : (term11 n) = (term12 n).
Proof. exact (MK_COMB (@lem85022) (@lem85021 n)). Qed.
Lemma lem85024 : term13 = term14.
Proof. exact (fun_ext (fun n : nat => @lem85023 n)). Qed.
Lemma lem85025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem85026 : term15 = term16.
Proof. exact (MK_COMB (@lem85025) (@lem85024)). Qed.
Lemma lem85027 : term16.
Proof. exact (EQ_MP (@lem85026) (@lem75570)). Qed.
Lemma lem85028 (n : nat) : term17 n.
Proof. exact (@lem85027 n). Qed.
Lemma lem85029 (n : nat) : (term17 n) = (term12 n).
Proof. exact (eq_refl (term17 n)). Qed.
Lemma lem85030 (n : nat) : term12 n.
Proof. exact (EQ_MP (@lem85029 n) (@lem85028 n)). Qed.
Lemma lem85031 (n : nat) : term18 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem85044 (n : nat) : term19 n.
Proof. exact (@lem80210 n). Qed.
Lemma lem85045 (n : nat) : (term19 n) = ((term20 n) = (term21 n)).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem85050 : term22.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem85051 : term23.
Proof. exact (proj2 (@lem85050)). Qed.
Lemma lem85052 : term24.
Proof. exact (proj2 (@lem85051)). Qed.
Lemma lem85053 (m : nat) : term25 m.
Proof. exact (@lem85052 m). Qed.
Lemma lem85054 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem85055 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem85054 m) (@lem85053 m)). Qed.
Lemma lem85056 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem85055 m n). Qed.
Lemma lem85057 (m : nat) (n : nat) : (term27 m n) = ((term28 m n) = (term29 m n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem85066 : term30.
Proof. exact (proj1 (@lem85050)). Qed.
Lemma lem85067 (m : nat) : term31 m.
Proof. exact (@lem85066 m). Qed.
Lemma lem85068 (m : nat) : (term31 m) = ((term32 m) = m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem85070 : term33.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem85071 (n : nat) : term34 n.
Proof. exact (@lem85070 n). Qed.
Lemma lem85072 (n : nat) : (term34 n) = ((term35 n) = n).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem85074 : term36.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem85075 : term37.
Proof. exact (proj2 (@lem85074)). Qed.
Lemma lem85076 : term38.
Proof. exact (proj2 (@lem85075)). Qed.
Lemma lem85077 : term39.
Proof. exact (proj2 (@lem85076)). Qed.
Lemma lem85078 : term40.
Proof. exact (proj2 (@lem85077)). Qed.
Lemma lem85079 (m : nat) : term41 m.
Proof. exact (@lem85078 m). Qed.
Lemma lem85080 (m : nat) : (term41 m) = (term42 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem85081 (m : nat) : term42 m.
Proof. exact (EQ_MP (@lem85080 m) (@lem85079 m)). Qed.
Lemma lem85082 (m : nat) (n : nat) : term43 m n.
Proof. exact (@lem85081 m n). Qed.
Lemma lem85083 (m : nat) (n : nat) : (term43 m n) = ((term44 m n) = (term45 m n)).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem85085 : term46.
Proof. exact (proj1 (@lem85077)). Qed.
Lemma lem85086 (m : nat) : term47 m.
Proof. exact (@lem85085 m). Qed.
Lemma lem85087 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem85088 (m : nat) : term48 m.
Proof. exact (EQ_MP (@lem85087 m) (@lem85086 m)). Qed.
Lemma lem85089 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem85088 m n). Qed.
Lemma lem85090 (m : nat) (n : nat) : (term49 m n) = ((term50 m n) = (term51 m n)).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem85100 : term52.
Proof. exact (proj1 (@lem85074)). Qed.
Lemma lem85101 (m : nat) : term53 m.
Proof. exact (@lem85100 m). Qed.
Lemma lem85102 (m : nat) : (term53 m) = ((term54 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term53 m)). Qed.
Lemma lem85104 : term55.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem85105 (n : nat) : term56 n.
Proof. exact (@lem85104 n). Qed.
Lemma lem85106 (n : nat) : (term56 n) = ((term57 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term56 n)). Qed.
Lemma lem85109 (P : nat -> Prop) : term58 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem85110 : term59.
Proof. exact (@lem85109 term60). Qed.
Lemma lem85111 : term61 = term62.
Proof. exact (eq_refl term61). Qed.
Lemma lem85112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem85113 : term63 = term64.
Proof. exact (MK_COMB (@lem85112) (@lem85111)). Qed.
Lemma lem85114 (m : nat) : (term65 m) = (term66 m).
Proof. exact (eq_refl (term65 m)). Qed.
Lemma lem85115 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem85116 (m : nat) : (term67 m) = (term68 m).
Proof. exact (MK_COMB (@lem85115) (@lem85114 m)). Qed.
Lemma lem85117 (m : nat) : (term69 m) = (term70 m).
Proof. exact (eq_refl (term69 m)). Qed.
Lemma lem85118 (m : nat) : (term71 m) = (term72 m).
Proof. exact (MK_COMB (@lem85116 m) (@lem85117 m)). Qed.
Lemma lem85119 : term73 = term74.
Proof. exact (fun_ext (fun m : nat => @lem85118 m)). Qed.
Lemma lem85120 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem85121 : term75 = term76.
Proof. exact (MK_COMB (@lem85120) (@lem85119)). Qed.
Lemma lem85122 : term77 = term78.
Proof. exact (MK_COMB (@lem85113) (@lem85121)). Qed.
Lemma lem85123 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem85124 : term79 = term80.
Proof. exact (MK_COMB (@lem85123) (@lem85122)). Qed.
Lemma lem85125 (m : nat) : (term65 m) = (term66 m).
Proof. exact (eq_refl (term65 m)). Qed.
Lemma lem85126 : term81 = term60.
Proof. exact (fun_ext (fun m : nat => @lem85125 m)). Qed.
Lemma lem85127 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem85128 : term82 = term83.
Proof. exact (MK_COMB (@lem85127) (@lem85126)). Qed.
Lemma lem85129 : term59 = term84.
Proof. exact (MK_COMB (@lem85124) (@lem85128)). Qed.
Lemma lem85130 : term84.
Proof. exact (EQ_MP (@lem85129) (@lem85110)). Qed.
Lemma lem85133 (P : nat -> Prop) : term58 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem85134 : term85.
Proof. exact (@lem85133 term86). Qed.
Lemma lem85135 : term87 = ((term88 = term89) = term90).
Proof. exact (eq_refl term87). Qed.
Lemma lem85136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem85137 : term91 = term92.
Proof. exact (MK_COMB (@lem85136) (@lem85135)). Qed.
Lemma lem85138 (n : nat) : (term93 n) = (((term57 n) = term89) = (term94 n)).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem85139 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem85140 (n : nat) : (term95 n) = (term96 n).
Proof. exact (MK_COMB (@lem85139) (@lem85138 n)). Qed.
Lemma lem85141 (n : nat) : (term97 n) = (((term98 n) = term89) = (term99 n)).
Proof. exact (eq_refl (term97 n)). Qed.
Lemma lem85142 (n : nat) : (term100 n) = (term101 n).
Proof. exact (MK_COMB (@lem85140 n) (@lem85141 n)). Qed.
Lemma lem85143 : term102 = term103.
Proof. exact (fun_ext (fun n : nat => @lem85142 n)). Qed.
Lemma lem85144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem85145 : term104 = term105.
Proof. exact (MK_COMB (@lem85144) (@lem85143)). Qed.
Lemma lem85146 : term106 = term107.
Proof. exact (MK_COMB (@lem85137) (@lem85145)). Qed.
Lemma lem85147 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem85148 : term108 = term109.
Proof. exact (MK_COMB (@lem85147) (@lem85146)). Qed.
Lemma lem85149 (n : nat) : (term93 n) = (((term57 n) = term89) = (term94 n)).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem85150 : term110 = term86.
Proof. exact (fun_ext (fun n : nat => @lem85149 n)). Qed.
Lemma lem85151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem85152 : term111 = term62.
Proof. exact (MK_COMB (@lem85151) (@lem85150)). Qed.
Lemma lem85153 : term85 = term112.
Proof. exact (MK_COMB (@lem85148) (@lem85152)). Qed.
Lemma lem85154 : term112.
Proof. exact (EQ_MP (@lem85153) (@lem85134)). Qed.
Lemma lem85157 (P : nat -> Prop) : term58 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem85158 (m : nat) : term113 m.
Proof. exact (@lem85157 (term114 m)). Qed.
Lemma lem85159 (m : nat) : (term115 m) = (((term116 m) = term89) = (term117 m)).
Proof. exact (eq_refl (term115 m)). Qed.
Lemma lem85160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem85161 (m : nat) : (term118 m) = (term119 m).
Proof. exact (MK_COMB (@lem85160) (@lem85159 m)). Qed.
Lemma lem85162 (m : nat) (n : nat) : (term120 m n) = (((term50 m n) = term89) = (term121 m n)).
Proof. exact (eq_refl (term120 m n)). Qed.
Lemma lem85163 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem85164 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (MK_COMB (@lem85163) (@lem85162 m n)). Qed.
Lemma lem85165 (m : nat) (n : nat) : (term124 m n) = (((term125 m n) = term89) = (term126 m n)).
Proof. exact (eq_refl (term124 m n)). Qed.
Lemma lem85166 (m : nat) (n : nat) : (term127 m n) = (term128 m n).
Proof. exact (MK_COMB (@lem85164 m n) (@lem85165 m n)). Qed.
Lemma lem85167 (m : nat) : (term129 m) = (term130 m).
Proof. exact (fun_ext (fun n : nat => @lem85166 m n)). Qed.
Lemma lem85168 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem85169 (m : nat) : (term131 m) = (term132 m).
Proof. exact (MK_COMB (@lem85168) (@lem85167 m)). Qed.
Lemma lem85170 (m : nat) : (term133 m) = (term134 m).
Proof. exact (MK_COMB (@lem85161 m) (@lem85169 m)). Qed.
Lemma lem85171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem85172 (m : nat) : (term135 m) = (term136 m).
Proof. exact (MK_COMB (@lem85171) (@lem85170 m)). Qed.
Lemma lem85173 (m : nat) (n : nat) : (term120 m n) = (((term50 m n) = term89) = (term121 m n)).
Proof. exact (eq_refl (term120 m n)). Qed.
Lemma lem85174 (m : nat) : (term137 m) = (term114 m).
Proof. exact (fun_ext (fun n : nat => @lem85173 m n)). Qed.
Lemma lem85175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem85176 (m : nat) : (term138 m) = (term70 m).
Proof. exact (MK_COMB (@lem85175) (@lem85174 m)). Qed.
Lemma lem85177 (m : nat) : (term113 m) = (term139 m).
Proof. exact (MK_COMB (@lem85172 m) (@lem85176 m)). Qed.
Lemma lem85178 (m : nat) : term139 m.
Proof. exact (EQ_MP (@lem85177 m) (@lem85158 m)). Qed.
Lemma lem85185 (n : nat) : (term57 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem85106 n) (@lem85105 n)). Qed.
Lemma lem85186 : term88 = (NUMERAL 0).
Proof. exact (@lem85185 (NUMERAL 0)). Qed.
Lemma lem85187 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem85188 : term140 = term141.
Proof. exact (MK_COMB (@lem85187) (@lem85186)). Qed.
Lemma lem85190 (n : nat) : (term20 n) = (term21 n).
Proof. exact (EQ_MP (@lem85045 n) (@lem85044 n)). Qed.
Lemma lem85191 : term89 = term142.
Proof. exact (@lem85190 0). Qed.
Lemma lem85193 (n : nat) : (term35 n) = n.
Proof. exact (EQ_MP (@lem85072 n) (@lem85071 n)). Qed.
Lemma lem85194 : term143 = (NUMERAL 0).
Proof. exact (@lem85193 (NUMERAL 0)). Qed.
Lemma lem85195 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem85196 : term142 = term144.
Proof. exact (MK_COMB (@lem85195) (@lem85194)). Qed.
Lemma lem85197 : term89 = term144.
Proof. exact (TRANS (@lem85191) (@lem85196)). Qed.
Lemma lem85198 : (term88 = term89) = ((NUMERAL 0) = term144).
Proof. exact (MK_COMB (@lem85188) (@lem85197)). Qed.
Lemma lem85200 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem85031 n (@lem85030 n)). Qed.
Lemma lem85201 : ((NUMERAL 0) = term144) = False.
Proof. exact (@lem85200 (NUMERAL 0)). Qed.
Lemma lem85202 : (term88 = term89) = False.
Proof. exact (TRANS (@lem85198) (@lem85201)). Qed.
Lemma lem85203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem85204 : term145 = (@eq Prop False).
Proof. exact (MK_COMB (@lem85203) (@lem85202)). Qed.
Lemma lem85206 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem85207 : term90 = ((NUMERAL 0) = term89).
Proof. exact (@lem85206 ((NUMERAL 0) = term89)). Qed.
Lemma lem85211 (n : nat) : (term20 n) = (term21 n).
Proof. exact (EQ_MP (@lem85045 n) (@lem85044 n)). Qed.
Lemma lem85212 : term89 = term142.
Proof. exact (@lem85211 0). Qed.
Lemma lem85214 (n : nat) : (term35 n) = n.
Proof. exact (EQ_MP (@lem85072 n) (@lem85071 n)). Qed.
Lemma lem85215 : term143 = (NUMERAL 0).
Proof. exact (@lem85214 (NUMERAL 0)). Qed.
Lemma lem85216 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem85217 : term142 = term144.
Proof. exact (MK_COMB (@lem85216) (@lem85215)). Qed.
Lemma lem85218 : term89 = term144.
Proof. exact (TRANS (@lem85212) (@lem85217)). Qed.
Lemma lem85219 : term141 = term141.
Proof. exact (eq_refl term141). Qed.
Lemma lem85220 : ((NUMERAL 0) = term89) = ((NUMERAL 0) = term144).
Proof. exact (MK_COMB (@lem85219) (@lem85218)). Qed.
Lemma lem85222 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem85031 n (@lem85030 n)). Qed.
Lemma lem85223 : ((NUMERAL 0) = term144) = False.
Proof. exact (@lem85222 (NUMERAL 0)). Qed.
Lemma lem85224 : ((NUMERAL 0) = term89) = False.
Proof. exact (TRANS (@lem85220) (@lem85223)). Qed.
Lemma lem85225 : term90 = False.
Proof. exact (TRANS (@lem85207) (@lem85224)). Qed.
Lemma lem85226 : ((term88 = term89) = term90) = (False = False).
Proof. exact (MK_COMB (@lem85204) (@lem85225)). Qed.
Lemma lem85228 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem85229 : (False = False) = (~ False).
Proof. exact (@lem85228 False). Qed.
Lemma lem85231 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem85232 : (False = False) = True.
Proof. exact (TRANS (@lem85229) (@lem85231)). Qed.
Lemma lem85233 : ((term88 = term89) = term90) = True.
Proof. exact (TRANS (@lem85226) (@lem85232)). Qed.
Lemma lem85234 : True = ((term88 = term89) = term90).
Proof. exact (SYM (@lem85233)). Qed.
Lemma lem85235 : (term88 = term89) = term90.
Proof. exact (EQ_MP (@lem85234) (@lem0)). Qed.
Lemma lem85241 (n : nat) : (term57 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem85106 n) (@lem85105 n)). Qed.
Lemma lem85242 (n : nat) : (term98 n) = (NUMERAL 0).
Proof. exact (@lem85241 (S n)). Qed.
Lemma lem85243 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem85244 (n : nat) : (term146 n) = term141.
Proof. exact (MK_COMB (@lem85243) (@lem85242 n)). Qed.
Lemma lem85246 (n : nat) : (term20 n) = (term21 n).
Proof. exact (EQ_MP (@lem85045 n) (@lem85044 n)). Qed.
Lemma lem85247 : term89 = term142.
Proof. exact (@lem85246 0). Qed.
Lemma lem85249 (n : nat) : (term35 n) = n.
Proof. exact (EQ_MP (@lem85072 n) (@lem85071 n)). Qed.
Lemma lem85250 : term143 = (NUMERAL 0).
Proof. exact (@lem85249 (NUMERAL 0)). Qed.
Lemma lem85251 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem85252 : term142 = term144.
Proof. exact (MK_COMB (@lem85251) (@lem85250)). Qed.
Lemma lem85253 : term89 = term144.
Proof. exact (TRANS (@lem85247) (@lem85252)). Qed.
Lemma lem85254 (n : nat) : ((term98 n) = term89) = ((NUMERAL 0) = term144).
Proof. exact (MK_COMB (@lem85244 n) (@lem85253)). Qed.
Lemma lem85256 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem85031 n (@lem85030 n)). Qed.
Lemma lem85257 : ((NUMERAL 0) = term144) = False.
Proof. exact (@lem85256 (NUMERAL 0)). Qed.
Lemma lem85258 (n : nat) : ((term98 n) = term89) = False.
Proof. exact (TRANS (@lem85254 n) (@lem85257)). Qed.
Lemma lem85259 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem85260 (n : nat) : (term147 n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem85259) (@lem85258 n)). Qed.
Lemma lem85266 (n : nat) : (term20 n) = (term21 n).
Proof. exact (EQ_MP (@lem85045 n) (@lem85044 n)). Qed.
Lemma lem85267 : term89 = term142.
Proof. exact (@lem85266 0). Qed.
Lemma lem85269 (n : nat) : (term35 n) = n.
Proof. exact (EQ_MP (@lem85072 n) (@lem85071 n)). Qed.
Lemma lem85270 : term143 = (NUMERAL 0).
Proof. exact (@lem85269 (NUMERAL 0)). Qed.
Lemma lem85271 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem85272 : term142 = term144.
Proof. exact (MK_COMB (@lem85271) (@lem85270)). Qed.
Lemma lem85273 : term89 = term144.
Proof. exact (TRANS (@lem85267) (@lem85272)). Qed.
Lemma lem85274 : term141 = term141.
Proof. exact (eq_refl term141). Qed.
Lemma lem85275 : ((NUMERAL 0) = term89) = ((NUMERAL 0) = term144).
Proof. exact (MK_COMB (@lem85274) (@lem85273)). Qed.
Lemma lem85277 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem85031 n (@lem85030 n)). Qed.
Lemma lem85278 : ((NUMERAL 0) = term144) = False.
Proof. exact (@lem85277 (NUMERAL 0)). Qed.
Lemma lem85279 : ((NUMERAL 0) = term89) = False.
Proof. exact (TRANS (@lem85275) (@lem85278)). Qed.
Lemma lem85280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem85281 : term148 = (and False).
Proof. exact (MK_COMB (@lem85280) (@lem85279)). Qed.
Lemma lem85285 (n : nat) : (term20 n) = (term21 n).
Proof. exact (EQ_MP (@lem85045 n) (@lem85044 n)). Qed.
Lemma lem85286 : term89 = term142.
Proof. exact (@lem85285 0). Qed.
Lemma lem85288 (n : nat) : (term35 n) = n.
Proof. exact (EQ_MP (@lem85072 n) (@lem85071 n)). Qed.
Lemma lem85289 : term143 = (NUMERAL 0).
Proof. exact (@lem85288 (NUMERAL 0)). Qed.
Lemma lem85290 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem85291 : term142 = term144.
Proof. exact (MK_COMB (@lem85290) (@lem85289)). Qed.
Lemma lem85292 : term89 = term144.
Proof. exact (TRANS (@lem85286) (@lem85291)). Qed.
Lemma lem85293 (n : nat) : (term149 n) = (term149 n).
Proof. exact (eq_refl (term149 n)). Qed.
Lemma lem85294 (n : nat) : ((S n) = term89) = ((S n) = term144).
Proof. exact (MK_COMB (@lem85293 n) (@lem85292)). Qed.
Lemma lem85297 (n : nat) : (term99 n) = (term150 n).
Proof. exact (MK_COMB (@lem85281) (@lem85294 n)). Qed.
Lemma lem85299 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem85300 (n : nat) : (term150 n) = False.
Proof. exact (@lem85299 ((S n) = term144)). Qed.
Lemma lem85301 (n : nat) : (term99 n) = False.
Proof. exact (TRANS (@lem85297 n) (@lem85300 n)). Qed.
Lemma lem85302 (n : nat) : (((term98 n) = term89) = (term99 n)) = (False = False).
Proof. exact (MK_COMB (@lem85260 n) (@lem85301 n)). Qed.
Lemma lem85304 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem85305 : (False = False) = (~ False).
Proof. exact (@lem85304 False). Qed.
Lemma lem85307 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem85308 : (False = False) = True.
Proof. exact (TRANS (@lem85305) (@lem85307)). Qed.
Lemma lem85309 (n : nat) : (((term98 n) = term89) = (term99 n)) = True.
Proof. exact (TRANS (@lem85302 n) (@lem85308)). Qed.
Lemma lem85310 (n : nat) : True = (((term98 n) = term89) = (term99 n)).
Proof. exact (SYM (@lem85309 n)). Qed.
Lemma lem85311 (n : nat) : ((term98 n) = term89) = (term99 n).
Proof. exact (EQ_MP (@lem85310 n) (@lem0)). Qed.
Lemma lem85317 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (EQ_MP (@lem85090 m n) (@lem85089 m n)). Qed.
Lemma lem85318 (m : nat) : (term116 m) = (term151 m).
Proof. exact (@lem85317 m (NUMERAL 0)). Qed.
Lemma lem85320 (m : nat) : (term32 m) = m.
Proof. exact (EQ_MP (@lem85068 m) (@lem85067 m)). Qed.
Lemma lem85321 (m : nat) : (term151 m) = (term54 m).
Proof. exact (@lem85320 (term54 m)). Qed.
Lemma lem85323 (m : nat) : (term54 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem85102 m) (@lem85101 m)). Qed.
Lemma lem85324 (m : nat) : (term151 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem85321 m) (@lem85323 m)). Qed.
Lemma lem85325 (m : nat) : (term116 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem85318 m) (@lem85324 m)). Qed.
Lemma lem85326 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem85327 (m : nat) : (term152 m) = term141.
Proof. exact (MK_COMB (@lem85326) (@lem85325 m)). Qed.
Lemma lem85329 (n : nat) : (term20 n) = (term21 n).
Proof. exact (EQ_MP (@lem85045 n) (@lem85044 n)). Qed.
Lemma lem85330 : term89 = term142.
Proof. exact (@lem85329 0). Qed.
Lemma lem85332 (n : nat) : (term35 n) = n.
Proof. exact (EQ_MP (@lem85072 n) (@lem85071 n)). Qed.
Lemma lem85333 : term143 = (NUMERAL 0).
Proof. exact (@lem85332 (NUMERAL 0)). Qed.
Lemma lem85334 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem85335 : term142 = term144.
Proof. exact (MK_COMB (@lem85334) (@lem85333)). Qed.
Lemma lem85336 : term89 = term144.
Proof. exact (TRANS (@lem85330) (@lem85335)). Qed.
Lemma lem85337 (m : nat) : ((term116 m) = term89) = ((NUMERAL 0) = term144).
Proof. exact (MK_COMB (@lem85327 m) (@lem85336)). Qed.
Lemma lem85339 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem85031 n (@lem85030 n)). Qed.
Lemma lem85340 : ((NUMERAL 0) = term144) = False.
Proof. exact (@lem85339 (NUMERAL 0)). Qed.
Lemma lem85341 (m : nat) : ((term116 m) = term89) = False.
Proof. exact (TRANS (@lem85337 m) (@lem85340)). Qed.
Lemma lem85342 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem85343 (m : nat) : (term153 m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem85342) (@lem85341 m)). Qed.
Lemma lem85349 (n : nat) : (term20 n) = (term21 n).
Proof. exact (EQ_MP (@lem85045 n) (@lem85044 n)). Qed.
Lemma lem85350 : term89 = term142.
Proof. exact (@lem85349 0). Qed.
Lemma lem85352 (n : nat) : (term35 n) = n.
Proof. exact (EQ_MP (@lem85072 n) (@lem85071 n)). Qed.
Lemma lem85353 : term143 = (NUMERAL 0).
Proof. exact (@lem85352 (NUMERAL 0)). Qed.
Lemma lem85354 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem85355 : term142 = term144.
Proof. exact (MK_COMB (@lem85354) (@lem85353)). Qed.
Lemma lem85356 : term89 = term144.
Proof. exact (TRANS (@lem85350) (@lem85355)). Qed.
Lemma lem85357 (m : nat) : (term149 m) = (term149 m).
Proof. exact (eq_refl (term149 m)). Qed.
Lemma lem85358 (m : nat) : ((S m) = term89) = ((S m) = term144).
Proof. exact (MK_COMB (@lem85357 m) (@lem85356)). Qed.
Lemma lem85361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem85362 (m : nat) : (term154 m) = (term155 m).
Proof. exact (MK_COMB (@lem85361) (@lem85358 m)). Qed.
Lemma lem85366 (n : nat) : (term20 n) = (term21 n).
Proof. exact (EQ_MP (@lem85045 n) (@lem85044 n)). Qed.
Lemma lem85367 : term89 = term142.
Proof. exact (@lem85366 0). Qed.
Lemma lem85369 (n : nat) : (term35 n) = n.
Proof. exact (EQ_MP (@lem85072 n) (@lem85071 n)). Qed.
Lemma lem85370 : term143 = (NUMERAL 0).
Proof. exact (@lem85369 (NUMERAL 0)). Qed.
Lemma lem85371 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem85372 : term142 = term144.
Proof. exact (MK_COMB (@lem85371) (@lem85370)). Qed.
Lemma lem85373 : term89 = term144.
Proof. exact (TRANS (@lem85367) (@lem85372)). Qed.
Lemma lem85374 : term141 = term141.
Proof. exact (eq_refl term141). Qed.
Lemma lem85375 : ((NUMERAL 0) = term89) = ((NUMERAL 0) = term144).
Proof. exact (MK_COMB (@lem85374) (@lem85373)). Qed.
Lemma lem85377 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem85031 n (@lem85030 n)). Qed.
Lemma lem85378 : ((NUMERAL 0) = term144) = False.
Proof. exact (@lem85377 (NUMERAL 0)). Qed.
Lemma lem85379 : ((NUMERAL 0) = term89) = False.
Proof. exact (TRANS (@lem85375) (@lem85378)). Qed.
Lemma lem85380 (m : nat) : (term117 m) = (term156 m).
Proof. exact (MK_COMB (@lem85362 m) (@lem85379)). Qed.
Lemma lem85382 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem85383 (m : nat) : (term156 m) = False.
Proof. exact (@lem85382 ((S m) = term144)). Qed.
Lemma lem85384 (m : nat) : (term117 m) = False.
Proof. exact (TRANS (@lem85380 m) (@lem85383 m)). Qed.
Lemma lem85385 (m : nat) : (((term116 m) = term89) = (term117 m)) = (False = False).
Proof. exact (MK_COMB (@lem85343 m) (@lem85384 m)). Qed.
Lemma lem85387 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem85388 : (False = False) = (~ False).
Proof. exact (@lem85387 False). Qed.
Lemma lem85390 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem85391 : (False = False) = True.
Proof. exact (TRANS (@lem85388) (@lem85390)). Qed.
Lemma lem85392 (m : nat) : (((term116 m) = term89) = (term117 m)) = True.
Proof. exact (TRANS (@lem85385 m) (@lem85391)). Qed.
Lemma lem85393 (m : nat) : True = (((term116 m) = term89) = (term117 m)).
Proof. exact (SYM (@lem85392 m)). Qed.
Lemma lem85394 (m : nat) : ((term116 m) = term89) = (term117 m).
Proof. exact (EQ_MP (@lem85393 m) (@lem0)). Qed.
Lemma lem85400 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (EQ_MP (@lem85090 m n) (@lem85089 m n)). Qed.
Lemma lem85401 (m : nat) (n : nat) : (term125 m n) = (term157 m n).
Proof. exact (@lem85400 m (S n)). Qed.
Lemma lem85403 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (EQ_MP (@lem85057 m n) (@lem85056 m n)). Qed.
Lemma lem85404 (m : nat) (n : nat) : (term157 m n) = (term158 m n).
Proof. exact (@lem85403 (term44 m n) n). Qed.
Lemma lem85405 (m : nat) (n : nat) : (term125 m n) = (term158 m n).
Proof. exact (TRANS (@lem85401 m n) (@lem85404 m n)). Qed.
Lemma lem85407 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (EQ_MP (@lem85083 m n) (@lem85082 m n)). Qed.
Lemma lem85408 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem85409 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (MK_COMB (@lem85408) (@lem85407 m n)). Qed.
Lemma lem85410 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem85411 (m : nat) (n : nat) : (term161 m n) = (term162 m n).
Proof. exact (MK_COMB (@lem85409 m n) (@lem85410 n)). Qed.
Lemma lem85412 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem85413 (m : nat) (n : nat) : (term158 m n) = (term163 m n).
Proof. exact (MK_COMB (@lem85412) (@lem85411 m n)). Qed.
Lemma lem85414 (m : nat) (n : nat) : (term125 m n) = (term163 m n).
Proof. exact (TRANS (@lem85405 m n) (@lem85413 m n)). Qed.
Lemma lem85415 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem85416 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (MK_COMB (@lem85415) (@lem85414 m n)). Qed.
Lemma lem85418 (n : nat) : (term20 n) = (term21 n).
Proof. exact (EQ_MP (@lem85045 n) (@lem85044 n)). Qed.
Lemma lem85419 : term89 = term142.
Proof. exact (@lem85418 0). Qed.
Lemma lem85421 (n : nat) : (term35 n) = n.
Proof. exact (EQ_MP (@lem85072 n) (@lem85071 n)). Qed.
Lemma lem85422 : term143 = (NUMERAL 0).
Proof. exact (@lem85421 (NUMERAL 0)). Qed.
Lemma lem85423 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem85424 : term142 = term144.
Proof. exact (MK_COMB (@lem85423) (@lem85422)). Qed.
Lemma lem85425 : term89 = term144.
Proof. exact (TRANS (@lem85419) (@lem85424)). Qed.
Lemma lem85426 (m : nat) (n : nat) : ((term125 m n) = term89) = ((term163 m n) = term144).
Proof. exact (MK_COMB (@lem85416 m n) (@lem85425)). Qed.
Lemma lem85429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem85430 (m : nat) (n : nat) : (term166 m n) = (term167 m n).
Proof. exact (MK_COMB (@lem85429) (@lem85426 m n)). Qed.
Lemma lem85436 (n : nat) : (term20 n) = (term21 n).
Proof. exact (EQ_MP (@lem85045 n) (@lem85044 n)). Qed.
Lemma lem85437 : term89 = term142.
Proof. exact (@lem85436 0). Qed.
Lemma lem85439 (n : nat) : (term35 n) = n.
Proof. exact (EQ_MP (@lem85072 n) (@lem85071 n)). Qed.
Lemma lem85440 : term143 = (NUMERAL 0).
Proof. exact (@lem85439 (NUMERAL 0)). Qed.
Lemma lem85441 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem85442 : term142 = term144.
Proof. exact (MK_COMB (@lem85441) (@lem85440)). Qed.
Lemma lem85443 : term89 = term144.
Proof. exact (TRANS (@lem85437) (@lem85442)). Qed.
Lemma lem85444 (m : nat) : (term149 m) = (term149 m).
Proof. exact (eq_refl (term149 m)). Qed.
Lemma lem85445 (m : nat) : ((S m) = term89) = ((S m) = term144).
Proof. exact (MK_COMB (@lem85444 m) (@lem85443)). Qed.
Lemma lem85448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem85449 (m : nat) : (term154 m) = (term155 m).
Proof. exact (MK_COMB (@lem85448) (@lem85445 m)). Qed.
Lemma lem85453 (n : nat) : (term20 n) = (term21 n).
Proof. exact (EQ_MP (@lem85045 n) (@lem85044 n)). Qed.
Lemma lem85454 : term89 = term142.
Proof. exact (@lem85453 0). Qed.
Lemma lem85456 (n : nat) : (term35 n) = n.
Proof. exact (EQ_MP (@lem85072 n) (@lem85071 n)). Qed.
Lemma lem85457 : term143 = (NUMERAL 0).
Proof. exact (@lem85456 (NUMERAL 0)). Qed.
Lemma lem85458 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem85459 : term142 = term144.
Proof. exact (MK_COMB (@lem85458) (@lem85457)). Qed.
Lemma lem85460 : term89 = term144.
Proof. exact (TRANS (@lem85454) (@lem85459)). Qed.
Lemma lem85461 (n : nat) : (term149 n) = (term149 n).
Proof. exact (eq_refl (term149 n)). Qed.
Lemma lem85462 (n : nat) : ((S n) = term89) = ((S n) = term144).
Proof. exact (MK_COMB (@lem85461 n) (@lem85460)). Qed.
Lemma lem85465 (m : nat) (n : nat) : (term126 m n) = (term168 m n).
Proof. exact (MK_COMB (@lem85449 m) (@lem85462 n)). Qed.
Lemma lem85468 (m : nat) (n : nat) : (((term125 m n) = term89) = (term126 m n)) = (((term163 m n) = term144) = (term168 m n)).
Proof. exact (MK_COMB (@lem85430 m n) (@lem85465 m n)). Qed.
Lemma lem85471 (m : nat) (n : nat) : (((term163 m n) = term144) = (term168 m n)) = (((term125 m n) = term89) = (term126 m n)).
Proof. exact (SYM (@lem85468 m n)). Qed.
Lemma lem85475 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem85013 m n) (@lem85012 m n)). Qed.
Lemma lem85476 (m : nat) (n : nat) : ((term163 m n) = term144) = ((term162 m n) = (NUMERAL 0)).
Proof. exact (@lem85475 (term162 m n) (NUMERAL 0)). Qed.
Lemma lem85478 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term7 m n).
Proof. exact (EQ_MP (@lem85007 m n) (@lem85006 m n)). Qed.
Lemma lem85479 (m : nat) (n : nat) : ((term162 m n) = (NUMERAL 0)) = (term169 m n).
Proof. exact (@lem85478 (term45 m n) n). Qed.
Lemma lem85482 (m : nat) (n : nat) : ((term163 m n) = term144) = (term169 m n).
Proof. exact (TRANS (@lem85476 m n) (@lem85479 m n)). Qed.
Lemma lem85484 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term7 m n).
Proof. exact (EQ_MP (@lem85007 m n) (@lem85006 m n)). Qed.
Lemma lem85485 (m : nat) (n : nat) : ((term45 m n) = (NUMERAL 0)) = (term170 m n).
Proof. exact (@lem85484 m (Nat.mul m n)). Qed.
Lemma lem85491 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = (term3 m n).
Proof. exact (EQ_MP (@lem85001 m n) (@lem85000 m n)). Qed.
Lemma lem85498 (m : nat) : (term171 m) = (term171 m).
Proof. exact (eq_refl (term171 m)). Qed.
Lemma lem85499 (m : nat) (n : nat) : (term170 m n) = (term172 m n).
Proof. exact (MK_COMB (@lem85498 m) (@lem85491 m n)). Qed.
Lemma lem85502 (m : nat) (n : nat) : ((term45 m n) = (NUMERAL 0)) = (term172 m n).
Proof. exact (TRANS (@lem85485 m n) (@lem85499 m n)). Qed.
Lemma lem85503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem85504 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (MK_COMB (@lem85503) (@lem85502 m n)). Qed.
Lemma lem85507 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem85508 (m : nat) (n : nat) : (term169 m n) = (term175 m n).
Proof. exact (MK_COMB (@lem85504 m n) (@lem85507 n)). Qed.
Lemma lem85511 (m : nat) (n : nat) : ((term163 m n) = term144) = (term175 m n).
Proof. exact (TRANS (@lem85482 m n) (@lem85508 m n)). Qed.
Lemma lem85512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem85513 (m : nat) (n : nat) : (term167 m n) = (term176 m n).
Proof. exact (MK_COMB (@lem85512) (@lem85511 m n)). Qed.
Lemma lem85517 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem85013 m n) (@lem85012 m n)). Qed.
Lemma lem85518 (m : nat) : ((S m) = term144) = (m = (NUMERAL 0)).
Proof. exact (@lem85517 m (NUMERAL 0)). Qed.
Lemma lem85521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem85522 (m : nat) : (term155 m) = (term171 m).
Proof. exact (MK_COMB (@lem85521) (@lem85518 m)). Qed.
Lemma lem85524 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem85013 m n) (@lem85012 m n)). Qed.
Lemma lem85525 (n : nat) : ((S n) = term144) = (n = (NUMERAL 0)).
Proof. exact (@lem85524 n (NUMERAL 0)). Qed.
Lemma lem85528 (m : nat) (n : nat) : (term168 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem85522 m) (@lem85525 n)). Qed.
Lemma lem85531 (m : nat) (n : nat) : (((term163 m n) = term144) = (term168 m n)) = ((term175 m n) = (term7 m n)).
Proof. exact (MK_COMB (@lem85513 m n) (@lem85528 m n)). Qed.
Lemma lem85534 (m : nat) (n : nat) : ((term175 m n) = (term7 m n)) = (((term163 m n) = term144) = (term168 m n)).
Proof. exact (SYM (@lem85531 m n)). Qed.
Lemma lem85559 (m : nat) : term177 m.
Proof. exact (@lem9851 (m = (NUMERAL 0))). Qed.
Lemma lem85560 (m : nat) : (term177 m) = (term178 m).
Proof. exact (eq_refl (term177 m)). Qed.
Lemma lem85561 (m : nat) : term178 m.
Proof. exact (EQ_MP (@lem85560 m) (@lem85559 m)). Qed.
Lemma lem85562 (m : nat) (h1 : (m = (NUMERAL 0)) = True) : (m = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem85563 (m : nat) (h1 : (m = (NUMERAL 0)) = False) : (m = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem85588 (n : nat) : (term179 n) = (term179 n).
Proof. exact (eq_refl (term179 n)). Qed.
Lemma lem85589 (n : nat) (m : nat) (h1 : (m = (NUMERAL 0)) = True) : (term180 n m) = (term181 n).
Proof. exact (MK_COMB (@lem85588 n) (@lem85562 m h1)). Qed.
Lemma lem85590 (n : nat) : (term181 n) = ((term182 n) = (term183 n)).
Proof. exact (eq_refl (term181 n)). Qed.
Lemma lem85591 (n : nat) (m : nat) : (term184 n m) = (term184 n m).
Proof. exact (eq_refl (term184 n m)). Qed.
Lemma lem85592 (m : nat) (n : nat) : ((term180 n m) = (term181 n)) = ((term180 n m) = ((term182 n) = (term183 n))).
Proof. exact (MK_COMB (@lem85591 n m) (@lem85590 n)). Qed.
Lemma lem85593 (m : nat) (n : nat) : (term180 n m) = ((term175 m n) = (term7 m n)).
Proof. exact (eq_refl (term180 n m)). Qed.
Lemma lem85594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem85595 (m : nat) (n : nat) : (term184 n m) = (term185 m n).
Proof. exact (MK_COMB (@lem85594) (@lem85593 m n)). Qed.
Lemma lem85596 (n : nat) : ((term182 n) = (term183 n)) = ((term182 n) = (term183 n)).
Proof. exact (eq_refl ((term182 n) = (term183 n))). Qed.
Lemma lem85597 (m : nat) (n : nat) : ((term180 n m) = ((term182 n) = (term183 n))) = (((term175 m n) = (term7 m n)) = ((term182 n) = (term183 n))).
Proof. exact (MK_COMB (@lem85595 m n) (@lem85596 n)). Qed.
Lemma lem85598 (m : nat) (n : nat) : ((term180 n m) = (term181 n)) = (((term175 m n) = (term7 m n)) = ((term182 n) = (term183 n))).
Proof. exact (TRANS (@lem85592 m n) (@lem85597 m n)). Qed.
Lemma lem85599 (n : nat) (m : nat) (h1 : (m = (NUMERAL 0)) = True) : ((term175 m n) = (term7 m n)) = ((term182 n) = (term183 n)).
Proof. exact (EQ_MP (@lem85598 m n) (@lem85589 n m h1)). Qed.
Lemma lem85600 (n : nat) (m : nat) (h1 : (m = (NUMERAL 0)) = True) : ((term182 n) = (term183 n)) = ((term175 m n) = (term7 m n)).
Proof. exact (SYM (@lem85599 n m h1)). Qed.
Lemma lem85601 (n : nat) : (term179 n) = (term179 n).
Proof. exact (eq_refl (term179 n)). Qed.
Lemma lem85602 (n : nat) (m : nat) (h1 : (m = (NUMERAL 0)) = False) : (term180 n m) = (term186 n).
Proof. exact (MK_COMB (@lem85601 n) (@lem85563 m h1)). Qed.
Lemma lem85603 (n : nat) : (term186 n) = ((term187 n) = (term188 n)).
Proof. exact (eq_refl (term186 n)). Qed.
Lemma lem85604 (n : nat) (m : nat) : (term184 n m) = (term184 n m).
Proof. exact (eq_refl (term184 n m)). Qed.
Lemma lem85605 (m : nat) (n : nat) : ((term180 n m) = (term186 n)) = ((term180 n m) = ((term187 n) = (term188 n))).
Proof. exact (MK_COMB (@lem85604 n m) (@lem85603 n)). Qed.
Lemma lem85606 (m : nat) (n : nat) : (term180 n m) = ((term175 m n) = (term7 m n)).
Proof. exact (eq_refl (term180 n m)). Qed.
Lemma lem85607 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem85608 (m : nat) (n : nat) : (term184 n m) = (term185 m n).
Proof. exact (MK_COMB (@lem85607) (@lem85606 m n)). Qed.
Lemma lem85609 (n : nat) : ((term187 n) = (term188 n)) = ((term187 n) = (term188 n)).
Proof. exact (eq_refl ((term187 n) = (term188 n))). Qed.
Lemma lem85610 (m : nat) (n : nat) : ((term180 n m) = ((term187 n) = (term188 n))) = (((term175 m n) = (term7 m n)) = ((term187 n) = (term188 n))).
Proof. exact (MK_COMB (@lem85608 m n) (@lem85609 n)). Qed.
Lemma lem85611 (m : nat) (n : nat) : ((term180 n m) = (term186 n)) = (((term175 m n) = (term7 m n)) = ((term187 n) = (term188 n))).
Proof. exact (TRANS (@lem85605 m n) (@lem85610 m n)). Qed.
Lemma lem85612 (n : nat) (m : nat) (h1 : (m = (NUMERAL 0)) = False) : ((term175 m n) = (term7 m n)) = ((term187 n) = (term188 n)).
Proof. exact (EQ_MP (@lem85611 m n) (@lem85602 n m h1)). Qed.
Lemma lem85613 (n : nat) (m : nat) (h1 : (m = (NUMERAL 0)) = False) : ((term187 n) = (term188 n)) = ((term175 m n) = (term7 m n)).
Proof. exact (SYM (@lem85612 n m h1)). Qed.
Lemma lem85619 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem85620 (n : nat) : (term189 n) = (term190 n).
Proof. exact (@lem85619 (term190 n)). Qed.
Lemma lem85622 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem85623 (n : nat) : (term190 n) = True.
Proof. exact (@lem85622 (n = (NUMERAL 0))). Qed.
Lemma lem85624 (n : nat) : (term189 n) = True.
Proof. exact (TRANS (@lem85620 n) (@lem85623 n)). Qed.
Lemma lem85625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem85626 (n : nat) : (term191 n) = (and True).
Proof. exact (MK_COMB (@lem85625) (@lem85624 n)). Qed.
Lemma lem85629 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem85630 (n : nat) : (term182 n) = (term183 n).
Proof. exact (MK_COMB (@lem85626 n) (@lem85629 n)). Qed.
Lemma lem85632 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem85633 (n : nat) : (term183 n) = (n = (NUMERAL 0)).
Proof. exact (@lem85632 (n = (NUMERAL 0))). Qed.
Lemma lem85636 (n : nat) : (term182 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem85630 n) (@lem85633 n)). Qed.
Lemma lem85637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem85638 (n : nat) : (term192 n) = (term193 n).
Proof. exact (MK_COMB (@lem85637) (@lem85636 n)). Qed.
Lemma lem85640 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem85641 (n : nat) : (term183 n) = (n = (NUMERAL 0)).
Proof. exact (@lem85640 (n = (NUMERAL 0))). Qed.
Lemma lem85644 (n : nat) : ((term182 n) = (term183 n)) = ((n = (NUMERAL 0)) = (n = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem85638 n) (@lem85641 n)). Qed.
Lemma lem85646 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem85647 (x : Prop) : (x = x) = True.
Proof. exact (@lem85646 Prop x). Qed.
Lemma lem85648 (n : nat) : ((n = (NUMERAL 0)) = (n = (NUMERAL 0))) = True.
Proof. exact (@lem85647 (n = (NUMERAL 0))). Qed.
Lemma lem85649 (n : nat) : ((term182 n) = (term183 n)) = True.
Proof. exact (TRANS (@lem85644 n) (@lem85648 n)). Qed.
Lemma lem85650 (n : nat) : True = ((term182 n) = (term183 n)).
Proof. exact (SYM (@lem85649 n)). Qed.
Lemma lem85651 (n : nat) : (term182 n) = (term183 n).
Proof. exact (EQ_MP (@lem85650 n) (@lem0)). Qed.
Lemma lem85657 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem85658 (n : nat) : (term194 n) = False.
Proof. exact (@lem85657 (term195 n)). Qed.
Lemma lem85659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem85660 (n : nat) : (term196 n) = (and False).
Proof. exact (MK_COMB (@lem85659) (@lem85658 n)). Qed.
Lemma lem85663 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem85664 (n : nat) : (term187 n) = (term188 n).
Proof. exact (MK_COMB (@lem85660 n) (@lem85663 n)). Qed.
Lemma lem85666 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem85667 (n : nat) : (term188 n) = False.
Proof. exact (@lem85666 (n = (NUMERAL 0))). Qed.
Lemma lem85668 (n : nat) : (term187 n) = False.
Proof. exact (TRANS (@lem85664 n) (@lem85667 n)). Qed.
Lemma lem85669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem85670 (n : nat) : (term197 n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem85669) (@lem85668 n)). Qed.
Lemma lem85672 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem85673 (n : nat) : (term188 n) = False.
Proof. exact (@lem85672 (n = (NUMERAL 0))). Qed.
Lemma lem85674 (n : nat) : ((term187 n) = (term188 n)) = (False = False).
Proof. exact (MK_COMB (@lem85670 n) (@lem85673 n)). Qed.
Lemma lem85676 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem85677 : (False = False) = (~ False).
Proof. exact (@lem85676 False). Qed.
Lemma lem85679 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem85680 : (False = False) = True.
Proof. exact (TRANS (@lem85677) (@lem85679)). Qed.
Lemma lem85681 (n : nat) : ((term187 n) = (term188 n)) = True.
Proof. exact (TRANS (@lem85674 n) (@lem85680)). Qed.
Lemma lem85682 (n : nat) : True = ((term187 n) = (term188 n)).
Proof. exact (SYM (@lem85681 n)). Qed.
Lemma lem85683 (n : nat) : (term187 n) = (term188 n).
Proof. exact (EQ_MP (@lem85682 n) (@lem0)). Qed.
Lemma lem85684 (n : nat) (m : nat) (h1 : (m = (NUMERAL 0)) = False) : (term175 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem85613 n m h1) (@lem85683 n)). Qed.
Lemma lem85685 (n : nat) (m : nat) (h1 : (m = (NUMERAL 0)) = True) : (term175 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem85600 n m h1) (@lem85651 n)). Qed.
Lemma lem85688 (m : nat) (n : nat) : (term175 m n) = (term7 m n).
Proof. exact (or_elim (@lem85561 m) (fun h0 : (m = (NUMERAL 0)) = True => @lem85685 n m h0) (fun h0 : (m = (NUMERAL 0)) = False => @lem85684 n m h0)). Qed.
Lemma lem85689 (m : nat) (n : nat) : ((term163 m n) = term144) = (term168 m n).
Proof. exact (EQ_MP (@lem85534 m n) (@lem85688 m n)). Qed.
Lemma lem85690 (m : nat) (n : nat) : ((term125 m n) = term89) = (term126 m n).
Proof. exact (EQ_MP (@lem85471 m n) (@lem85689 m n)). Qed.
Lemma lem85691 (m : nat) (n : nat) : term128 m n.
Proof. exact (fun h0 : ((term50 m n) = term89) = (term121 m n) => @lem85690 m n). Qed.
Lemma lem85696 (m : nat) : term132 m.
Proof. exact (fun n : nat => @lem85691 m n). Qed.
Lemma lem85697 (m : nat) : term134 m.
Proof. exact (conj (@lem85394 m) (@lem85696 m)). Qed.
Lemma lem85698 (m : nat) : term70 m.
Proof. exact (@lem85178 m (@lem85697 m)). Qed.
Lemma lem85699 (n : nat) : term101 n.
Proof. exact (fun h0 : ((term57 n) = term89) = (term94 n) => @lem85311 n). Qed.
Lemma lem85704 : term105.
Proof. exact (fun n : nat => @lem85699 n). Qed.
Lemma lem85705 : term107.
Proof. exact (conj (@lem85235) (@lem85704)). Qed.
Lemma lem85706 : term62.
Proof. exact (@lem85154 (@lem85705)). Qed.
Lemma lem85707 (m : nat) : term72 m.
Proof. exact (fun h0 : term66 m => @lem85698 m). Qed.
Lemma lem85712 : term76.
Proof. exact (fun m : nat => @lem85707 m). Qed.
Lemma lem85713 : term78.
Proof. exact (conj (@lem85706) (@lem85712)). Qed.
Lemma lem85714 : term83.
Proof. exact (@lem85130 (@lem85713)). Qed.
