Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_ADD_SPLIT_term_abbrevs.
Require Import DISJOINT_NUMSEG_spec.
Require Import FINITE_NUMSEG_spec.
Require Import INT_POS_spec.
Require Import NUMSEG_ADD_SPLIT_spec.
Require Import SUM_UNION_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm2318496_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7222101 (m : nat) (n : nat) : (Peano.lt m n) = (term0 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem7222102 (x : nat) : (term1 x) = (term2 x).
Proof. exact (@lem7222101 x (term3 x)). Qed.
Lemma lem7222104 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7222105 (x : nat) : (term6 x) = (term7 x).
Proof. exact (@lem7222104 x term8). Qed.
Lemma lem7222106 (x : nat) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem7222107 (x : nat) : (term2 x) = (term10 x).
Proof. exact (MK_COMB (@lem7222106 x) (@lem7222105 x)). Qed.
Lemma lem7222109 (x : nat) : (term1 x) = (term10 x).
Proof. exact (TRANS (@lem7222102 x) (@lem7222107 x)). Qed.
Lemma lem7222110 (x : nat) : term11 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem7222111 (x : nat) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem7222112 (x : nat) : term12 x.
Proof. exact (EQ_MP (@lem7222111 x) (@lem7222110 x)). Qed.
Lemma lem7222113 (_96841 : int) : (term13 _96841) = (term14 _96841).
Proof. exact (@lem2318604 (term14 _96841)). Qed.
Lemma lem7222136 (_96841 : int) : (term15 _96841) = (term16 _96841).
Proof. exact (@lem17362 (term17 _96841) (term18 _96841)). Qed.
Lemma lem7222139 (x : int) (y : int) : (int_le x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7222140 (_96841 : int) : (term17 _96841) = (term20 _96841).
Proof. exact (@lem7222139 term21 _96841). Qed.
Lemma lem7222142 (n : nat) : (term22 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7222143 : term23 = term24.
Proof. exact (@lem7222142 (NUMERAL 0)). Qed.
Lemma lem7222144 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7222145 : term25 = term26.
Proof. exact (MK_COMB (@lem7222144) (@lem7222143)). Qed.
Lemma lem7222146 (_96841 : int) : (real_of_int _96841) = (real_of_int _96841).
Proof. exact (eq_refl (real_of_int _96841)). Qed.
Lemma lem7222147 (_96841 : int) : (term20 _96841) = (term27 _96841).
Proof. exact (MK_COMB (@lem7222145) (@lem7222146 _96841)). Qed.
Lemma lem7222149 (_96841 : int) : (term17 _96841) = (term27 _96841).
Proof. exact (TRANS (@lem7222140 _96841) (@lem7222147 _96841)). Qed.
Lemma lem7222151 (y : int) (x : int) : (term28 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem7222152 (_96841 : int) : (term29 _96841) = (term30 _96841).
Proof. exact (@lem7222151 (term31 _96841) _96841). Qed.
Lemma lem7222154 (x : int) (y : int) : (int_le x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7222155 (_96841 : int) : (term30 _96841) = (term32 _96841).
Proof. exact (@lem7222154 (term31 _96841) _96841). Qed.
Lemma lem7222157 (x : int) (y : int) : (term33 x y) = (term34 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7222158 (_96841 : int) : (term35 _96841) = (term36 _96841).
Proof. exact (@lem7222157 _96841 term37). Qed.
Lemma lem7222160 (n : nat) : (term22 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7222161 : term38 = term39.
Proof. exact (@lem7222160 term8). Qed.
Lemma lem7222162 (_96841 : int) : (term40 _96841) = (term40 _96841).
Proof. exact (eq_refl (term40 _96841)). Qed.
Lemma lem7222163 (_96841 : int) : (term36 _96841) = (term41 _96841).
Proof. exact (MK_COMB (@lem7222162 _96841) (@lem7222161)). Qed.
Lemma lem7222164 (_96841 : int) : (term35 _96841) = (term41 _96841).
Proof. exact (TRANS (@lem7222158 _96841) (@lem7222163 _96841)). Qed.
Lemma lem7222165 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7222166 (_96841 : int) : (term42 _96841) = (term43 _96841).
Proof. exact (MK_COMB (@lem7222165) (@lem7222164 _96841)). Qed.
Lemma lem7222167 (_96841 : int) : (real_of_int _96841) = (real_of_int _96841).
Proof. exact (eq_refl (real_of_int _96841)). Qed.
Lemma lem7222168 (_96841 : int) : (term32 _96841) = (term44 _96841).
Proof. exact (MK_COMB (@lem7222166 _96841) (@lem7222167 _96841)). Qed.
Lemma lem7222169 (_96841 : int) : (term30 _96841) = (term44 _96841).
Proof. exact (TRANS (@lem7222155 _96841) (@lem7222168 _96841)). Qed.
Lemma lem7222170 (_96841 : int) : (term29 _96841) = (term44 _96841).
Proof. exact (TRANS (@lem7222152 _96841) (@lem7222169 _96841)). Qed.
Lemma lem7222171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7222172 (_96841 : int) : (term45 _96841) = (term46 _96841).
Proof. exact (MK_COMB (@lem7222171) (@lem7222149 _96841)). Qed.
Lemma lem7222173 (_96841 : int) : (term16 _96841) = (term47 _96841).
Proof. exact (MK_COMB (@lem7222172 _96841) (@lem7222170 _96841)). Qed.
Lemma lem7222174 (_96841 : int) : (term15 _96841) = (term47 _96841).
Proof. exact (TRANS (@lem7222136 _96841) (@lem7222173 _96841)). Qed.
Lemma lem7222178 (t : Prop) : (term48 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7222194 (_96841 : int) : (term49 _96841) = (term47 _96841).
Proof. exact (@lem7222178 (term47 _96841)). Qed.
Lemma lem7222195 (_96841 : int) : (term27 _96841) = (term50 _96841).
Proof. exact (@lem1988287 (real_of_int _96841) term24). Qed.
Lemma lem7222201 (_96841 : int) : (term51 _96841) = (term52 _96841).
Proof. exact (@lem1982792 (real_of_int _96841) term24). Qed.
Lemma lem7222203 (x : nat) : (real_of_num x) = (term53 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7222204 : term24 = term54.
Proof. exact (@lem7222203 (NUMERAL 0)). Qed.
Lemma lem7222206 (x : nat) : (term55 x) = (term56 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7222207 : term57 = term58.
Proof. exact (@lem7222206 term8). Qed.
Lemma lem7222208 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7222209 : term59 = term60.
Proof. exact (MK_COMB (@lem7222208) (@lem7222207)). Qed.
Lemma lem7222210 : term61 = term62.
Proof. exact (MK_COMB (@lem7222209) (@lem7222204)). Qed.
Lemma lem7222211 : term62 = term63.
Proof. exact (@lem1981613 term57 term24 term39 term39). Qed.
Lemma lem7222213 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7222214 : term66 = term67.
Proof. exact (@lem7222213 term8 term8). Qed.
Lemma lem7222215 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7222216 : term69 = term8.
Proof. exact (EQ_MP (@lem7222215) (@lem940073)). Qed.
Lemma lem7222217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7222218 : term67 = term39.
Proof. exact (MK_COMB (@lem7222217) (@lem7222216)). Qed.
Lemma lem7222219 : term66 = term39.
Proof. exact (TRANS (@lem7222214) (@lem7222218)). Qed.
Lemma lem7222221 (x : nat) : (term70 x) = term24.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7222222 : term61 = term24.
Proof. exact (@lem7222221 term8). Qed.
Lemma lem7222223 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7222224 : term71 = term72.
Proof. exact (MK_COMB (@lem7222223) (@lem7222222)). Qed.
Lemma lem7222225 : term63 = term54.
Proof. exact (MK_COMB (@lem7222224) (@lem7222219)). Qed.
Lemma lem7222226 : term62 = term54.
Proof. exact (TRANS (@lem7222211) (@lem7222225)). Qed.
Lemma lem7222227 : term61 = term54.
Proof. exact (TRANS (@lem7222210) (@lem7222226)). Qed.
Lemma lem7222229 (x : real) : (term73 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7222230 : term54 = term24.
Proof. exact (@lem7222229 term24). Qed.
Lemma lem7222231 : term61 = term24.
Proof. exact (TRANS (@lem7222227) (@lem7222230)). Qed.
Lemma lem7222232 (_96841 : int) : (term40 _96841) = (term40 _96841).
Proof. exact (eq_refl (term40 _96841)). Qed.
Lemma lem7222233 (_96841 : int) : (term52 _96841) = (term74 _96841).
Proof. exact (MK_COMB (@lem7222232 _96841) (@lem7222231)). Qed.
Lemma lem7222234 (_96841 : int) : (term74 _96841) = (real_of_int _96841).
Proof. exact (@lem1982723 (real_of_int _96841)). Qed.
Lemma lem7222235 (_96841 : int) : (term52 _96841) = (real_of_int _96841).
Proof. exact (TRANS (@lem7222233 _96841) (@lem7222234 _96841)). Qed.
Lemma lem7222237 (_96841 : int) : (term51 _96841) = (real_of_int _96841).
Proof. exact (TRANS (@lem7222201 _96841) (@lem7222235 _96841)). Qed.
Lemma lem7222238 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7222239 (_96841 : int) : (term75 _96841) = (term76 _96841).
Proof. exact (MK_COMB (@lem7222238) (@lem7222237 _96841)). Qed.
Lemma lem7222240 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem7222241 (_96841 : int) : (term50 _96841) = (term77 _96841).
Proof. exact (MK_COMB (@lem7222239 _96841) (@lem7222240)). Qed.
Lemma lem7222242 (_96841 : int) : (term27 _96841) = (term77 _96841).
Proof. exact (TRANS (@lem7222195 _96841) (@lem7222241 _96841)). Qed.
Lemma lem7222243 (_96841 : int) : (term44 _96841) = (term78 _96841).
Proof. exact (@lem1988287 (real_of_int _96841) (term41 _96841)). Qed.
Lemma lem7222255 (_96841 : int) : (term79 _96841) = (term80 _96841).
Proof. exact (@lem1982792 (real_of_int _96841) (term41 _96841)). Qed.
Lemma lem7222256 (_96841 : int) : (term81 _96841) = (term82 _96841).
Proof. exact (@lem1982781 (real_of_int _96841) term57 term39). Qed.
Lemma lem7222258 (x : nat) : (real_of_num x) = (term53 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7222259 : term39 = term83.
Proof. exact (@lem7222258 term8). Qed.
Lemma lem7222261 (x : nat) : (term55 x) = (term56 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7222262 : term57 = term58.
Proof. exact (@lem7222261 term8). Qed.
Lemma lem7222263 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7222264 : term59 = term60.
Proof. exact (MK_COMB (@lem7222263) (@lem7222262)). Qed.
Lemma lem7222265 : term84 = term85.
Proof. exact (MK_COMB (@lem7222264) (@lem7222259)). Qed.
Lemma lem7222266 : term85 = term86.
Proof. exact (@lem1981613 term57 term39 term39 term39). Qed.
Lemma lem7222268 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7222269 : term66 = term67.
Proof. exact (@lem7222268 term8 term8). Qed.
Lemma lem7222270 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7222271 : term69 = term8.
Proof. exact (EQ_MP (@lem7222270) (@lem940073)). Qed.
Lemma lem7222272 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7222273 : term67 = term39.
Proof. exact (MK_COMB (@lem7222272) (@lem7222271)). Qed.
Lemma lem7222274 : term66 = term39.
Proof. exact (TRANS (@lem7222269) (@lem7222273)). Qed.
Lemma lem7222276 (m : nat) (n : nat) : (term87 m n) = (term88 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7222277 : term84 = term89.
Proof. exact (@lem7222276 term8 term8). Qed.
Lemma lem7222278 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7222279 : term69 = term8.
Proof. exact (EQ_MP (@lem7222278) (@lem940073)). Qed.
Lemma lem7222280 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7222281 : term67 = term39.
Proof. exact (MK_COMB (@lem7222280) (@lem7222279)). Qed.
Lemma lem7222282 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7222283 : term89 = term57.
Proof. exact (MK_COMB (@lem7222282) (@lem7222281)). Qed.
Lemma lem7222284 : term84 = term57.
Proof. exact (TRANS (@lem7222277) (@lem7222283)). Qed.
Lemma lem7222285 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7222286 : term90 = term91.
Proof. exact (MK_COMB (@lem7222285) (@lem7222284)). Qed.
Lemma lem7222287 : term86 = term58.
Proof. exact (MK_COMB (@lem7222286) (@lem7222274)). Qed.
Lemma lem7222288 : term85 = term58.
Proof. exact (TRANS (@lem7222266) (@lem7222287)). Qed.
Lemma lem7222289 : term84 = term58.
Proof. exact (TRANS (@lem7222265) (@lem7222288)). Qed.
Lemma lem7222291 (x : real) : (term73 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7222292 : term58 = term57.
Proof. exact (@lem7222291 term57). Qed.
Lemma lem7222293 : term84 = term57.
Proof. exact (TRANS (@lem7222289) (@lem7222292)). Qed.
Lemma lem7222296 (_96841 : int) : (term92 _96841) = (term92 _96841).
Proof. exact (eq_refl (term92 _96841)). Qed.
Lemma lem7222297 (_96841 : int) : (term82 _96841) = (term93 _96841).
Proof. exact (MK_COMB (@lem7222296 _96841) (@lem7222293)). Qed.
Lemma lem7222298 (_96841 : int) : (term81 _96841) = (term93 _96841).
Proof. exact (TRANS (@lem7222256 _96841) (@lem7222297 _96841)). Qed.
Lemma lem7222299 (_96841 : int) : (term40 _96841) = (term40 _96841).
Proof. exact (eq_refl (term40 _96841)). Qed.
Lemma lem7222300 (_96841 : int) : (term80 _96841) = (term94 _96841).
Proof. exact (MK_COMB (@lem7222299 _96841) (@lem7222298 _96841)). Qed.
Lemma lem7222301 (_96841 : int) : (term94 _96841) = (term95 _96841).
Proof. exact (@lem1982763 (real_of_int _96841) (term96 _96841) term57). Qed.
Lemma lem7222302 (_96841 : int) : (term97 _96841) = (term98 _96841).
Proof. exact (@lem1982715 term57 (real_of_int _96841)). Qed.
Lemma lem7222304 (x : nat) : (real_of_num x) = (term53 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7222305 : term39 = term83.
Proof. exact (@lem7222304 term8). Qed.
Lemma lem7222307 (x : nat) : (term55 x) = (term56 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7222308 : term57 = term58.
Proof. exact (@lem7222307 term8). Qed.
Lemma lem7222309 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7222310 : term99 = term100.
Proof. exact (MK_COMB (@lem7222309) (@lem7222308)). Qed.
Lemma lem7222311 : term101 = term102.
Proof. exact (MK_COMB (@lem7222310) (@lem7222305)). Qed.
Lemma lem7222312 : term103.
Proof. exact (@lem1981473 term57 term39 term39 term39 term24 term39). Qed.
Lemma lem7222314 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7222315 : term105 = term106.
Proof. exact (@lem7222314 (NUMERAL 0) term8). Qed.
Lemma lem7222316 : term107 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7222317 (h1 : term107 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7222318 : (term107 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term107 = (BIT1 0) => @lem7222317 h1) (fun h1 : term106 = True => @lem7222316)). Qed.
Lemma lem7222319 : term106 = True.
Proof. exact (EQ_MP (@lem7222318) (@lem7222316)). Qed.
Lemma lem7222320 : term105 = True.
Proof. exact (TRANS (@lem7222315) (@lem7222319)). Qed.
Lemma lem7222321 : True = term105.
Proof. exact (SYM (@lem7222320)). Qed.
Lemma lem7222322 : term105.
Proof. exact (EQ_MP (@lem7222321) (@lem0)). Qed.
Lemma lem7222323 : term108.
Proof. exact (@lem7222312 (@lem7222322)). Qed.
Lemma lem7222325 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7222326 : term105 = term106.
Proof. exact (@lem7222325 (NUMERAL 0) term8). Qed.
Lemma lem7222327 : term107 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7222328 (h1 : term107 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7222329 : (term107 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term107 = (BIT1 0) => @lem7222328 h1) (fun h1 : term106 = True => @lem7222327)). Qed.
Lemma lem7222330 : term106 = True.
Proof. exact (EQ_MP (@lem7222329) (@lem7222327)). Qed.
Lemma lem7222331 : term105 = True.
Proof. exact (TRANS (@lem7222326) (@lem7222330)). Qed.
Lemma lem7222332 : True = term105.
Proof. exact (SYM (@lem7222331)). Qed.
Lemma lem7222333 : term105.
Proof. exact (EQ_MP (@lem7222332) (@lem0)). Qed.
Lemma lem7222334 : term109.
Proof. exact (@lem7222323 (@lem7222333)). Qed.
Lemma lem7222336 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7222337 : term105 = term106.
Proof. exact (@lem7222336 (NUMERAL 0) term8). Qed.
Lemma lem7222338 : term107 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7222339 (h1 : term107 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7222340 : (term107 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term107 = (BIT1 0) => @lem7222339 h1) (fun h1 : term106 = True => @lem7222338)). Qed.
Lemma lem7222341 : term106 = True.
Proof. exact (EQ_MP (@lem7222340) (@lem7222338)). Qed.
Lemma lem7222342 : term105 = True.
Proof. exact (TRANS (@lem7222337) (@lem7222341)). Qed.
Lemma lem7222343 : True = term105.
Proof. exact (SYM (@lem7222342)). Qed.
Lemma lem7222344 : term105.
Proof. exact (EQ_MP (@lem7222343) (@lem0)). Qed.
Lemma lem7222345 : term110.
Proof. exact (@lem7222334 (@lem7222344)). Qed.
Lemma lem7222347 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7222348 : term66 = term67.
Proof. exact (@lem7222347 term8 term8). Qed.
Lemma lem7222349 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7222350 : term69 = term8.
Proof. exact (EQ_MP (@lem7222349) (@lem940073)). Qed.
Lemma lem7222351 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7222352 : term67 = term39.
Proof. exact (MK_COMB (@lem7222351) (@lem7222350)). Qed.
Lemma lem7222353 : term66 = term39.
Proof. exact (TRANS (@lem7222348) (@lem7222352)). Qed.
Lemma lem7222355 (m : nat) (n : nat) : (term87 m n) = (term88 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7222356 : term84 = term89.
Proof. exact (@lem7222355 term8 term8). Qed.
Lemma lem7222357 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7222358 : term69 = term8.
Proof. exact (EQ_MP (@lem7222357) (@lem940073)). Qed.
Lemma lem7222359 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7222360 : term67 = term39.
Proof. exact (MK_COMB (@lem7222359) (@lem7222358)). Qed.
Lemma lem7222361 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7222362 : term89 = term57.
Proof. exact (MK_COMB (@lem7222361) (@lem7222360)). Qed.
Lemma lem7222363 : term84 = term57.
Proof. exact (TRANS (@lem7222356) (@lem7222362)). Qed.
Lemma lem7222364 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7222365 : term111 = term99.
Proof. exact (MK_COMB (@lem7222364) (@lem7222363)). Qed.
Lemma lem7222366 : term112 = term101.
Proof. exact (MK_COMB (@lem7222365) (@lem7222353)). Qed.
Lemma lem7222368 (m : nat) : (term113 m) = term24.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7222369 : term101 = term24.
Proof. exact (@lem7222368 term8). Qed.
Lemma lem7222370 : term112 = term24.
Proof. exact (TRANS (@lem7222366) (@lem7222369)). Qed.
Lemma lem7222371 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7222372 : term114 = term115.
Proof. exact (MK_COMB (@lem7222371) (@lem7222370)). Qed.
Lemma lem7222373 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem7222374 : term116 = term117.
Proof. exact (MK_COMB (@lem7222372) (@lem7222373)). Qed.
Lemma lem7222376 (x : nat) : (term118 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7222377 : term117 = term24.
Proof. exact (@lem7222376 term8). Qed.
Lemma lem7222378 : term116 = term24.
Proof. exact (TRANS (@lem7222374) (@lem7222377)). Qed.
Lemma lem7222380 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7222381 : term66 = term67.
Proof. exact (@lem7222380 term8 term8). Qed.
Lemma lem7222382 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7222383 : term69 = term8.
Proof. exact (EQ_MP (@lem7222382) (@lem940073)). Qed.
Lemma lem7222384 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7222385 : term67 = term39.
Proof. exact (MK_COMB (@lem7222384) (@lem7222383)). Qed.
Lemma lem7222386 : term66 = term39.
Proof. exact (TRANS (@lem7222381) (@lem7222385)). Qed.
Lemma lem7222387 : term115 = term115.
Proof. exact (eq_refl term115). Qed.
Lemma lem7222388 : term119 = term117.
Proof. exact (MK_COMB (@lem7222387) (@lem7222386)). Qed.
Lemma lem7222390 (x : nat) : (term118 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7222391 : term117 = term24.
Proof. exact (@lem7222390 term8). Qed.
Lemma lem7222392 : term119 = term24.
Proof. exact (TRANS (@lem7222388) (@lem7222391)). Qed.
Lemma lem7222393 : term24 = term119.
Proof. exact (SYM (@lem7222392)). Qed.
Lemma lem7222394 : term116 = term119.
Proof. exact (TRANS (@lem7222378) (@lem7222393)). Qed.
Lemma lem7222395 : term102 = term54.
Proof. exact (@lem7222345 (@lem7222394)). Qed.
Lemma lem7222396 : term101 = term54.
Proof. exact (TRANS (@lem7222311) (@lem7222395)). Qed.
Lemma lem7222398 (x : real) : (term73 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7222399 : term54 = term24.
Proof. exact (@lem7222398 term24). Qed.
Lemma lem7222400 : term101 = term24.
Proof. exact (TRANS (@lem7222396) (@lem7222399)). Qed.
Lemma lem7222401 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7222402 : term120 = term115.
Proof. exact (MK_COMB (@lem7222401) (@lem7222400)). Qed.
Lemma lem7222403 (_96841 : int) : (real_of_int _96841) = (real_of_int _96841).
Proof. exact (eq_refl (real_of_int _96841)). Qed.
Lemma lem7222404 (_96841 : int) : (term98 _96841) = (term121 _96841).
Proof. exact (MK_COMB (@lem7222402) (@lem7222403 _96841)). Qed.
Lemma lem7222405 (_96841 : int) : (term97 _96841) = (term121 _96841).
Proof. exact (TRANS (@lem7222302 _96841) (@lem7222404 _96841)). Qed.
Lemma lem7222406 (_96841 : int) : (term121 _96841) = term24.
Proof. exact (@lem1982719 (real_of_int _96841)). Qed.
Lemma lem7222407 (_96841 : int) : (term97 _96841) = term24.
Proof. exact (TRANS (@lem7222405 _96841) (@lem7222406 _96841)). Qed.
Lemma lem7222408 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7222409 (_96841 : int) : (term122 _96841) = term123.
Proof. exact (MK_COMB (@lem7222408) (@lem7222407 _96841)). Qed.
Lemma lem7222410 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem7222411 (_96841 : int) : (term95 _96841) = term124.
Proof. exact (MK_COMB (@lem7222409 _96841) (@lem7222410)). Qed.
Lemma lem7222412 (_96841 : int) : (term94 _96841) = term124.
Proof. exact (TRANS (@lem7222301 _96841) (@lem7222411 _96841)). Qed.
Lemma lem7222413 : term124 = term57.
Proof. exact (@lem1982721 term57). Qed.
Lemma lem7222414 (_96841 : int) : (term94 _96841) = term57.
Proof. exact (TRANS (@lem7222412 _96841) (@lem7222413)). Qed.
Lemma lem7222415 (_96841 : int) : (term80 _96841) = term57.
Proof. exact (TRANS (@lem7222300 _96841) (@lem7222414 _96841)). Qed.
Lemma lem7222417 (_96841 : int) : (term79 _96841) = term57.
Proof. exact (TRANS (@lem7222255 _96841) (@lem7222415 _96841)). Qed.
Lemma lem7222418 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7222419 (_96841 : int) : (term125 _96841) = term126.
Proof. exact (MK_COMB (@lem7222418) (@lem7222417 _96841)). Qed.
Lemma lem7222420 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem7222421 (_96841 : int) : (term78 _96841) = term127.
Proof. exact (MK_COMB (@lem7222419 _96841) (@lem7222420)). Qed.
Lemma lem7222422 (_96841 : int) : (term44 _96841) = term127.
Proof. exact (TRANS (@lem7222243 _96841) (@lem7222421 _96841)). Qed.
Lemma lem7222423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7222424 (_96841 : int) : (term46 _96841) = (term128 _96841).
Proof. exact (MK_COMB (@lem7222423) (@lem7222242 _96841)). Qed.
Lemma lem7222425 (_96841 : int) : (term47 _96841) = (term129 _96841).
Proof. exact (MK_COMB (@lem7222424 _96841) (@lem7222422 _96841)). Qed.
Lemma lem7222440 (_96841 : int) : (term49 _96841) = (term129 _96841).
Proof. exact (TRANS (@lem7222194 _96841) (@lem7222425 _96841)). Qed.
Lemma lem7222444 (_96841 : int) (h1 : term129 _96841) : term129 _96841.
Proof. exact (h1). Qed.
Lemma lem7222445 (_96841 : int) (h1 : term129 _96841) : term127.
Proof. exact (proj2 (@lem7222444 _96841 h1)). Qed.
Lemma lem7222448 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7222449 : term127 = term130.
Proof. exact (@lem7222448 term24 term57). Qed.
Lemma lem7222451 (x : nat) : (term55 x) = (term56 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7222452 : term57 = term58.
Proof. exact (@lem7222451 term8). Qed.
Lemma lem7222454 (x : nat) : (real_of_num x) = (term53 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7222455 : term24 = term54.
Proof. exact (@lem7222454 (NUMERAL 0)). Qed.
Lemma lem7222456 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7222457 : term26 = term131.
Proof. exact (MK_COMB (@lem7222456) (@lem7222455)). Qed.
Lemma lem7222458 : term130 = term132.
Proof. exact (MK_COMB (@lem7222457) (@lem7222452)). Qed.
Lemma lem7222459 : term133.
Proof. exact (@lem1980026 term24 term39 term57 term39). Qed.
Lemma lem7222461 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7222462 : term105 = term106.
Proof. exact (@lem7222461 (NUMERAL 0) term8). Qed.
Lemma lem7222463 : term107 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7222464 (h1 : term107 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7222465 : (term107 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term107 = (BIT1 0) => @lem7222464 h1) (fun h1 : term106 = True => @lem7222463)). Qed.
Lemma lem7222466 : term106 = True.
Proof. exact (EQ_MP (@lem7222465) (@lem7222463)). Qed.
Lemma lem7222467 : term105 = True.
Proof. exact (TRANS (@lem7222462) (@lem7222466)). Qed.
Lemma lem7222468 : True = term105.
Proof. exact (SYM (@lem7222467)). Qed.
Lemma lem7222469 : term105.
Proof. exact (EQ_MP (@lem7222468) (@lem0)). Qed.
Lemma lem7222470 : term134.
Proof. exact (@lem7222459 (@lem7222469)). Qed.
Lemma lem7222472 (m : nat) (n : nat) : (term104 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7222473 : term105 = term106.
Proof. exact (@lem7222472 (NUMERAL 0) term8). Qed.
Lemma lem7222474 : term107 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7222475 (h1 : term107 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7222476 : (term107 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term107 = (BIT1 0) => @lem7222475 h1) (fun h1 : term106 = True => @lem7222474)). Qed.
Lemma lem7222477 : term106 = True.
Proof. exact (EQ_MP (@lem7222476) (@lem7222474)). Qed.
Lemma lem7222478 : term105 = True.
Proof. exact (TRANS (@lem7222473) (@lem7222477)). Qed.
Lemma lem7222479 : True = term105.
Proof. exact (SYM (@lem7222478)). Qed.
Lemma lem7222480 : term105.
Proof. exact (EQ_MP (@lem7222479) (@lem0)). Qed.
Lemma lem7222481 : term132 = term135.
Proof. exact (@lem7222470 (@lem7222480)). Qed.
Lemma lem7222483 (m : nat) (n : nat) : (term87 m n) = (term88 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7222484 : term84 = term89.
Proof. exact (@lem7222483 term8 term8). Qed.
Lemma lem7222485 : (term68 = (BIT1 0)) = (term69 = term8).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7222486 : term69 = term8.
Proof. exact (EQ_MP (@lem7222485) (@lem940073)). Qed.
Lemma lem7222487 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7222488 : term67 = term39.
Proof. exact (MK_COMB (@lem7222487) (@lem7222486)). Qed.
Lemma lem7222489 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7222490 : term89 = term57.
Proof. exact (MK_COMB (@lem7222489) (@lem7222488)). Qed.
Lemma lem7222491 : term84 = term57.
Proof. exact (TRANS (@lem7222484) (@lem7222490)). Qed.
Lemma lem7222493 (x : nat) : (term118 x) = term24.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7222494 : term117 = term24.
Proof. exact (@lem7222493 term8). Qed.
Lemma lem7222495 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7222496 : term136 = term26.
Proof. exact (MK_COMB (@lem7222495) (@lem7222494)). Qed.
Lemma lem7222497 : term135 = term130.
Proof. exact (MK_COMB (@lem7222496) (@lem7222491)). Qed.
Lemma lem7222499 (m : nat) (n : nat) : (term137 m n) = (term138 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7222500 : term130 = term139.
Proof. exact (@lem7222499 (NUMERAL 0) term8). Qed.
Lemma lem7222501 : term107 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7222502 (h1 : term107 = (BIT1 0)) : (term8 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7222503 : (term107 = (BIT1 0)) = ((term8 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term107 = (BIT1 0) => @lem7222502 h1) (fun h1 : (term8 = (NUMERAL 0)) = False => @lem7222501)). Qed.
Lemma lem7222504 : (term8 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7222503) (@lem7222501)). Qed.
Lemma lem7222505 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7222506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7222507 : term140 = (and True).
Proof. exact (MK_COMB (@lem7222506) (@lem7222505)). Qed.
Lemma lem7222508 : term139 = (True /\ False).
Proof. exact (MK_COMB (@lem7222507) (@lem7222504)). Qed.
Lemma lem7222510 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7222511 : term139 = False.
Proof. exact (TRANS (@lem7222508) (@lem7222510)). Qed.
Lemma lem7222512 : term130 = False.
Proof. exact (TRANS (@lem7222500) (@lem7222511)). Qed.
Lemma lem7222513 : term135 = False.
Proof. exact (TRANS (@lem7222497) (@lem7222512)). Qed.
Lemma lem7222514 : term132 = False.
Proof. exact (TRANS (@lem7222481) (@lem7222513)). Qed.
Lemma lem7222515 : term130 = False.
Proof. exact (TRANS (@lem7222458) (@lem7222514)). Qed.
Lemma lem7222516 : term127 = False.
Proof. exact (TRANS (@lem7222449) (@lem7222515)). Qed.
Lemma lem7222517 (_96841 : int) (h1 : term129 _96841) : False.
Proof. exact (EQ_MP (@lem7222516) (@lem7222445 _96841 h1)). Qed.
Lemma lem7222519 (_96841 : int) (h1 : term129 _96841) : term129 _96841.
Proof. exact (h1). Qed.
Lemma lem7222520 (_96841 : int) (h1 : term129 _96841) : (term129 _96841) = False.
Proof. exact (prop_ext (fun h2 : term129 _96841 => @lem7222517 _96841 h1) (fun h2 : False => @lem7222519 _96841 h1)). Qed.
Lemma lem7222521 (_96841 : int) (h1 : term129 _96841) : False.
Proof. exact (EQ_MP (@lem7222520 _96841 h1) (@lem7222519 _96841 h1)). Qed.
Lemma lem7222522 (_96841 : int) (h1 : term49 _96841) : term49 _96841.
Proof. exact (h1). Qed.
Lemma lem7222523 (_96841 : int) (h1 : term49 _96841) : term129 _96841.
Proof. exact (EQ_MP (@lem7222440 _96841) (@lem7222522 _96841 h1)). Qed.
Lemma lem7222524 (_96841 : int) (h1 : term49 _96841) : (term129 _96841) = False.
Proof. exact (prop_ext (fun h2 : term129 _96841 => @lem7222521 _96841 h2) (fun h2 : False => @lem7222523 _96841 h1)). Qed.
Lemma lem7222525 (_96841 : int) (h1 : term49 _96841) : False.
Proof. exact (EQ_MP (@lem7222524 _96841 h1) (@lem7222523 _96841 h1)). Qed.
Lemma lem7222526 (_96841 : int) : term141 _96841.
Proof. exact (fun h0 : term49 _96841 => @lem7222525 _96841 h0). Qed.
Lemma lem7222527 (_96841 : int) : term142 _96841.
Proof. exact (@lem1386578 (term143 _96841)). Qed.
Lemma lem7222530 (_96841 : int) : term143 _96841.
Proof. exact (@lem7222527 _96841 (@lem7222526 _96841)). Qed.
Lemma lem7222531 (_96841 : int) : (term47 _96841) = (term15 _96841).
Proof. exact (SYM (@lem7222174 _96841)). Qed.
Lemma lem7222532 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7222533 (_96841 : int) : (term143 _96841) = (term13 _96841).
Proof. exact (MK_COMB (@lem7222532) (@lem7222531 _96841)). Qed.
Lemma lem7222534 (_96841 : int) : term13 _96841.
Proof. exact (EQ_MP (@lem7222533 _96841) (@lem7222530 _96841)). Qed.
Lemma lem7222535 (_96841 : int) : term14 _96841.
Proof. exact (EQ_MP (@lem7222113 _96841) (@lem7222534 _96841)). Qed.
Lemma lem7222536 (x : nat) : term144 x.
Proof. exact (@lem7222535 (int_of_num x)). Qed.
Lemma lem7222537 (x : nat) : term10 x.
Proof. exact (@lem7222536 x (@lem7222112 x)). Qed.
Lemma lem7222538 (x : nat) : (term10 x) = (term1 x).
Proof. exact (SYM (@lem7222109 x)). Qed.
Lemma lem7222539 (x : nat) : term1 x.
Proof. exact (EQ_MP (@lem7222538 x) (@lem7222537 x)). Qed.
Lemma lem7222540 (x : nat) : (term1 x) = ((term1 x) = True).
Proof. exact (@lem7 (term1 x)). Qed.
Lemma lem7222542 (m : nat) : term145 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7222543 (m : nat) : (term145 m) = (term146 m).
Proof. exact (eq_refl (term145 m)). Qed.
Lemma lem7222544 (m : nat) : term146 m.
Proof. exact (EQ_MP (@lem7222543 m) (@lem7222542 m)). Qed.
Lemma lem7222545 (m : nat) (n : nat) : term147 m n.
Proof. exact (@lem7222544 m n). Qed.
Lemma lem7222546 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (eq_refl (term147 m n)). Qed.
Lemma lem7222547 (m : nat) (n : nat) : term148 m n.
Proof. exact (EQ_MP (@lem7222546 m n) (@lem7222545 m n)). Qed.
Lemma lem7222548 (m : nat) (n : nat) : (term148 m n) = ((term148 m n) = True).
Proof. exact (@lem7 (term148 m n)). Qed.
Lemma lem7222550 (m : nat) : term149 m.
Proof. exact (@lem5451441 m). Qed.
Lemma lem7222551 (m : nat) : (term149 m) = (term150 m).
Proof. exact (eq_refl (term149 m)). Qed.
Lemma lem7222552 (m : nat) : term150 m.
Proof. exact (EQ_MP (@lem7222551 m) (@lem7222550 m)). Qed.
Lemma lem7222553 (m : nat) (n : nat) : term151 m n.
Proof. exact (@lem7222552 m n). Qed.
Lemma lem7222554 (n : nat) (m : nat) : (term151 m n) = (term152 n m).
Proof. exact (eq_refl (term151 m n)). Qed.
Lemma lem7222555 (n : nat) (m : nat) : term152 n m.
Proof. exact (EQ_MP (@lem7222554 n m) (@lem7222553 m n)). Qed.
Lemma lem7222556 (n : nat) (m : nat) (p : nat) : term153 n m p.
Proof. exact (@lem7222555 n m p). Qed.
Lemma lem7222557 (n : nat) (m : nat) (p : nat) : (term153 n m p) = (term154 n m p).
Proof. exact (eq_refl (term153 n m p)). Qed.
Lemma lem7222558 (n : nat) (m : nat) (p : nat) : term154 n m p.
Proof. exact (EQ_MP (@lem7222557 n m p) (@lem7222556 n m p)). Qed.
Lemma lem7222559 (n : nat) (m : nat) (p : nat) (q : nat) : term155 n m p q.
Proof. exact (@lem7222558 n m p q). Qed.
Lemma lem7222560 (n : nat) (m : nat) (q : nat) (p : nat) : (term155 n m p q) = ((term156 m n p q) = (term157 n m q p)).
Proof. exact (eq_refl (term155 n m p q)). Qed.
Lemma lem7222562 {_131550 : Type'} (f : _131550 -> real) : term158 _131550 f.
Proof. exact (@lem7067826 _131550 f). Qed.
Lemma lem7222563 {_131550 : Type'} (f : _131550 -> real) : (term158 _131550 f) = (term159 _131550 f).
Proof. exact (eq_refl (term158 _131550 f)). Qed.
Lemma lem7222564 {_131550 : Type'} (f : _131550 -> real) : term159 _131550 f.
Proof. exact (EQ_MP (@lem7222563 _131550 f) (@lem7222562 _131550 f)). Qed.
Lemma lem7222565 {_131550 : Type'} (f : _131550 -> real) (s : _131550 -> Prop) : term160 _131550 f s.
Proof. exact (@lem7222564 _131550 f s). Qed.
Lemma lem7222566 {_131550 : Type'} (s : _131550 -> Prop) (f : _131550 -> real) : (term160 _131550 f s) = (term161 _131550 s f).
Proof. exact (eq_refl (term160 _131550 f s)). Qed.
Lemma lem7222567 {_131550 : Type'} (s : _131550 -> Prop) (f : _131550 -> real) : term161 _131550 s f.
Proof. exact (EQ_MP (@lem7222566 _131550 s f) (@lem7222565 _131550 f s)). Qed.
Lemma lem7222568 {_131550 : Type'} (s : _131550 -> Prop) (f : _131550 -> real) (t : _131550 -> Prop) : term162 _131550 s f t.
Proof. exact (@lem7222567 _131550 s f t). Qed.
Lemma lem7222569 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) : (term162 _131550 s f t) = (term163 _131550 s t f).
Proof. exact (eq_refl (term162 _131550 s f t)). Qed.
Lemma lem7222570 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) : term163 _131550 s t f.
Proof. exact (EQ_MP (@lem7222569 _131550 s t f) (@lem7222568 _131550 s f t)). Qed.
Lemma lem7222571 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term164 _131550 s t) : term164 _131550 s t.
Proof. exact (h1). Qed.
Lemma lem7222572 {_131550 : Type'} (f : _131550 -> real) (s : _131550 -> Prop) (t : _131550 -> Prop) (h1 : term164 _131550 s t) : (term165 _131550 s t f) = (term166 _131550 s t f).
Proof. exact (@lem7222570 _131550 s t f (@lem7222571 _131550 s t h1)). Qed.
Lemma lem7222578 (m : nat) : term167 m.
Proof. exact (@lem5459080 m). Qed.
Lemma lem7222579 (m : nat) : (term167 m) = (term168 m).
Proof. exact (eq_refl (term167 m)). Qed.
Lemma lem7222580 (m : nat) : term168 m.
Proof. exact (EQ_MP (@lem7222579 m) (@lem7222578 m)). Qed.
Lemma lem7222581 (m : nat) (n : nat) : term169 m n.
Proof. exact (@lem7222580 m n). Qed.
Lemma lem7222582 (m : nat) (n : nat) : (term169 m n) = (term170 m n).
Proof. exact (eq_refl (term169 m n)). Qed.
Lemma lem7222583 (m : nat) (n : nat) : term170 m n.
Proof. exact (EQ_MP (@lem7222582 m n) (@lem7222581 m n)). Qed.
Lemma lem7222584 (m : nat) (n : nat) (p : nat) : term171 m n p.
Proof. exact (@lem7222583 m n p). Qed.
Lemma lem7222585 (m : nat) (n : nat) (p : nat) : (term171 m n p) = (term172 m n p).
Proof. exact (eq_refl (term171 m n p)). Qed.
Lemma lem7222586 (m : nat) (n : nat) (p : nat) : term172 m n p.
Proof. exact (EQ_MP (@lem7222585 m n p) (@lem7222584 m n p)). Qed.
Lemma lem7222587 (m : nat) (n : nat) (h1 : term173 m n) : term173 m n.
Proof. exact (h1). Qed.
Lemma lem7222588 (p : nat) (m : nat) (n : nat) (h1 : term173 m n) : (term174 m n p) = (term175 m n p).
Proof. exact (@lem7222586 m n p (@lem7222587 m n h1)). Qed.
Lemma lem7222613 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term176 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7222614 (p : Prop) (q : Prop) (p' : Prop) : term177 p q p'.
Proof. exact (fun q' : Prop => @lem7222613 p q p' q'). Qed.
Lemma lem7222615 (p : Prop) (q : Prop) : term178 p q.
Proof. exact (fun p' : Prop => @lem7222614 p q p'). Qed.
Lemma lem7222616 (m : nat) (n : nat) (p : nat) (f : nat -> real) : term179 m n p f.
Proof. exact (@lem7222615 (term173 m n) ((term180 m n p f) = (term181 m n p f))). Qed.
Lemma lem7222617 (m : nat) (n : nat) (p : nat) (f : nat -> real) (p' : Prop) : term182 m n p f p'.
Proof. exact (@lem7222616 m n p f p'). Qed.
Lemma lem7222618 (m : nat) (n : nat) (p : nat) (f : nat -> real) (p' : Prop) : (term182 m n p f p') = (term183 m n p f p').
Proof. exact (eq_refl (term182 m n p f p')). Qed.
Lemma lem7222619 (m : nat) (n : nat) (p : nat) (f : nat -> real) (p' : Prop) : term183 m n p f p'.
Proof. exact (EQ_MP (@lem7222618 m n p f p') (@lem7222617 m n p f p')). Qed.
Lemma lem7222620 (m : nat) (n : nat) (p : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : term184 m n p f p' q'.
Proof. exact (@lem7222619 m n p f p' q'). Qed.
Lemma lem7222621 (m : nat) (n : nat) (p : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : (term184 m n p f p' q') = (term185 m n p f p' q').
Proof. exact (eq_refl (term184 m n p f p' q')). Qed.
Lemma lem7222622 (m : nat) (n : nat) (p : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : term185 m n p f p' q'.
Proof. exact (EQ_MP (@lem7222621 m n p f p' q') (@lem7222620 m n p f p' q')). Qed.
Lemma lem7222623 (m : nat) (n : nat) : (term173 m n) = (term173 m n).
Proof. exact (eq_refl (term173 m n)). Qed.
Lemma lem7222624 (p : nat) (f : nat -> real) (m : nat) (n : nat) (q' : Prop) : term186 p f m n q'.
Proof. exact (@lem7222622 m n p f (term173 m n) q'). Qed.
Lemma lem7222625 (p : nat) (f : nat -> real) (m : nat) (n : nat) (q' : Prop) : term187 p f m n q'.
Proof. exact (@lem7222624 p f m n q' (@lem7222623 m n)). Qed.
Lemma lem7222626 (m : nat) (n : nat) (h1 : term173 m n) : term173 m n.
Proof. exact (h1). Qed.
Lemma lem7222627 (m : nat) (n : nat) : (term173 m n) = ((term173 m n) = True).
Proof. exact (@lem7 (term173 m n)). Qed.
Lemma lem7222632 (m : nat) (n : nat) (p : nat) : term172 m n p.
Proof. exact (fun h0 : term173 m n => @lem7222588 p m n h0). Qed.
Lemma lem7222634 (m : nat) (n : nat) (h1 : term173 m n) : (term173 m n) = True.
Proof. exact (EQ_MP (@lem7222627 m n) (@lem7222626 m n h1)). Qed.
Lemma lem7222635 (m : nat) (n : nat) (h1 : term173 m n) : True = (term173 m n).
Proof. exact (SYM (@lem7222634 m n h1)). Qed.
Lemma lem7222636 (m : nat) (n : nat) (h1 : term173 m n) : term173 m n.
Proof. exact (EQ_MP (@lem7222635 m n h1) (@lem0)). Qed.
Lemma lem7222637 (p : nat) (m : nat) (n : nat) (h1 : term173 m n) : (term174 m n p) = (term175 m n p).
Proof. exact (@lem7222632 m n p (@lem7222636 m n h1)). Qed.
Lemma lem7222643 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7222644 (p : nat) (m : nat) (n : nat) (h1 : term173 m n) : (term188 m n p) = (term189 m n p).
Proof. exact (MK_COMB (@lem7222643) (@lem7222637 p m n h1)). Qed.
Lemma lem7222650 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7222651 (p : nat) (f : nat -> real) (m : nat) (n : nat) (h1 : term173 m n) : (term180 m n p f) = (term190 m n p f).
Proof. exact (MK_COMB (@lem7222644 p m n h1) (@lem7222650 f)). Qed.
Lemma lem7222653 {_131550 : Type'} (s : _131550 -> Prop) (t : _131550 -> Prop) (f : _131550 -> real) : term163 _131550 s t f.
Proof. exact (fun h0 : term164 _131550 s t => @lem7222572 _131550 f s t h0). Qed.
Lemma lem7222654 (s : nat -> Prop) (t : nat -> Prop) (f : nat -> real) : term191 s t f.
Proof. exact (@lem7222653 nat s t f). Qed.
Lemma lem7222655 (m : nat) (n : nat) (p : nat) (f : nat -> real) : term192 m n p f.
Proof. exact (@lem7222654 (dotdot m n) (term193 n p) f). Qed.
Lemma lem7222659 (m : nat) (n : nat) : (term148 m n) = True.
Proof. exact (EQ_MP (@lem7222548 m n) (@lem7222547 m n)). Qed.
Lemma lem7222660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7222661 (m : nat) (n : nat) : (term194 m n) = (and True).
Proof. exact (MK_COMB (@lem7222660) (@lem7222659 m n)). Qed.
Lemma lem7222665 (m : nat) (n : nat) : (term148 m n) = True.
Proof. exact (EQ_MP (@lem7222548 m n) (@lem7222547 m n)). Qed.
Lemma lem7222666 (n : nat) (p : nat) : (term195 n p) = True.
Proof. exact (@lem7222665 (term3 n) (Nat.add n p)). Qed.
Lemma lem7222667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7222668 (n : nat) (p : nat) : (term196 n p) = (and True).
Proof. exact (MK_COMB (@lem7222667) (@lem7222666 n p)). Qed.
Lemma lem7222670 (n : nat) (m : nat) (q : nat) (p : nat) : (term156 m n p q) = (term157 n m q p).
Proof. exact (EQ_MP (@lem7222560 n m q p) (@lem7222559 n m p q)). Qed.
Lemma lem7222671 (m : nat) (p : nat) (n : nat) : (term197 m n p) = (term198 m p n).
Proof. exact (@lem7222670 n m (Nat.add n p) (term3 n)). Qed.
Lemma lem7222675 (x : nat) : (term1 x) = True.
Proof. exact (EQ_MP (@lem7222540 x) (@lem7222539 x)). Qed.
Lemma lem7222676 (n : nat) : (term1 n) = True.
Proof. exact (@lem7222675 n). Qed.
Lemma lem7222677 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7222678 (n : nat) : (term199 n) = (or True).
Proof. exact (MK_COMB (@lem7222677) (@lem7222676 n)). Qed.
Lemma lem7222685 (m : nat) (p : nat) (n : nat) : (term200 m p n) = (term200 m p n).
Proof. exact (eq_refl (term200 m p n)). Qed.
Lemma lem7222686 (m : nat) (p : nat) (n : nat) : (term198 m p n) = (term201 m p n).
Proof. exact (MK_COMB (@lem7222678 n) (@lem7222685 m p n)). Qed.
Lemma lem7222688 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem7222689 (m : nat) (p : nat) (n : nat) : (term201 m p n) = True.
Proof. exact (@lem7222688 (term200 m p n)). Qed.
Lemma lem7222690 (m : nat) (p : nat) (n : nat) : (term198 m p n) = True.
Proof. exact (TRANS (@lem7222686 m p n) (@lem7222689 m p n)). Qed.
Lemma lem7222691 (m : nat) (n : nat) (p : nat) : (term197 m n p) = True.
Proof. exact (TRANS (@lem7222671 m p n) (@lem7222690 m p n)). Qed.
Lemma lem7222692 (m : nat) (n : nat) (p : nat) : (term202 m n p) = (True /\ True).
Proof. exact (MK_COMB (@lem7222668 n p) (@lem7222691 m n p)). Qed.
Lemma lem7222694 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7222695 : (True /\ True) = True.
Proof. exact (@lem7222694 True). Qed.
Lemma lem7222696 (m : nat) (n : nat) (p : nat) : (term202 m n p) = True.
Proof. exact (TRANS (@lem7222692 m n p) (@lem7222695)). Qed.
Lemma lem7222697 (m : nat) (n : nat) (p : nat) : (term203 m n p) = (True /\ True).
Proof. exact (MK_COMB (@lem7222661 m n) (@lem7222696 m n p)). Qed.
Lemma lem7222699 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7222700 : (True /\ True) = True.
Proof. exact (@lem7222699 True). Qed.
Lemma lem7222701 (m : nat) (n : nat) (p : nat) : (term203 m n p) = True.
Proof. exact (TRANS (@lem7222697 m n p) (@lem7222700)). Qed.
Lemma lem7222702 (m : nat) (n : nat) (p : nat) : True = (term203 m n p).
Proof. exact (SYM (@lem7222701 m n p)). Qed.
Lemma lem7222703 (m : nat) (n : nat) (p : nat) : term203 m n p.
Proof. exact (EQ_MP (@lem7222702 m n p) (@lem0)). Qed.
Lemma lem7222704 (m : nat) (n : nat) (p : nat) (f : nat -> real) : (term190 m n p f) = (term181 m n p f).
Proof. exact (@lem7222655 m n p f (@lem7222703 m n p)). Qed.
Lemma lem7222710 (p : nat) (f : nat -> real) (m : nat) (n : nat) (h1 : term173 m n) : (term180 m n p f) = (term181 m n p f).
Proof. exact (TRANS (@lem7222651 p f m n h1) (@lem7222704 m n p f)). Qed.
Lemma lem7222711 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7222712 (p : nat) (f : nat -> real) (m : nat) (n : nat) (h1 : term173 m n) : (term204 m n p f) = (term205 m n p f).
Proof. exact (MK_COMB (@lem7222711) (@lem7222710 p f m n h1)). Qed.
Lemma lem7222723 (m : nat) (n : nat) (p : nat) (f : nat -> real) : (term181 m n p f) = (term181 m n p f).
Proof. exact (eq_refl (term181 m n p f)). Qed.
Lemma lem7222724 (p : nat) (f : nat -> real) (m : nat) (n : nat) (h1 : term173 m n) : ((term180 m n p f) = (term181 m n p f)) = ((term181 m n p f) = (term181 m n p f)).
Proof. exact (MK_COMB (@lem7222712 p f m n h1) (@lem7222723 m n p f)). Qed.
Lemma lem7222726 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7222727 (x : real) : (x = x) = True.
Proof. exact (@lem7222726 real x). Qed.
Lemma lem7222728 (m : nat) (n : nat) (p : nat) (f : nat -> real) : ((term181 m n p f) = (term181 m n p f)) = True.
Proof. exact (@lem7222727 (term181 m n p f)). Qed.
Lemma lem7222729 (p : nat) (f : nat -> real) (m : nat) (n : nat) (h1 : term173 m n) : ((term180 m n p f) = (term181 m n p f)) = True.
Proof. exact (TRANS (@lem7222724 p f m n h1) (@lem7222728 m n p f)). Qed.
Lemma lem7222730 (m : nat) (n : nat) (p : nat) (f : nat -> real) : term206 m n p f.
Proof. exact (fun h0 : term173 m n => @lem7222729 p f m n h0). Qed.
Lemma lem7222731 (p : nat) (f : nat -> real) (m : nat) (n : nat) : term207 p f m n.
Proof. exact (@lem7222625 p f m n True). Qed.
Lemma lem7222732 (p : nat) (f : nat -> real) (m : nat) (n : nat) : (term208 m n p f) = (term209 m n).
Proof. exact (@lem7222731 p f m n (@lem7222730 m n p f)). Qed.
Lemma lem7222734 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7222735 (m : nat) (n : nat) : (term209 m n) = True.
Proof. exact (@lem7222734 (term173 m n)). Qed.
Lemma lem7222736 (m : nat) (n : nat) (p : nat) (f : nat -> real) : (term208 m n p f) = True.
Proof. exact (TRANS (@lem7222732 p f m n) (@lem7222735 m n)). Qed.
Lemma lem7222737 (m : nat) (n : nat) (f : nat -> real) : (term210 m n f) = term211.
Proof. exact (fun_ext (fun p : nat => @lem7222736 m n p f)). Qed.
Lemma lem7222738 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7222739 (m : nat) (n : nat) (f : nat -> real) : (term212 m n f) = term213.
Proof. exact (MK_COMB (@lem7222738) (@lem7222737 m n f)). Qed.
Lemma lem7222741 {A : Type'} (t : Prop) : (term214 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7222742 (t : Prop) : (term215 t) = t.
Proof. exact (@lem7222741 nat t). Qed.
Lemma lem7222743 : term213 = True.
Proof. exact (@lem7222742 True). Qed.
Lemma lem7222744 (m : nat) (n : nat) (f : nat -> real) : (term212 m n f) = True.
Proof. exact (TRANS (@lem7222739 m n f) (@lem7222743)). Qed.
Lemma lem7222745 (m : nat) (f : nat -> real) : (term216 m f) = term211.
Proof. exact (fun_ext (fun n : nat => @lem7222744 m n f)). Qed.
Lemma lem7222746 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7222747 (m : nat) (f : nat -> real) : (term217 m f) = term213.
Proof. exact (MK_COMB (@lem7222746) (@lem7222745 m f)). Qed.
Lemma lem7222749 {A : Type'} (t : Prop) : (term214 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7222750 (t : Prop) : (term215 t) = t.
Proof. exact (@lem7222749 nat t). Qed.
Lemma lem7222751 : term213 = True.
Proof. exact (@lem7222750 True). Qed.
Lemma lem7222752 (m : nat) (f : nat -> real) : (term217 m f) = True.
Proof. exact (TRANS (@lem7222747 m f) (@lem7222751)). Qed.
Lemma lem7222753 (f : nat -> real) : (term218 f) = term211.
Proof. exact (fun_ext (fun m : nat => @lem7222752 m f)). Qed.
Lemma lem7222754 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7222755 (f : nat -> real) : (term219 f) = term213.
Proof. exact (MK_COMB (@lem7222754) (@lem7222753 f)). Qed.
Lemma lem7222757 {A : Type'} (t : Prop) : (term214 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7222758 (t : Prop) : (term215 t) = t.
Proof. exact (@lem7222757 nat t). Qed.
Lemma lem7222759 : term213 = True.
Proof. exact (@lem7222758 True). Qed.
Lemma lem7222760 (f : nat -> real) : (term219 f) = True.
Proof. exact (TRANS (@lem7222755 f) (@lem7222759)). Qed.
Lemma lem7222761 : term220 = term221.
Proof. exact (fun_ext (fun f : nat -> real => @lem7222760 f)). Qed.
Lemma lem7222762 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7222763 : term222 = term223.
Proof. exact (MK_COMB (@lem7222762) (@lem7222761)). Qed.
Lemma lem7222765 {A : Type'} (t : Prop) : (term214 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7222766 (t : Prop) : (term224 t) = t.
Proof. exact (@lem7222765 (nat -> real) t). Qed.
Lemma lem7222767 : term223 = True.
Proof. exact (@lem7222766 True). Qed.
Lemma lem7222768 : term222 = True.
Proof. exact (TRANS (@lem7222763) (@lem7222767)). Qed.
Lemma lem7222769 : True = term222.
Proof. exact (SYM (@lem7222768)). Qed.
Lemma lem7222770 : term222.
Proof. exact (EQ_MP (@lem7222769) (@lem0)). Qed.
