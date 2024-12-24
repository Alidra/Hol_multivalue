Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_REM_DIV_term_abbrevs.
Require Import INT_DIVISION_SIMP_spec.
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
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm1982733_spec.
Require Import thm1982749_spec.
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
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2397099 (m : int) : term0 m.
Proof. exact (@lem2394130 m). Qed.
Lemma lem2397100 (m : int) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2397101 (m : int) : term1 m.
Proof. exact (EQ_MP (@lem2397100 m) (@lem2397099 m)). Qed.
Lemma lem2397102 (m : int) (n : int) : term2 m n.
Proof. exact (@lem2397101 m n). Qed.
Lemma lem2397103 (n : int) (m : int) : (term2 m n) = ((term3 m n) = m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2397105 (c : int) (a : int) (b : int) : (term4 c a b) = ((a = (int_sub b c)) = ((int_add c a) = b)).
Proof. exact (@lem2318604 ((a = (int_sub b c)) = ((int_add c a) = b))). Qed.
Lemma lem2397144 (c : int) (a : int) (b : int) : (term5 c a b) = (term6 c a b).
Proof. exact (@lem17646 (a = (int_sub b c)) ((int_add c a) = b)). Qed.
Lemma lem2397147 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2397148 (a : int) (b : int) (c : int) : (a = (int_sub b c)) = ((real_of_int a) = (term7 b c)).
Proof. exact (@lem2397147 a (int_sub b c)). Qed.
Lemma lem2397152 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2397153 (b : int) (c : int) : (term7 b c) = (term8 b c).
Proof. exact (@lem2397152 b c). Qed.
Lemma lem2397154 (a : int) : (term9 a) = (term9 a).
Proof. exact (eq_refl (term9 a)). Qed.
Lemma lem2397155 (a : int) (b : int) (c : int) : ((real_of_int a) = (term7 b c)) = ((real_of_int a) = (term8 b c)).
Proof. exact (MK_COMB (@lem2397154 a) (@lem2397153 b c)). Qed.
Lemma lem2397157 (a : int) (b : int) (c : int) : (a = (int_sub b c)) = ((real_of_int a) = (term8 b c)).
Proof. exact (TRANS (@lem2397148 a b c) (@lem2397155 a b c)). Qed.
Lemma lem2397159 (y : int) (x : int) : (term10 x y) = (term11 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2397160 (b : int) (c : int) (a : int) : (term12 c a b) = (term13 b c a).
Proof. exact (@lem2397159 b (int_add c a)). Qed.
Lemma lem2397162 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2397163 (c : int) (a : int) (b : int) : (term15 c a b) = (term16 c a b).
Proof. exact (@lem2397162 (term17 c a) b). Qed.
Lemma lem2397165 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2397166 (c : int) (a : int) : (term20 c a) = (term21 c a).
Proof. exact (@lem2397165 (int_add c a) term22). Qed.
Lemma lem2397168 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2397169 (c : int) (a : int) : (term18 c a) = (term19 c a).
Proof. exact (@lem2397168 c a). Qed.
Lemma lem2397170 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2397171 (c : int) (a : int) : (term23 c a) = (term24 c a).
Proof. exact (MK_COMB (@lem2397170) (@lem2397169 c a)). Qed.
Lemma lem2397173 (n : nat) : (term25 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2397174 : term26 = term27.
Proof. exact (@lem2397173 term28). Qed.
Lemma lem2397175 (c : int) (a : int) : (term21 c a) = (term29 c a).
Proof. exact (MK_COMB (@lem2397171 c a) (@lem2397174)). Qed.
Lemma lem2397176 (c : int) (a : int) : (term20 c a) = (term29 c a).
Proof. exact (TRANS (@lem2397166 c a) (@lem2397175 c a)). Qed.
Lemma lem2397177 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2397178 (c : int) (a : int) : (term30 c a) = (term31 c a).
Proof. exact (MK_COMB (@lem2397177) (@lem2397176 c a)). Qed.
Lemma lem2397179 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2397180 (c : int) (a : int) (b : int) : (term16 c a b) = (term32 c a b).
Proof. exact (MK_COMB (@lem2397178 c a) (@lem2397179 b)). Qed.
Lemma lem2397181 (c : int) (a : int) (b : int) : (term15 c a b) = (term32 c a b).
Proof. exact (TRANS (@lem2397163 c a b) (@lem2397180 c a b)). Qed.
Lemma lem2397182 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2397183 (c : int) (a : int) (b : int) : (term33 c a b) = (term34 c a b).
Proof. exact (MK_COMB (@lem2397182) (@lem2397181 c a b)). Qed.
Lemma lem2397185 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2397186 (b : int) (c : int) (a : int) : (term35 b c a) = (term36 b c a).
Proof. exact (@lem2397185 (term37 b) (int_add c a)). Qed.
Lemma lem2397188 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2397189 (b : int) : (term38 b) = (term39 b).
Proof. exact (@lem2397188 b term22). Qed.
Lemma lem2397191 (n : nat) : (term25 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2397192 : term26 = term27.
Proof. exact (@lem2397191 term28). Qed.
Lemma lem2397193 (b : int) : (term40 b) = (term40 b).
Proof. exact (eq_refl (term40 b)). Qed.
Lemma lem2397194 (b : int) : (term39 b) = (term41 b).
Proof. exact (MK_COMB (@lem2397193 b) (@lem2397192)). Qed.
Lemma lem2397195 (b : int) : (term38 b) = (term41 b).
Proof. exact (TRANS (@lem2397189 b) (@lem2397194 b)). Qed.
Lemma lem2397196 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2397197 (b : int) : (term42 b) = (term43 b).
Proof. exact (MK_COMB (@lem2397196) (@lem2397195 b)). Qed.
Lemma lem2397199 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2397200 (c : int) (a : int) : (term18 c a) = (term19 c a).
Proof. exact (@lem2397199 c a). Qed.
Lemma lem2397201 (b : int) (c : int) (a : int) : (term36 b c a) = (term44 b c a).
Proof. exact (MK_COMB (@lem2397197 b) (@lem2397200 c a)). Qed.
Lemma lem2397202 (b : int) (c : int) (a : int) : (term35 b c a) = (term44 b c a).
Proof. exact (TRANS (@lem2397186 b c a) (@lem2397201 b c a)). Qed.
Lemma lem2397203 (b : int) (c : int) (a : int) : (term13 b c a) = (term45 b c a).
Proof. exact (MK_COMB (@lem2397183 c a b) (@lem2397202 b c a)). Qed.
Lemma lem2397204 (b : int) (c : int) (a : int) : (term12 c a b) = (term45 b c a).
Proof. exact (TRANS (@lem2397160 b c a) (@lem2397203 b c a)). Qed.
Lemma lem2397205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2397206 (a : int) (b : int) (c : int) : (term46 a b c) = (term47 a b c).
Proof. exact (MK_COMB (@lem2397205) (@lem2397157 a b c)). Qed.
Lemma lem2397207 (b : int) (c : int) (a : int) : (term48 c a b) = (term49 b c a).
Proof. exact (MK_COMB (@lem2397206 a b c) (@lem2397204 b c a)). Qed.
Lemma lem2397209 (y : int) (x : int) : (term10 x y) = (term11 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2397210 (b : int) (c : int) (a : int) : (term50 a b c) = (term51 b c a).
Proof. exact (@lem2397209 (int_sub b c) a). Qed.
Lemma lem2397212 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2397213 (a : int) (b : int) (c : int) : (term52 a b c) = (term53 a b c).
Proof. exact (@lem2397212 (term37 a) (int_sub b c)). Qed.
Lemma lem2397215 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2397216 (a : int) : (term38 a) = (term39 a).
Proof. exact (@lem2397215 a term22). Qed.
Lemma lem2397218 (n : nat) : (term25 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2397219 : term26 = term27.
Proof. exact (@lem2397218 term28). Qed.
Lemma lem2397220 (a : int) : (term40 a) = (term40 a).
Proof. exact (eq_refl (term40 a)). Qed.
Lemma lem2397221 (a : int) : (term39 a) = (term41 a).
Proof. exact (MK_COMB (@lem2397220 a) (@lem2397219)). Qed.
Lemma lem2397222 (a : int) : (term38 a) = (term41 a).
Proof. exact (TRANS (@lem2397216 a) (@lem2397221 a)). Qed.
Lemma lem2397223 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2397224 (a : int) : (term42 a) = (term43 a).
Proof. exact (MK_COMB (@lem2397223) (@lem2397222 a)). Qed.
Lemma lem2397226 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2397227 (b : int) (c : int) : (term7 b c) = (term8 b c).
Proof. exact (@lem2397226 b c). Qed.
Lemma lem2397228 (a : int) (b : int) (c : int) : (term53 a b c) = (term54 a b c).
Proof. exact (MK_COMB (@lem2397224 a) (@lem2397227 b c)). Qed.
Lemma lem2397229 (a : int) (b : int) (c : int) : (term52 a b c) = (term54 a b c).
Proof. exact (TRANS (@lem2397213 a b c) (@lem2397228 a b c)). Qed.
Lemma lem2397230 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2397231 (a : int) (b : int) (c : int) : (term55 a b c) = (term56 a b c).
Proof. exact (MK_COMB (@lem2397230) (@lem2397229 a b c)). Qed.
Lemma lem2397233 (x : int) (y : int) : (int_le x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2397234 (b : int) (c : int) (a : int) : (term57 b c a) = (term58 b c a).
Proof. exact (@lem2397233 (term59 b c) a). Qed.
Lemma lem2397236 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2397237 (b : int) (c : int) : (term60 b c) = (term61 b c).
Proof. exact (@lem2397236 (int_sub b c) term22). Qed.
Lemma lem2397239 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2318527 x y) (@lem2318526 x y)). Qed.
Lemma lem2397240 (b : int) (c : int) : (term7 b c) = (term8 b c).
Proof. exact (@lem2397239 b c). Qed.
Lemma lem2397241 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2397242 (b : int) (c : int) : (term62 b c) = (term63 b c).
Proof. exact (MK_COMB (@lem2397241) (@lem2397240 b c)). Qed.
Lemma lem2397244 (n : nat) : (term25 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2397245 : term26 = term27.
Proof. exact (@lem2397244 term28). Qed.
Lemma lem2397246 (b : int) (c : int) : (term61 b c) = (term64 b c).
Proof. exact (MK_COMB (@lem2397242 b c) (@lem2397245)). Qed.
Lemma lem2397247 (b : int) (c : int) : (term60 b c) = (term64 b c).
Proof. exact (TRANS (@lem2397237 b c) (@lem2397246 b c)). Qed.
Lemma lem2397248 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2397249 (b : int) (c : int) : (term65 b c) = (term66 b c).
Proof. exact (MK_COMB (@lem2397248) (@lem2397247 b c)). Qed.
Lemma lem2397250 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2397251 (b : int) (c : int) (a : int) : (term58 b c a) = (term67 b c a).
Proof. exact (MK_COMB (@lem2397249 b c) (@lem2397250 a)). Qed.
Lemma lem2397252 (b : int) (c : int) (a : int) : (term57 b c a) = (term67 b c a).
Proof. exact (TRANS (@lem2397234 b c a) (@lem2397251 b c a)). Qed.
Lemma lem2397253 (b : int) (c : int) (a : int) : (term51 b c a) = (term68 b c a).
Proof. exact (MK_COMB (@lem2397231 a b c) (@lem2397252 b c a)). Qed.
Lemma lem2397254 (b : int) (c : int) (a : int) : (term50 a b c) = (term68 b c a).
Proof. exact (TRANS (@lem2397210 b c a) (@lem2397253 b c a)). Qed.
Lemma lem2397257 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2397258 (c : int) (a : int) (b : int) : ((int_add c a) = b) = ((term18 c a) = (real_of_int b)).
Proof. exact (@lem2397257 (int_add c a) b). Qed.
Lemma lem2397262 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2397263 (c : int) (a : int) : (term18 c a) = (term19 c a).
Proof. exact (@lem2397262 c a). Qed.
Lemma lem2397264 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2397265 (c : int) (a : int) : (term69 c a) = (term70 c a).
Proof. exact (MK_COMB (@lem2397264) (@lem2397263 c a)). Qed.
Lemma lem2397266 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2397267 (c : int) (a : int) (b : int) : ((term18 c a) = (real_of_int b)) = ((term19 c a) = (real_of_int b)).
Proof. exact (MK_COMB (@lem2397265 c a) (@lem2397266 b)). Qed.
Lemma lem2397269 (c : int) (a : int) (b : int) : ((int_add c a) = b) = ((term19 c a) = (real_of_int b)).
Proof. exact (TRANS (@lem2397258 c a b) (@lem2397267 c a b)). Qed.
Lemma lem2397270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2397271 (b : int) (c : int) (a : int) : (term71 a b c) = (term72 b c a).
Proof. exact (MK_COMB (@lem2397270) (@lem2397254 b c a)). Qed.
Lemma lem2397272 (c : int) (a : int) (b : int) : (term73 c a b) = (term74 c a b).
Proof. exact (MK_COMB (@lem2397271 b c a) (@lem2397269 c a b)). Qed.
Lemma lem2397273 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2397274 (b : int) (c : int) (a : int) : (term75 c a b) = (term76 b c a).
Proof. exact (MK_COMB (@lem2397273) (@lem2397207 b c a)). Qed.
Lemma lem2397275 (c : int) (a : int) (b : int) : (term6 c a b) = (term77 c a b).
Proof. exact (MK_COMB (@lem2397274 b c a) (@lem2397272 c a b)). Qed.
Lemma lem2397276 (c : int) (a : int) (b : int) : (term5 c a b) = (term77 c a b).
Proof. exact (TRANS (@lem2397144 c a b) (@lem2397275 c a b)). Qed.
Lemma lem2397280 (t : Prop) : (term78 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2397336 (c : int) (a : int) (b : int) : (term79 c a b) = (term77 c a b).
Proof. exact (@lem2397280 (term77 c a b)). Qed.
Lemma lem2397337 (a : int) (b : int) (c : int) : ((real_of_int a) = (term8 b c)) = ((term80 a b c) = term81).
Proof. exact (@lem1988293 (real_of_int a) (term8 b c)). Qed.
Lemma lem2397350 (b : int) (c : int) : (term8 b c) = (term82 b c).
Proof. exact (@lem1982792 (real_of_int b) (real_of_int c)). Qed.
Lemma lem2397353 (a : int) : (term83 a) = (term83 a).
Proof. exact (eq_refl (term83 a)). Qed.
Lemma lem2397354 (a : int) (b : int) (c : int) : (term80 a b c) = (term84 a b c).
Proof. exact (MK_COMB (@lem2397353 a) (@lem2397350 b c)). Qed.
Lemma lem2397355 (a : int) (b : int) (c : int) : (term84 a b c) = (term85 a b c).
Proof. exact (@lem1982792 (real_of_int a) (term82 b c)). Qed.
Lemma lem2397356 (b : int) (c : int) : (term86 b c) = (term87 b c).
Proof. exact (@lem1982781 (real_of_int b) term88 (term89 c)). Qed.
Lemma lem2397357 (c : int) : (term90 c) = (term91 c).
Proof. exact (@lem1982749 term88 term88 (real_of_int c)). Qed.
Lemma lem2397359 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2397360 : term88 = term94.
Proof. exact (@lem2397359 term28). Qed.
Lemma lem2397362 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2397363 : term88 = term94.
Proof. exact (@lem2397362 term28). Qed.
Lemma lem2397364 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2397365 : term95 = term96.
Proof. exact (MK_COMB (@lem2397364) (@lem2397363)). Qed.
Lemma lem2397366 : term97 = term98.
Proof. exact (MK_COMB (@lem2397365) (@lem2397360)). Qed.
Lemma lem2397367 : term98 = term99.
Proof. exact (@lem1981613 term88 term88 term27 term27). Qed.
Lemma lem2397369 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2397370 : term102 = term103.
Proof. exact (@lem2397369 term28 term28). Qed.
Lemma lem2397371 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397372 : term105 = term28.
Proof. exact (EQ_MP (@lem2397371) (@lem940073)). Qed.
Lemma lem2397373 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397374 : term103 = term27.
Proof. exact (MK_COMB (@lem2397373) (@lem2397372)). Qed.
Lemma lem2397375 : term102 = term27.
Proof. exact (TRANS (@lem2397370) (@lem2397374)). Qed.
Lemma lem2397377 (m : nat) (n : nat) : (term106 m n) = (term101 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2397378 : term97 = term103.
Proof. exact (@lem2397377 term28 term28). Qed.
Lemma lem2397379 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397380 : term105 = term28.
Proof. exact (EQ_MP (@lem2397379) (@lem940073)). Qed.
Lemma lem2397381 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397382 : term103 = term27.
Proof. exact (MK_COMB (@lem2397381) (@lem2397380)). Qed.
Lemma lem2397383 : term97 = term27.
Proof. exact (TRANS (@lem2397378) (@lem2397382)). Qed.
Lemma lem2397384 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2397385 : term107 = term108.
Proof. exact (MK_COMB (@lem2397384) (@lem2397383)). Qed.
Lemma lem2397386 : term99 = term109.
Proof. exact (MK_COMB (@lem2397385) (@lem2397375)). Qed.
Lemma lem2397387 : term98 = term109.
Proof. exact (TRANS (@lem2397367) (@lem2397386)). Qed.
Lemma lem2397388 : term97 = term109.
Proof. exact (TRANS (@lem2397366) (@lem2397387)). Qed.
Lemma lem2397390 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2397391 : term109 = term27.
Proof. exact (@lem2397390 term27). Qed.
Lemma lem2397392 : term97 = term27.
Proof. exact (TRANS (@lem2397388) (@lem2397391)). Qed.
Lemma lem2397393 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2397394 : term111 = term112.
Proof. exact (MK_COMB (@lem2397393) (@lem2397392)). Qed.
Lemma lem2397395 (c : int) : (real_of_int c) = (real_of_int c).
Proof. exact (eq_refl (real_of_int c)). Qed.
Lemma lem2397396 (c : int) : (term91 c) = (term113 c).
Proof. exact (MK_COMB (@lem2397394) (@lem2397395 c)). Qed.
Lemma lem2397397 (c : int) : (term90 c) = (term113 c).
Proof. exact (TRANS (@lem2397357 c) (@lem2397396 c)). Qed.
Lemma lem2397398 (c : int) : (term113 c) = (real_of_int c).
Proof. exact (@lem1982709 (real_of_int c)). Qed.
Lemma lem2397399 (c : int) : (term90 c) = (real_of_int c).
Proof. exact (TRANS (@lem2397397 c) (@lem2397398 c)). Qed.
Lemma lem2397402 (b : int) : (term114 b) = (term114 b).
Proof. exact (eq_refl (term114 b)). Qed.
Lemma lem2397403 (b : int) (c : int) : (term87 b c) = (term115 b c).
Proof. exact (MK_COMB (@lem2397402 b) (@lem2397399 c)). Qed.
Lemma lem2397404 (b : int) (c : int) : (term86 b c) = (term115 b c).
Proof. exact (TRANS (@lem2397356 b c) (@lem2397403 b c)). Qed.
Lemma lem2397405 (a : int) : (term40 a) = (term40 a).
Proof. exact (eq_refl (term40 a)). Qed.
Lemma lem2397408 (a : int) (b : int) (c : int) : (term85 a b c) = (term116 a b c).
Proof. exact (MK_COMB (@lem2397405 a) (@lem2397404 b c)). Qed.
Lemma lem2397409 (a : int) (b : int) (c : int) : (term84 a b c) = (term116 a b c).
Proof. exact (TRANS (@lem2397355 a b c) (@lem2397408 a b c)). Qed.
Lemma lem2397410 (a : int) (b : int) (c : int) : (term80 a b c) = (term116 a b c).
Proof. exact (TRANS (@lem2397354 a b c) (@lem2397409 a b c)). Qed.
Lemma lem2397411 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2397412 (a : int) (b : int) (c : int) : (term117 a b c) = (term118 a b c).
Proof. exact (MK_COMB (@lem2397411) (@lem2397410 a b c)). Qed.
Lemma lem2397413 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2397414 (a : int) (b : int) (c : int) : ((term80 a b c) = term81) = ((term116 a b c) = term81).
Proof. exact (MK_COMB (@lem2397412 a b c) (@lem2397413)). Qed.
Lemma lem2397415 (a : int) (b : int) (c : int) : ((real_of_int a) = (term8 b c)) = ((term116 a b c) = term81).
Proof. exact (TRANS (@lem2397337 a b c) (@lem2397414 a b c)). Qed.
Lemma lem2397416 (b : int) (c : int) (a : int) : (term32 c a b) = (term119 b c a).
Proof. exact (@lem1988287 (real_of_int b) (term29 c a)). Qed.
Lemma lem2397417 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2397424 (a : int) (c : int) : (term19 c a) = (term19 a c).
Proof. exact (@lem1982761 (real_of_int a) (real_of_int c)). Qed.
Lemma lem2397425 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2397426 (a : int) (c : int) : (term24 c a) = (term24 a c).
Proof. exact (MK_COMB (@lem2397425) (@lem2397424 a c)). Qed.
Lemma lem2397427 (a : int) (c : int) : (term29 c a) = (term29 a c).
Proof. exact (MK_COMB (@lem2397426 a c) (@lem2397417)). Qed.
Lemma lem2397432 (a : int) (c : int) : (term29 a c) = (term120 a c).
Proof. exact (@lem1982755 (real_of_int a) (real_of_int c) term27). Qed.
Lemma lem2397433 (a : int) (c : int) : (term29 c a) = (term120 a c).
Proof. exact (TRANS (@lem2397427 a c) (@lem2397432 a c)). Qed.
Lemma lem2397436 (b : int) : (term83 b) = (term83 b).
Proof. exact (eq_refl (term83 b)). Qed.
Lemma lem2397437 (b : int) (a : int) (c : int) : (term121 b c a) = (term122 b a c).
Proof. exact (MK_COMB (@lem2397436 b) (@lem2397433 a c)). Qed.
Lemma lem2397438 (b : int) (a : int) (c : int) : (term122 b a c) = (term123 b a c).
Proof. exact (@lem1982792 (real_of_int b) (term120 a c)). Qed.
Lemma lem2397439 (a : int) (c : int) : (term124 a c) = (term125 a c).
Proof. exact (@lem1982781 (real_of_int a) term88 (term41 c)). Qed.
Lemma lem2397440 (c : int) : (term126 c) = (term127 c).
Proof. exact (@lem1982781 (real_of_int c) term88 term27). Qed.
Lemma lem2397442 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2397443 : term27 = term109.
Proof. exact (@lem2397442 term28). Qed.
Lemma lem2397445 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2397446 : term88 = term94.
Proof. exact (@lem2397445 term28). Qed.
Lemma lem2397447 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2397448 : term95 = term96.
Proof. exact (MK_COMB (@lem2397447) (@lem2397446)). Qed.
Lemma lem2397449 : term129 = term130.
Proof. exact (MK_COMB (@lem2397448) (@lem2397443)). Qed.
Lemma lem2397450 : term130 = term131.
Proof. exact (@lem1981613 term88 term27 term27 term27). Qed.
Lemma lem2397452 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2397453 : term102 = term103.
Proof. exact (@lem2397452 term28 term28). Qed.
Lemma lem2397454 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397455 : term105 = term28.
Proof. exact (EQ_MP (@lem2397454) (@lem940073)). Qed.
Lemma lem2397456 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397457 : term103 = term27.
Proof. exact (MK_COMB (@lem2397456) (@lem2397455)). Qed.
Lemma lem2397458 : term102 = term27.
Proof. exact (TRANS (@lem2397453) (@lem2397457)). Qed.
Lemma lem2397460 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2397461 : term129 = term134.
Proof. exact (@lem2397460 term28 term28). Qed.
Lemma lem2397462 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397463 : term105 = term28.
Proof. exact (EQ_MP (@lem2397462) (@lem940073)). Qed.
Lemma lem2397464 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397465 : term103 = term27.
Proof. exact (MK_COMB (@lem2397464) (@lem2397463)). Qed.
Lemma lem2397466 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2397467 : term134 = term88.
Proof. exact (MK_COMB (@lem2397466) (@lem2397465)). Qed.
Lemma lem2397468 : term129 = term88.
Proof. exact (TRANS (@lem2397461) (@lem2397467)). Qed.
Lemma lem2397469 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2397470 : term135 = term136.
Proof. exact (MK_COMB (@lem2397469) (@lem2397468)). Qed.
Lemma lem2397471 : term131 = term94.
Proof. exact (MK_COMB (@lem2397470) (@lem2397458)). Qed.
Lemma lem2397472 : term130 = term94.
Proof. exact (TRANS (@lem2397450) (@lem2397471)). Qed.
Lemma lem2397473 : term129 = term94.
Proof. exact (TRANS (@lem2397449) (@lem2397472)). Qed.
Lemma lem2397475 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2397476 : term94 = term88.
Proof. exact (@lem2397475 term88). Qed.
Lemma lem2397477 : term129 = term88.
Proof. exact (TRANS (@lem2397473) (@lem2397476)). Qed.
Lemma lem2397480 (c : int) : (term114 c) = (term114 c).
Proof. exact (eq_refl (term114 c)). Qed.
Lemma lem2397481 (c : int) : (term127 c) = (term137 c).
Proof. exact (MK_COMB (@lem2397480 c) (@lem2397477)). Qed.
Lemma lem2397482 (c : int) : (term126 c) = (term137 c).
Proof. exact (TRANS (@lem2397440 c) (@lem2397481 c)). Qed.
Lemma lem2397485 (a : int) : (term114 a) = (term114 a).
Proof. exact (eq_refl (term114 a)). Qed.
Lemma lem2397486 (a : int) (c : int) : (term125 a c) = (term138 a c).
Proof. exact (MK_COMB (@lem2397485 a) (@lem2397482 c)). Qed.
Lemma lem2397487 (a : int) (c : int) : (term124 a c) = (term138 a c).
Proof. exact (TRANS (@lem2397439 a c) (@lem2397486 a c)). Qed.
Lemma lem2397488 (b : int) : (term40 b) = (term40 b).
Proof. exact (eq_refl (term40 b)). Qed.
Lemma lem2397489 (b : int) (a : int) (c : int) : (term123 b a c) = (term139 b a c).
Proof. exact (MK_COMB (@lem2397488 b) (@lem2397487 a c)). Qed.
Lemma lem2397494 (a : int) (b : int) (c : int) : (term139 b a c) = (term140 a b c).
Proof. exact (@lem1982757 (term89 a) (real_of_int b) (term137 c)). Qed.
Lemma lem2397495 (a : int) (b : int) (c : int) : (term123 b a c) = (term140 a b c).
Proof. exact (TRANS (@lem2397489 b a c) (@lem2397494 a b c)). Qed.
Lemma lem2397496 (a : int) (b : int) (c : int) : (term122 b a c) = (term140 a b c).
Proof. exact (TRANS (@lem2397438 b a c) (@lem2397495 a b c)). Qed.
Lemma lem2397497 (a : int) (b : int) (c : int) : (term121 b c a) = (term140 a b c).
Proof. exact (TRANS (@lem2397437 b a c) (@lem2397496 a b c)). Qed.
Lemma lem2397498 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2397499 (a : int) (b : int) (c : int) : (term141 b c a) = (term142 a b c).
Proof. exact (MK_COMB (@lem2397498) (@lem2397497 a b c)). Qed.
Lemma lem2397500 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2397501 (a : int) (b : int) (c : int) : (term119 b c a) = (term143 a b c).
Proof. exact (MK_COMB (@lem2397499 a b c) (@lem2397500)). Qed.
Lemma lem2397502 (a : int) (b : int) (c : int) : (term32 c a b) = (term143 a b c).
Proof. exact (TRANS (@lem2397416 b c a) (@lem2397501 a b c)). Qed.
Lemma lem2397503 (c : int) (a : int) (b : int) : (term44 b c a) = (term144 c a b).
Proof. exact (@lem1988287 (term19 c a) (term41 b)). Qed.
Lemma lem2397510 (b : int) : (term41 b) = (term41 b).
Proof. exact (eq_refl (term41 b)). Qed.
Lemma lem2397517 (a : int) (c : int) : (term19 c a) = (term19 a c).
Proof. exact (@lem1982761 (real_of_int a) (real_of_int c)). Qed.
Lemma lem2397518 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2397519 (a : int) (c : int) : (term145 c a) = (term145 a c).
Proof. exact (MK_COMB (@lem2397518) (@lem2397517 a c)). Qed.
Lemma lem2397520 (a : int) (c : int) (b : int) : (term146 c a b) = (term146 a c b).
Proof. exact (MK_COMB (@lem2397519 a c) (@lem2397510 b)). Qed.
Lemma lem2397521 (a : int) (c : int) (b : int) : (term146 a c b) = (term147 a c b).
Proof. exact (@lem1982792 (term19 a c) (term41 b)). Qed.
Lemma lem2397522 (b : int) : (term126 b) = (term127 b).
Proof. exact (@lem1982781 (real_of_int b) term88 term27). Qed.
Lemma lem2397524 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2397525 : term27 = term109.
Proof. exact (@lem2397524 term28). Qed.
Lemma lem2397527 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2397528 : term88 = term94.
Proof. exact (@lem2397527 term28). Qed.
Lemma lem2397529 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2397530 : term95 = term96.
Proof. exact (MK_COMB (@lem2397529) (@lem2397528)). Qed.
Lemma lem2397531 : term129 = term130.
Proof. exact (MK_COMB (@lem2397530) (@lem2397525)). Qed.
Lemma lem2397532 : term130 = term131.
Proof. exact (@lem1981613 term88 term27 term27 term27). Qed.
Lemma lem2397534 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2397535 : term102 = term103.
Proof. exact (@lem2397534 term28 term28). Qed.
Lemma lem2397536 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397537 : term105 = term28.
Proof. exact (EQ_MP (@lem2397536) (@lem940073)). Qed.
Lemma lem2397538 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397539 : term103 = term27.
Proof. exact (MK_COMB (@lem2397538) (@lem2397537)). Qed.
Lemma lem2397540 : term102 = term27.
Proof. exact (TRANS (@lem2397535) (@lem2397539)). Qed.
Lemma lem2397542 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2397543 : term129 = term134.
Proof. exact (@lem2397542 term28 term28). Qed.
Lemma lem2397544 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397545 : term105 = term28.
Proof. exact (EQ_MP (@lem2397544) (@lem940073)). Qed.
Lemma lem2397546 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397547 : term103 = term27.
Proof. exact (MK_COMB (@lem2397546) (@lem2397545)). Qed.
Lemma lem2397548 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2397549 : term134 = term88.
Proof. exact (MK_COMB (@lem2397548) (@lem2397547)). Qed.
Lemma lem2397550 : term129 = term88.
Proof. exact (TRANS (@lem2397543) (@lem2397549)). Qed.
Lemma lem2397551 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2397552 : term135 = term136.
Proof. exact (MK_COMB (@lem2397551) (@lem2397550)). Qed.
Lemma lem2397553 : term131 = term94.
Proof. exact (MK_COMB (@lem2397552) (@lem2397540)). Qed.
Lemma lem2397554 : term130 = term94.
Proof. exact (TRANS (@lem2397532) (@lem2397553)). Qed.
Lemma lem2397555 : term129 = term94.
Proof. exact (TRANS (@lem2397531) (@lem2397554)). Qed.
Lemma lem2397557 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2397558 : term94 = term88.
Proof. exact (@lem2397557 term88). Qed.
Lemma lem2397559 : term129 = term88.
Proof. exact (TRANS (@lem2397555) (@lem2397558)). Qed.
Lemma lem2397562 (b : int) : (term114 b) = (term114 b).
Proof. exact (eq_refl (term114 b)). Qed.
Lemma lem2397563 (b : int) : (term127 b) = (term137 b).
Proof. exact (MK_COMB (@lem2397562 b) (@lem2397559)). Qed.
Lemma lem2397564 (b : int) : (term126 b) = (term137 b).
Proof. exact (TRANS (@lem2397522 b) (@lem2397563 b)). Qed.
Lemma lem2397565 (a : int) (c : int) : (term24 a c) = (term24 a c).
Proof. exact (eq_refl (term24 a c)). Qed.
Lemma lem2397566 (a : int) (c : int) (b : int) : (term147 a c b) = (term148 a c b).
Proof. exact (MK_COMB (@lem2397565 a c) (@lem2397564 b)). Qed.
Lemma lem2397567 (a : int) (c : int) (b : int) : (term148 a c b) = (term149 a c b).
Proof. exact (@lem1982755 (real_of_int a) (real_of_int c) (term137 b)). Qed.
Lemma lem2397572 (b : int) (c : int) : (term150 c b) = (term151 b c).
Proof. exact (@lem1982757 (term89 b) (real_of_int c) term88). Qed.
Lemma lem2397573 (a : int) : (term40 a) = (term40 a).
Proof. exact (eq_refl (term40 a)). Qed.
Lemma lem2397574 (a : int) (b : int) (c : int) : (term149 a c b) = (term152 a b c).
Proof. exact (MK_COMB (@lem2397573 a) (@lem2397572 b c)). Qed.
Lemma lem2397575 (a : int) (b : int) (c : int) : (term148 a c b) = (term152 a b c).
Proof. exact (TRANS (@lem2397567 a c b) (@lem2397574 a b c)). Qed.
Lemma lem2397576 (a : int) (b : int) (c : int) : (term147 a c b) = (term152 a b c).
Proof. exact (TRANS (@lem2397566 a c b) (@lem2397575 a b c)). Qed.
Lemma lem2397577 (a : int) (b : int) (c : int) : (term146 a c b) = (term152 a b c).
Proof. exact (TRANS (@lem2397521 a c b) (@lem2397576 a b c)). Qed.
Lemma lem2397578 (a : int) (b : int) (c : int) : (term146 c a b) = (term152 a b c).
Proof. exact (TRANS (@lem2397520 a c b) (@lem2397577 a b c)). Qed.
Lemma lem2397579 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2397580 (a : int) (b : int) (c : int) : (term153 c a b) = (term154 a b c).
Proof. exact (MK_COMB (@lem2397579) (@lem2397578 a b c)). Qed.
Lemma lem2397581 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2397582 (a : int) (b : int) (c : int) : (term144 c a b) = (term155 a b c).
Proof. exact (MK_COMB (@lem2397580 a b c) (@lem2397581)). Qed.
Lemma lem2397583 (a : int) (b : int) (c : int) : (term44 b c a) = (term155 a b c).
Proof. exact (TRANS (@lem2397503 c a b) (@lem2397582 a b c)). Qed.
Lemma lem2397584 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2397585 (a : int) (b : int) (c : int) : (term34 c a b) = (term156 a b c).
Proof. exact (MK_COMB (@lem2397584) (@lem2397502 a b c)). Qed.
Lemma lem2397586 (a : int) (b : int) (c : int) : (term45 b c a) = (term157 a b c).
Proof. exact (MK_COMB (@lem2397585 a b c) (@lem2397583 a b c)). Qed.
Lemma lem2397587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2397588 (a : int) (b : int) (c : int) : (term47 a b c) = (term158 a b c).
Proof. exact (MK_COMB (@lem2397587) (@lem2397415 a b c)). Qed.
Lemma lem2397589 (a : int) (b : int) (c : int) : (term49 b c a) = (term159 a b c).
Proof. exact (MK_COMB (@lem2397588 a b c) (@lem2397586 a b c)). Qed.
Lemma lem2397590 (b : int) (c : int) (a : int) : (term54 a b c) = (term160 b c a).
Proof. exact (@lem1988287 (term8 b c) (term41 a)). Qed.
Lemma lem2397597 (a : int) : (term41 a) = (term41 a).
Proof. exact (eq_refl (term41 a)). Qed.
Lemma lem2397610 (b : int) (c : int) : (term8 b c) = (term82 b c).
Proof. exact (@lem1982792 (real_of_int b) (real_of_int c)). Qed.
Lemma lem2397611 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2397612 (b : int) (c : int) : (term161 b c) = (term162 b c).
Proof. exact (MK_COMB (@lem2397611) (@lem2397610 b c)). Qed.
Lemma lem2397613 (b : int) (c : int) (a : int) : (term163 b c a) = (term164 b c a).
Proof. exact (MK_COMB (@lem2397612 b c) (@lem2397597 a)). Qed.
Lemma lem2397614 (b : int) (c : int) (a : int) : (term164 b c a) = (term165 b c a).
Proof. exact (@lem1982792 (term82 b c) (term41 a)). Qed.
Lemma lem2397615 (a : int) : (term126 a) = (term127 a).
Proof. exact (@lem1982781 (real_of_int a) term88 term27). Qed.
Lemma lem2397617 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2397618 : term27 = term109.
Proof. exact (@lem2397617 term28). Qed.
Lemma lem2397620 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2397621 : term88 = term94.
Proof. exact (@lem2397620 term28). Qed.
Lemma lem2397622 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2397623 : term95 = term96.
Proof. exact (MK_COMB (@lem2397622) (@lem2397621)). Qed.
Lemma lem2397624 : term129 = term130.
Proof. exact (MK_COMB (@lem2397623) (@lem2397618)). Qed.
Lemma lem2397625 : term130 = term131.
Proof. exact (@lem1981613 term88 term27 term27 term27). Qed.
Lemma lem2397627 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2397628 : term102 = term103.
Proof. exact (@lem2397627 term28 term28). Qed.
Lemma lem2397629 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397630 : term105 = term28.
Proof. exact (EQ_MP (@lem2397629) (@lem940073)). Qed.
Lemma lem2397631 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397632 : term103 = term27.
Proof. exact (MK_COMB (@lem2397631) (@lem2397630)). Qed.
Lemma lem2397633 : term102 = term27.
Proof. exact (TRANS (@lem2397628) (@lem2397632)). Qed.
Lemma lem2397635 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2397636 : term129 = term134.
Proof. exact (@lem2397635 term28 term28). Qed.
Lemma lem2397637 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397638 : term105 = term28.
Proof. exact (EQ_MP (@lem2397637) (@lem940073)). Qed.
Lemma lem2397639 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397640 : term103 = term27.
Proof. exact (MK_COMB (@lem2397639) (@lem2397638)). Qed.
Lemma lem2397641 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2397642 : term134 = term88.
Proof. exact (MK_COMB (@lem2397641) (@lem2397640)). Qed.
Lemma lem2397643 : term129 = term88.
Proof. exact (TRANS (@lem2397636) (@lem2397642)). Qed.
Lemma lem2397644 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2397645 : term135 = term136.
Proof. exact (MK_COMB (@lem2397644) (@lem2397643)). Qed.
Lemma lem2397646 : term131 = term94.
Proof. exact (MK_COMB (@lem2397645) (@lem2397633)). Qed.
Lemma lem2397647 : term130 = term94.
Proof. exact (TRANS (@lem2397625) (@lem2397646)). Qed.
Lemma lem2397648 : term129 = term94.
Proof. exact (TRANS (@lem2397624) (@lem2397647)). Qed.
Lemma lem2397650 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2397651 : term94 = term88.
Proof. exact (@lem2397650 term88). Qed.
Lemma lem2397652 : term129 = term88.
Proof. exact (TRANS (@lem2397648) (@lem2397651)). Qed.
Lemma lem2397655 (a : int) : (term114 a) = (term114 a).
Proof. exact (eq_refl (term114 a)). Qed.
Lemma lem2397656 (a : int) : (term127 a) = (term137 a).
Proof. exact (MK_COMB (@lem2397655 a) (@lem2397652)). Qed.
Lemma lem2397657 (a : int) : (term126 a) = (term137 a).
Proof. exact (TRANS (@lem2397615 a) (@lem2397656 a)). Qed.
Lemma lem2397658 (b : int) (c : int) : (term166 b c) = (term166 b c).
Proof. exact (eq_refl (term166 b c)). Qed.
Lemma lem2397659 (b : int) (c : int) (a : int) : (term165 b c a) = (term167 b c a).
Proof. exact (MK_COMB (@lem2397658 b c) (@lem2397657 a)). Qed.
Lemma lem2397660 (a : int) (b : int) (c : int) : (term167 b c a) = (term168 a b c).
Proof. exact (@lem1982757 (term89 a) (term82 b c) term88). Qed.
Lemma lem2397665 (b : int) (c : int) : (term169 b c) = (term150 b c).
Proof. exact (@lem1982755 (real_of_int b) (term89 c) term88). Qed.
Lemma lem2397666 (a : int) : (term114 a) = (term114 a).
Proof. exact (eq_refl (term114 a)). Qed.
Lemma lem2397667 (a : int) (b : int) (c : int) : (term168 a b c) = (term140 a b c).
Proof. exact (MK_COMB (@lem2397666 a) (@lem2397665 b c)). Qed.
Lemma lem2397668 (a : int) (b : int) (c : int) : (term167 b c a) = (term140 a b c).
Proof. exact (TRANS (@lem2397660 a b c) (@lem2397667 a b c)). Qed.
Lemma lem2397669 (a : int) (b : int) (c : int) : (term165 b c a) = (term140 a b c).
Proof. exact (TRANS (@lem2397659 b c a) (@lem2397668 a b c)). Qed.
Lemma lem2397670 (a : int) (b : int) (c : int) : (term164 b c a) = (term140 a b c).
Proof. exact (TRANS (@lem2397614 b c a) (@lem2397669 a b c)). Qed.
Lemma lem2397671 (a : int) (b : int) (c : int) : (term163 b c a) = (term140 a b c).
Proof. exact (TRANS (@lem2397613 b c a) (@lem2397670 a b c)). Qed.
Lemma lem2397672 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2397673 (a : int) (b : int) (c : int) : (term170 b c a) = (term142 a b c).
Proof. exact (MK_COMB (@lem2397672) (@lem2397671 a b c)). Qed.
Lemma lem2397674 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2397675 (a : int) (b : int) (c : int) : (term160 b c a) = (term143 a b c).
Proof. exact (MK_COMB (@lem2397673 a b c) (@lem2397674)). Qed.
Lemma lem2397676 (a : int) (b : int) (c : int) : (term54 a b c) = (term143 a b c).
Proof. exact (TRANS (@lem2397590 b c a) (@lem2397675 a b c)). Qed.
Lemma lem2397677 (a : int) (b : int) (c : int) : (term67 b c a) = (term171 a b c).
Proof. exact (@lem1988287 (real_of_int a) (term64 b c)). Qed.
Lemma lem2397678 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2397691 (b : int) (c : int) : (term8 b c) = (term82 b c).
Proof. exact (@lem1982792 (real_of_int b) (real_of_int c)). Qed.
Lemma lem2397692 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2397693 (b : int) (c : int) : (term63 b c) = (term166 b c).
Proof. exact (MK_COMB (@lem2397692) (@lem2397691 b c)). Qed.
Lemma lem2397694 (b : int) (c : int) : (term64 b c) = (term172 b c).
Proof. exact (MK_COMB (@lem2397693 b c) (@lem2397678)). Qed.
Lemma lem2397699 (b : int) (c : int) : (term172 b c) = (term173 b c).
Proof. exact (@lem1982755 (real_of_int b) (term89 c) term27). Qed.
Lemma lem2397700 (b : int) (c : int) : (term64 b c) = (term173 b c).
Proof. exact (TRANS (@lem2397694 b c) (@lem2397699 b c)). Qed.
Lemma lem2397703 (a : int) : (term83 a) = (term83 a).
Proof. exact (eq_refl (term83 a)). Qed.
Lemma lem2397704 (a : int) (b : int) (c : int) : (term174 a b c) = (term175 a b c).
Proof. exact (MK_COMB (@lem2397703 a) (@lem2397700 b c)). Qed.
Lemma lem2397705 (a : int) (b : int) (c : int) : (term175 a b c) = (term176 a b c).
Proof. exact (@lem1982792 (real_of_int a) (term173 b c)). Qed.
Lemma lem2397706 (b : int) (c : int) : (term177 b c) = (term178 b c).
Proof. exact (@lem1982781 (real_of_int b) term88 (term179 c)). Qed.
Lemma lem2397707 (c : int) : (term180 c) = (term181 c).
Proof. exact (@lem1982781 (term89 c) term88 term27). Qed.
Lemma lem2397709 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2397710 : term27 = term109.
Proof. exact (@lem2397709 term28). Qed.
Lemma lem2397712 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2397713 : term88 = term94.
Proof. exact (@lem2397712 term28). Qed.
Lemma lem2397714 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2397715 : term95 = term96.
Proof. exact (MK_COMB (@lem2397714) (@lem2397713)). Qed.
Lemma lem2397716 : term129 = term130.
Proof. exact (MK_COMB (@lem2397715) (@lem2397710)). Qed.
Lemma lem2397717 : term130 = term131.
Proof. exact (@lem1981613 term88 term27 term27 term27). Qed.
Lemma lem2397719 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2397720 : term102 = term103.
Proof. exact (@lem2397719 term28 term28). Qed.
Lemma lem2397721 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397722 : term105 = term28.
Proof. exact (EQ_MP (@lem2397721) (@lem940073)). Qed.
Lemma lem2397723 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397724 : term103 = term27.
Proof. exact (MK_COMB (@lem2397723) (@lem2397722)). Qed.
Lemma lem2397725 : term102 = term27.
Proof. exact (TRANS (@lem2397720) (@lem2397724)). Qed.
Lemma lem2397727 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2397728 : term129 = term134.
Proof. exact (@lem2397727 term28 term28). Qed.
Lemma lem2397729 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397730 : term105 = term28.
Proof. exact (EQ_MP (@lem2397729) (@lem940073)). Qed.
Lemma lem2397731 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397732 : term103 = term27.
Proof. exact (MK_COMB (@lem2397731) (@lem2397730)). Qed.
Lemma lem2397733 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2397734 : term134 = term88.
Proof. exact (MK_COMB (@lem2397733) (@lem2397732)). Qed.
Lemma lem2397735 : term129 = term88.
Proof. exact (TRANS (@lem2397728) (@lem2397734)). Qed.
Lemma lem2397736 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2397737 : term135 = term136.
Proof. exact (MK_COMB (@lem2397736) (@lem2397735)). Qed.
Lemma lem2397738 : term131 = term94.
Proof. exact (MK_COMB (@lem2397737) (@lem2397725)). Qed.
Lemma lem2397739 : term130 = term94.
Proof. exact (TRANS (@lem2397717) (@lem2397738)). Qed.
Lemma lem2397740 : term129 = term94.
Proof. exact (TRANS (@lem2397716) (@lem2397739)). Qed.
Lemma lem2397742 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2397743 : term94 = term88.
Proof. exact (@lem2397742 term88). Qed.
Lemma lem2397744 : term129 = term88.
Proof. exact (TRANS (@lem2397740) (@lem2397743)). Qed.
Lemma lem2397745 (c : int) : (term90 c) = (term91 c).
Proof. exact (@lem1982749 term88 term88 (real_of_int c)). Qed.
Lemma lem2397747 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2397748 : term88 = term94.
Proof. exact (@lem2397747 term28). Qed.
Lemma lem2397750 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2397751 : term88 = term94.
Proof. exact (@lem2397750 term28). Qed.
Lemma lem2397752 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2397753 : term95 = term96.
Proof. exact (MK_COMB (@lem2397752) (@lem2397751)). Qed.
Lemma lem2397754 : term97 = term98.
Proof. exact (MK_COMB (@lem2397753) (@lem2397748)). Qed.
Lemma lem2397755 : term98 = term99.
Proof. exact (@lem1981613 term88 term88 term27 term27). Qed.
Lemma lem2397757 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2397758 : term102 = term103.
Proof. exact (@lem2397757 term28 term28). Qed.
Lemma lem2397759 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397760 : term105 = term28.
Proof. exact (EQ_MP (@lem2397759) (@lem940073)). Qed.
Lemma lem2397761 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397762 : term103 = term27.
Proof. exact (MK_COMB (@lem2397761) (@lem2397760)). Qed.
Lemma lem2397763 : term102 = term27.
Proof. exact (TRANS (@lem2397758) (@lem2397762)). Qed.
Lemma lem2397765 (m : nat) (n : nat) : (term106 m n) = (term101 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2397766 : term97 = term103.
Proof. exact (@lem2397765 term28 term28). Qed.
Lemma lem2397767 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397768 : term105 = term28.
Proof. exact (EQ_MP (@lem2397767) (@lem940073)). Qed.
Lemma lem2397769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397770 : term103 = term27.
Proof. exact (MK_COMB (@lem2397769) (@lem2397768)). Qed.
Lemma lem2397771 : term97 = term27.
Proof. exact (TRANS (@lem2397766) (@lem2397770)). Qed.
Lemma lem2397772 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2397773 : term107 = term108.
Proof. exact (MK_COMB (@lem2397772) (@lem2397771)). Qed.
Lemma lem2397774 : term99 = term109.
Proof. exact (MK_COMB (@lem2397773) (@lem2397763)). Qed.
Lemma lem2397775 : term98 = term109.
Proof. exact (TRANS (@lem2397755) (@lem2397774)). Qed.
Lemma lem2397776 : term97 = term109.
Proof. exact (TRANS (@lem2397754) (@lem2397775)). Qed.
Lemma lem2397778 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2397779 : term109 = term27.
Proof. exact (@lem2397778 term27). Qed.
Lemma lem2397780 : term97 = term27.
Proof. exact (TRANS (@lem2397776) (@lem2397779)). Qed.
Lemma lem2397781 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2397782 : term111 = term112.
Proof. exact (MK_COMB (@lem2397781) (@lem2397780)). Qed.
Lemma lem2397783 (c : int) : (real_of_int c) = (real_of_int c).
Proof. exact (eq_refl (real_of_int c)). Qed.
Lemma lem2397784 (c : int) : (term91 c) = (term113 c).
Proof. exact (MK_COMB (@lem2397782) (@lem2397783 c)). Qed.
Lemma lem2397785 (c : int) : (term90 c) = (term113 c).
Proof. exact (TRANS (@lem2397745 c) (@lem2397784 c)). Qed.
Lemma lem2397786 (c : int) : (term113 c) = (real_of_int c).
Proof. exact (@lem1982709 (real_of_int c)). Qed.
Lemma lem2397787 (c : int) : (term90 c) = (real_of_int c).
Proof. exact (TRANS (@lem2397785 c) (@lem2397786 c)). Qed.
Lemma lem2397788 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2397789 (c : int) : (term182 c) = (term40 c).
Proof. exact (MK_COMB (@lem2397788) (@lem2397787 c)). Qed.
Lemma lem2397790 (c : int) : (term181 c) = (term183 c).
Proof. exact (MK_COMB (@lem2397789 c) (@lem2397744)). Qed.
Lemma lem2397791 (c : int) : (term180 c) = (term183 c).
Proof. exact (TRANS (@lem2397707 c) (@lem2397790 c)). Qed.
Lemma lem2397794 (b : int) : (term114 b) = (term114 b).
Proof. exact (eq_refl (term114 b)). Qed.
Lemma lem2397795 (b : int) (c : int) : (term178 b c) = (term151 b c).
Proof. exact (MK_COMB (@lem2397794 b) (@lem2397791 c)). Qed.
Lemma lem2397796 (b : int) (c : int) : (term177 b c) = (term151 b c).
Proof. exact (TRANS (@lem2397706 b c) (@lem2397795 b c)). Qed.
Lemma lem2397797 (a : int) : (term40 a) = (term40 a).
Proof. exact (eq_refl (term40 a)). Qed.
Lemma lem2397800 (a : int) (b : int) (c : int) : (term176 a b c) = (term152 a b c).
Proof. exact (MK_COMB (@lem2397797 a) (@lem2397796 b c)). Qed.
Lemma lem2397801 (a : int) (b : int) (c : int) : (term175 a b c) = (term152 a b c).
Proof. exact (TRANS (@lem2397705 a b c) (@lem2397800 a b c)). Qed.
Lemma lem2397802 (a : int) (b : int) (c : int) : (term174 a b c) = (term152 a b c).
Proof. exact (TRANS (@lem2397704 a b c) (@lem2397801 a b c)). Qed.
Lemma lem2397803 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2397804 (a : int) (b : int) (c : int) : (term184 a b c) = (term154 a b c).
Proof. exact (MK_COMB (@lem2397803) (@lem2397802 a b c)). Qed.
Lemma lem2397805 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2397806 (a : int) (b : int) (c : int) : (term171 a b c) = (term155 a b c).
Proof. exact (MK_COMB (@lem2397804 a b c) (@lem2397805)). Qed.
Lemma lem2397807 (a : int) (b : int) (c : int) : (term67 b c a) = (term155 a b c).
Proof. exact (TRANS (@lem2397677 a b c) (@lem2397806 a b c)). Qed.
Lemma lem2397808 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2397809 (a : int) (b : int) (c : int) : (term56 a b c) = (term156 a b c).
Proof. exact (MK_COMB (@lem2397808) (@lem2397676 a b c)). Qed.
Lemma lem2397810 (a : int) (b : int) (c : int) : (term68 b c a) = (term157 a b c).
Proof. exact (MK_COMB (@lem2397809 a b c) (@lem2397807 a b c)). Qed.
Lemma lem2397811 (c : int) (a : int) (b : int) : ((term19 c a) = (real_of_int b)) = ((term185 c a b) = term81).
Proof. exact (@lem1988293 (term19 c a) (real_of_int b)). Qed.
Lemma lem2397812 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2397819 (a : int) (c : int) : (term19 c a) = (term19 a c).
Proof. exact (@lem1982761 (real_of_int a) (real_of_int c)). Qed.
Lemma lem2397820 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2397821 (a : int) (c : int) : (term145 c a) = (term145 a c).
Proof. exact (MK_COMB (@lem2397820) (@lem2397819 a c)). Qed.
Lemma lem2397822 (a : int) (c : int) (b : int) : (term185 c a b) = (term185 a c b).
Proof. exact (MK_COMB (@lem2397821 a c) (@lem2397812 b)). Qed.
Lemma lem2397823 (a : int) (c : int) (b : int) : (term185 a c b) = (term186 a c b).
Proof. exact (@lem1982792 (term19 a c) (real_of_int b)). Qed.
Lemma lem2397827 (a : int) (c : int) (b : int) : (term186 a c b) = (term187 a c b).
Proof. exact (@lem1982755 (real_of_int a) (real_of_int c) (term89 b)). Qed.
Lemma lem2397828 (b : int) (c : int) : (term82 c b) = (term115 b c).
Proof. exact (@lem1982761 (term89 b) (real_of_int c)). Qed.
Lemma lem2397829 (a : int) : (term40 a) = (term40 a).
Proof. exact (eq_refl (term40 a)). Qed.
Lemma lem2397830 (a : int) (b : int) (c : int) : (term187 a c b) = (term116 a b c).
Proof. exact (MK_COMB (@lem2397829 a) (@lem2397828 b c)). Qed.
Lemma lem2397832 (a : int) (b : int) (c : int) : (term186 a c b) = (term116 a b c).
Proof. exact (TRANS (@lem2397827 a c b) (@lem2397830 a b c)). Qed.
Lemma lem2397833 (a : int) (b : int) (c : int) : (term185 a c b) = (term116 a b c).
Proof. exact (TRANS (@lem2397823 a c b) (@lem2397832 a b c)). Qed.
Lemma lem2397834 (a : int) (b : int) (c : int) : (term185 c a b) = (term116 a b c).
Proof. exact (TRANS (@lem2397822 a c b) (@lem2397833 a b c)). Qed.
Lemma lem2397835 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2397836 (a : int) (b : int) (c : int) : (term188 c a b) = (term118 a b c).
Proof. exact (MK_COMB (@lem2397835) (@lem2397834 a b c)). Qed.
Lemma lem2397837 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2397838 (a : int) (b : int) (c : int) : ((term185 c a b) = term81) = ((term116 a b c) = term81).
Proof. exact (MK_COMB (@lem2397836 a b c) (@lem2397837)). Qed.
Lemma lem2397839 (a : int) (b : int) (c : int) : ((term19 c a) = (real_of_int b)) = ((term116 a b c) = term81).
Proof. exact (TRANS (@lem2397811 c a b) (@lem2397838 a b c)). Qed.
Lemma lem2397840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2397841 (a : int) (b : int) (c : int) : (term72 b c a) = (term189 a b c).
Proof. exact (MK_COMB (@lem2397840) (@lem2397810 a b c)). Qed.
Lemma lem2397842 (a : int) (b : int) (c : int) : (term74 c a b) = (term190 a b c).
Proof. exact (MK_COMB (@lem2397841 a b c) (@lem2397839 a b c)). Qed.
Lemma lem2397843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2397844 (a : int) (b : int) (c : int) : (term76 b c a) = (term191 a b c).
Proof. exact (MK_COMB (@lem2397843) (@lem2397589 a b c)). Qed.
Lemma lem2397845 (a : int) (b : int) (c : int) : (term77 c a b) = (term192 a b c).
Proof. exact (MK_COMB (@lem2397844 a b c) (@lem2397842 a b c)). Qed.
Lemma lem2397852 (a : int) (b : int) (c : int) : (term79 c a b) = (term192 a b c).
Proof. exact (TRANS (@lem2397336 c a b) (@lem2397845 a b c)). Qed.
Lemma lem2397869 (a : int) (b : int) (c : int) : (term190 a b c) = (term193 a b c).
Proof. exact (@lem19367 (term143 a b c) (term155 a b c) ((term116 a b c) = term81)). Qed.
Lemma lem2397886 (a : int) (b : int) (c : int) : (term159 a b c) = (term194 a b c).
Proof. exact (@lem19158 (term143 a b c) ((term116 a b c) = term81) (term155 a b c)). Qed.
Lemma lem2397887 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2397888 (a : int) (b : int) (c : int) : (term191 a b c) = (term195 a b c).
Proof. exact (MK_COMB (@lem2397887) (@lem2397886 a b c)). Qed.
Lemma lem2397889 (a : int) (b : int) (c : int) : (term192 a b c) = (term196 a b c).
Proof. exact (MK_COMB (@lem2397888 a b c) (@lem2397869 a b c)). Qed.
Lemma lem2397890 (a : int) (b : int) (c : int) : (term79 c a b) = (term196 a b c).
Proof. exact (TRANS (@lem2397852 a b c) (@lem2397889 a b c)). Qed.
Lemma lem2397912 (a : int) (b : int) (c : int) (h1 : term196 a b c) : term196 a b c.
Proof. exact (h1). Qed.
Lemma lem2397913 (a : int) (b : int) (c : int) (h1 : term194 a b c) : term194 a b c.
Proof. exact (h1). Qed.
Lemma lem2397914 (a : int) (b : int) (c : int) (h1 : term197 a b c) : term197 a b c.
Proof. exact (h1). Qed.
Lemma lem2397915 (a : int) (b : int) (c : int) (h1 : term197 a b c) : term143 a b c.
Proof. exact (proj2 (@lem2397914 a b c h1)). Qed.
Lemma lem2397916 (a : int) (b : int) (c : int) (h1 : term197 a b c) : (term116 a b c) = term81.
Proof. exact (proj1 (@lem2397914 a b c h1)). Qed.
Lemma lem2397918 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2397919 : term198 = term199.
Proof. exact (@lem2397918 term81 term27). Qed.
Lemma lem2397921 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2397922 : term27 = term109.
Proof. exact (@lem2397921 term28). Qed.
Lemma lem2397924 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2397925 : term81 = term200.
Proof. exact (@lem2397924 (NUMERAL 0)). Qed.
Lemma lem2397926 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2397927 : term201 = term202.
Proof. exact (MK_COMB (@lem2397926) (@lem2397925)). Qed.
Lemma lem2397928 : term199 = term203.
Proof. exact (MK_COMB (@lem2397927) (@lem2397922)). Qed.
Lemma lem2397929 : term204.
Proof. exact (@lem1980255 term81 term27 term27 term27). Qed.
Lemma lem2397931 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2397932 : term199 = term206.
Proof. exact (@lem2397931 (NUMERAL 0) term28). Qed.
Lemma lem2397933 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2397934 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2397935 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2397934 h1) (fun h1 : term206 = True => @lem2397933)). Qed.
Lemma lem2397936 : term206 = True.
Proof. exact (EQ_MP (@lem2397935) (@lem2397933)). Qed.
Lemma lem2397937 : term199 = True.
Proof. exact (TRANS (@lem2397932) (@lem2397936)). Qed.
Lemma lem2397938 : True = term199.
Proof. exact (SYM (@lem2397937)). Qed.
Lemma lem2397939 : term199.
Proof. exact (EQ_MP (@lem2397938) (@lem0)). Qed.
Lemma lem2397940 : term208.
Proof. exact (@lem2397929 (@lem2397939)). Qed.
Lemma lem2397942 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2397943 : term199 = term206.
Proof. exact (@lem2397942 (NUMERAL 0) term28). Qed.
Lemma lem2397944 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2397945 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2397946 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2397945 h1) (fun h1 : term206 = True => @lem2397944)). Qed.
Lemma lem2397947 : term206 = True.
Proof. exact (EQ_MP (@lem2397946) (@lem2397944)). Qed.
Lemma lem2397948 : term199 = True.
Proof. exact (TRANS (@lem2397943) (@lem2397947)). Qed.
Lemma lem2397949 : True = term199.
Proof. exact (SYM (@lem2397948)). Qed.
Lemma lem2397950 : term199.
Proof. exact (EQ_MP (@lem2397949) (@lem0)). Qed.
Lemma lem2397951 : term203 = term209.
Proof. exact (@lem2397940 (@lem2397950)). Qed.
Lemma lem2397953 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2397954 : term102 = term103.
Proof. exact (@lem2397953 term28 term28). Qed.
Lemma lem2397955 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2397956 : term105 = term28.
Proof. exact (EQ_MP (@lem2397955) (@lem940073)). Qed.
Lemma lem2397957 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2397958 : term103 = term27.
Proof. exact (MK_COMB (@lem2397957) (@lem2397956)). Qed.
Lemma lem2397959 : term102 = term27.
Proof. exact (TRANS (@lem2397954) (@lem2397958)). Qed.
Lemma lem2397961 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2397962 : term211 = term81.
Proof. exact (@lem2397961 term28). Qed.
Lemma lem2397963 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2397964 : term212 = term201.
Proof. exact (MK_COMB (@lem2397963) (@lem2397962)). Qed.
Lemma lem2397965 : term209 = term199.
Proof. exact (MK_COMB (@lem2397964) (@lem2397959)). Qed.
Lemma lem2397967 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2397968 : term199 = term206.
Proof. exact (@lem2397967 (NUMERAL 0) term28). Qed.
Lemma lem2397969 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2397970 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2397971 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2397970 h1) (fun h1 : term206 = True => @lem2397969)). Qed.
Lemma lem2397972 : term206 = True.
Proof. exact (EQ_MP (@lem2397971) (@lem2397969)). Qed.
Lemma lem2397973 : term199 = True.
Proof. exact (TRANS (@lem2397968) (@lem2397972)). Qed.
Lemma lem2397974 : term209 = True.
Proof. exact (TRANS (@lem2397965) (@lem2397973)). Qed.
Lemma lem2397975 : term203 = True.
Proof. exact (TRANS (@lem2397951) (@lem2397974)). Qed.
Lemma lem2397976 : term199 = True.
Proof. exact (TRANS (@lem2397928) (@lem2397975)). Qed.
Lemma lem2397977 : term198 = True.
Proof. exact (TRANS (@lem2397919) (@lem2397976)). Qed.
Lemma lem2397978 : True = term198.
Proof. exact (SYM (@lem2397977)). Qed.
Lemma lem2397979 : term198.
Proof. exact (EQ_MP (@lem2397978) (@lem0)). Qed.
Lemma lem2397980 (a : int) (b : int) (c : int) (h1 : term197 a b c) : term213 a b c.
Proof. exact (conj (@lem2397979) (@lem2397915 a b c h1)). Qed.
Lemma lem2397982 (x : real) (y : real) : term214 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2397983 (a : int) (b : int) (c : int) : term215 a b c.
Proof. exact (@lem2397982 term27 (term140 a b c)). Qed.
Lemma lem2397984 (a : int) (b : int) (c : int) (h1 : term197 a b c) : term216 a b c.
Proof. exact (@lem2397983 a b c (@lem2397980 a b c h1)). Qed.
Lemma lem2397985 (a : int) (b : int) (c : int) : (term217 a b c) = (term140 a b c).
Proof. exact (@lem1982733 (term140 a b c)). Qed.
Lemma lem2397986 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2397987 (a : int) (b : int) (c : int) : (term218 a b c) = (term142 a b c).
Proof. exact (MK_COMB (@lem2397986) (@lem2397985 a b c)). Qed.
Lemma lem2397988 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2397989 (a : int) (b : int) (c : int) : (term216 a b c) = (term143 a b c).
Proof. exact (MK_COMB (@lem2397987 a b c) (@lem2397988)). Qed.
Lemma lem2397990 (a : int) (b : int) (c : int) (h1 : term197 a b c) : term143 a b c.
Proof. exact (EQ_MP (@lem2397989 a b c) (@lem2397984 a b c h1)). Qed.
Lemma lem2397992 (y : real) : term219 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2397993 (a : int) (b : int) (c : int) : term220 a b c.
Proof. exact (@lem2397992 (term116 a b c)). Qed.
Lemma lem2397994 (a : int) (b : int) (c : int) (h1 : term197 a b c) : term221 a b c.
Proof. exact (@lem2397993 a b c (@lem2397916 a b c h1)). Qed.
Lemma lem2397995 (a : int) (b : int) (c : int) (h1 : term197 a b c) : term222 a b c.
Proof. exact (@lem2397994 a b c h1 term27). Qed.
Lemma lem2397996 (a : int) (b : int) (c : int) : (term222 a b c) = ((term223 a b c) = term81).
Proof. exact (eq_refl (term222 a b c)). Qed.
Lemma lem2397997 (a : int) (b : int) (c : int) (h1 : term197 a b c) : (term223 a b c) = term81.
Proof. exact (EQ_MP (@lem2397996 a b c) (@lem2397995 a b c h1)). Qed.
Lemma lem2397998 (a : int) (b : int) (c : int) : (term223 a b c) = (term116 a b c).
Proof. exact (@lem1982733 (term116 a b c)). Qed.
Lemma lem2397999 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2398000 (a : int) (b : int) (c : int) : (term224 a b c) = (term118 a b c).
Proof. exact (MK_COMB (@lem2397999) (@lem2397998 a b c)). Qed.
Lemma lem2398001 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2398002 (a : int) (b : int) (c : int) : ((term223 a b c) = term81) = ((term116 a b c) = term81).
Proof. exact (MK_COMB (@lem2398000 a b c) (@lem2398001)). Qed.
Lemma lem2398003 (a : int) (b : int) (c : int) (h1 : term197 a b c) : (term116 a b c) = term81.
Proof. exact (EQ_MP (@lem2398002 a b c) (@lem2397997 a b c h1)). Qed.
Lemma lem2398004 (a : int) (b : int) (c : int) (h1 : term197 a b c) : term197 a b c.
Proof. exact (conj (@lem2398003 a b c h1) (@lem2397990 a b c h1)). Qed.
Lemma lem2398006 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2398007 (a : int) (b : int) (c : int) : term226 a b c.
Proof. exact (@lem2398006 (term116 a b c) (term140 a b c)). Qed.
Lemma lem2398008 (a : int) (b : int) (c : int) (h1 : term197 a b c) : term227 a b c.
Proof. exact (@lem2398007 a b c (@lem2398004 a b c h1)). Qed.
Lemma lem2398009 (a : int) (b : int) (c : int) : (term228 a b c) = (term229 a b c).
Proof. exact (@lem1982753 (real_of_int a) (term89 a) (term115 b c) (term150 b c)). Qed.
Lemma lem2398010 (a : int) : (term230 a) = (term231 a).
Proof. exact (@lem1982715 term88 (real_of_int a)). Qed.
Lemma lem2398012 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2398013 : term27 = term109.
Proof. exact (@lem2398012 term28). Qed.
Lemma lem2398015 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2398016 : term88 = term94.
Proof. exact (@lem2398015 term28). Qed.
Lemma lem2398017 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398018 : term232 = term233.
Proof. exact (MK_COMB (@lem2398017) (@lem2398016)). Qed.
Lemma lem2398019 : term234 = term235.
Proof. exact (MK_COMB (@lem2398018) (@lem2398013)). Qed.
Lemma lem2398020 : term236.
Proof. exact (@lem1981473 term88 term27 term27 term27 term81 term27). Qed.
Lemma lem2398022 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398023 : term199 = term206.
Proof. exact (@lem2398022 (NUMERAL 0) term28). Qed.
Lemma lem2398024 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398025 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398026 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398025 h1) (fun h1 : term206 = True => @lem2398024)). Qed.
Lemma lem2398027 : term206 = True.
Proof. exact (EQ_MP (@lem2398026) (@lem2398024)). Qed.
Lemma lem2398028 : term199 = True.
Proof. exact (TRANS (@lem2398023) (@lem2398027)). Qed.
Lemma lem2398029 : True = term199.
Proof. exact (SYM (@lem2398028)). Qed.
Lemma lem2398030 : term199.
Proof. exact (EQ_MP (@lem2398029) (@lem0)). Qed.
Lemma lem2398031 : term237.
Proof. exact (@lem2398020 (@lem2398030)). Qed.
Lemma lem2398033 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398034 : term199 = term206.
Proof. exact (@lem2398033 (NUMERAL 0) term28). Qed.
Lemma lem2398035 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398036 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398037 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398036 h1) (fun h1 : term206 = True => @lem2398035)). Qed.
Lemma lem2398038 : term206 = True.
Proof. exact (EQ_MP (@lem2398037) (@lem2398035)). Qed.
Lemma lem2398039 : term199 = True.
Proof. exact (TRANS (@lem2398034) (@lem2398038)). Qed.
Lemma lem2398040 : True = term199.
Proof. exact (SYM (@lem2398039)). Qed.
Lemma lem2398041 : term199.
Proof. exact (EQ_MP (@lem2398040) (@lem0)). Qed.
Lemma lem2398042 : term238.
Proof. exact (@lem2398031 (@lem2398041)). Qed.
Lemma lem2398044 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398045 : term199 = term206.
Proof. exact (@lem2398044 (NUMERAL 0) term28). Qed.
Lemma lem2398046 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398047 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398048 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398047 h1) (fun h1 : term206 = True => @lem2398046)). Qed.
Lemma lem2398049 : term206 = True.
Proof. exact (EQ_MP (@lem2398048) (@lem2398046)). Qed.
Lemma lem2398050 : term199 = True.
Proof. exact (TRANS (@lem2398045) (@lem2398049)). Qed.
Lemma lem2398051 : True = term199.
Proof. exact (SYM (@lem2398050)). Qed.
Lemma lem2398052 : term199.
Proof. exact (EQ_MP (@lem2398051) (@lem0)). Qed.
Lemma lem2398053 : term239.
Proof. exact (@lem2398042 (@lem2398052)). Qed.
Lemma lem2398055 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398056 : term102 = term103.
Proof. exact (@lem2398055 term28 term28). Qed.
Lemma lem2398057 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398058 : term105 = term28.
Proof. exact (EQ_MP (@lem2398057) (@lem940073)). Qed.
Lemma lem2398059 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398060 : term103 = term27.
Proof. exact (MK_COMB (@lem2398059) (@lem2398058)). Qed.
Lemma lem2398061 : term102 = term27.
Proof. exact (TRANS (@lem2398056) (@lem2398060)). Qed.
Lemma lem2398063 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2398064 : term129 = term134.
Proof. exact (@lem2398063 term28 term28). Qed.
Lemma lem2398065 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398066 : term105 = term28.
Proof. exact (EQ_MP (@lem2398065) (@lem940073)). Qed.
Lemma lem2398067 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398068 : term103 = term27.
Proof. exact (MK_COMB (@lem2398067) (@lem2398066)). Qed.
Lemma lem2398069 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2398070 : term134 = term88.
Proof. exact (MK_COMB (@lem2398069) (@lem2398068)). Qed.
Lemma lem2398071 : term129 = term88.
Proof. exact (TRANS (@lem2398064) (@lem2398070)). Qed.
Lemma lem2398072 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398073 : term240 = term232.
Proof. exact (MK_COMB (@lem2398072) (@lem2398071)). Qed.
Lemma lem2398074 : term241 = term234.
Proof. exact (MK_COMB (@lem2398073) (@lem2398061)). Qed.
Lemma lem2398076 (m : nat) : (term242 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2398077 : term234 = term81.
Proof. exact (@lem2398076 term28). Qed.
Lemma lem2398078 : term241 = term81.
Proof. exact (TRANS (@lem2398074) (@lem2398077)). Qed.
Lemma lem2398079 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398080 : term243 = term244.
Proof. exact (MK_COMB (@lem2398079) (@lem2398078)). Qed.
Lemma lem2398081 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2398082 : term245 = term211.
Proof. exact (MK_COMB (@lem2398080) (@lem2398081)). Qed.
Lemma lem2398084 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398085 : term211 = term81.
Proof. exact (@lem2398084 term28). Qed.
Lemma lem2398086 : term245 = term81.
Proof. exact (TRANS (@lem2398082) (@lem2398085)). Qed.
Lemma lem2398088 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398089 : term102 = term103.
Proof. exact (@lem2398088 term28 term28). Qed.
Lemma lem2398090 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398091 : term105 = term28.
Proof. exact (EQ_MP (@lem2398090) (@lem940073)). Qed.
Lemma lem2398092 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398093 : term103 = term27.
Proof. exact (MK_COMB (@lem2398092) (@lem2398091)). Qed.
Lemma lem2398094 : term102 = term27.
Proof. exact (TRANS (@lem2398089) (@lem2398093)). Qed.
Lemma lem2398095 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem2398096 : term246 = term211.
Proof. exact (MK_COMB (@lem2398095) (@lem2398094)). Qed.
Lemma lem2398098 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398099 : term211 = term81.
Proof. exact (@lem2398098 term28). Qed.
Lemma lem2398100 : term246 = term81.
Proof. exact (TRANS (@lem2398096) (@lem2398099)). Qed.
Lemma lem2398101 : term81 = term246.
Proof. exact (SYM (@lem2398100)). Qed.
Lemma lem2398102 : term245 = term246.
Proof. exact (TRANS (@lem2398086) (@lem2398101)). Qed.
Lemma lem2398103 : term235 = term200.
Proof. exact (@lem2398053 (@lem2398102)). Qed.
Lemma lem2398104 : term234 = term200.
Proof. exact (TRANS (@lem2398019) (@lem2398103)). Qed.
Lemma lem2398106 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2398107 : term200 = term81.
Proof. exact (@lem2398106 term81). Qed.
Lemma lem2398108 : term234 = term81.
Proof. exact (TRANS (@lem2398104) (@lem2398107)). Qed.
Lemma lem2398109 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398110 : term247 = term244.
Proof. exact (MK_COMB (@lem2398109) (@lem2398108)). Qed.
Lemma lem2398111 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2398112 (a : int) : (term231 a) = (term248 a).
Proof. exact (MK_COMB (@lem2398110) (@lem2398111 a)). Qed.
Lemma lem2398113 (a : int) : (term230 a) = (term248 a).
Proof. exact (TRANS (@lem2398010 a) (@lem2398112 a)). Qed.
Lemma lem2398114 (a : int) : (term248 a) = term81.
Proof. exact (@lem1982719 (real_of_int a)). Qed.
Lemma lem2398115 (a : int) : (term230 a) = term81.
Proof. exact (TRANS (@lem2398113 a) (@lem2398114 a)). Qed.
Lemma lem2398116 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398117 (a : int) : (term249 a) = term250.
Proof. exact (MK_COMB (@lem2398116) (@lem2398115 a)). Qed.
Lemma lem2398118 (b : int) (c : int) : (term251 b c) = (term252 b c).
Proof. exact (@lem1982753 (term89 b) (real_of_int b) (real_of_int c) (term137 c)). Qed.
Lemma lem2398119 (b : int) : (term253 b) = (term231 b).
Proof. exact (@lem1982713 term88 (real_of_int b)). Qed.
Lemma lem2398121 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2398122 : term27 = term109.
Proof. exact (@lem2398121 term28). Qed.
Lemma lem2398124 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2398125 : term88 = term94.
Proof. exact (@lem2398124 term28). Qed.
Lemma lem2398126 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398127 : term232 = term233.
Proof. exact (MK_COMB (@lem2398126) (@lem2398125)). Qed.
Lemma lem2398128 : term234 = term235.
Proof. exact (MK_COMB (@lem2398127) (@lem2398122)). Qed.
Lemma lem2398129 : term236.
Proof. exact (@lem1981473 term88 term27 term27 term27 term81 term27). Qed.
Lemma lem2398131 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398132 : term199 = term206.
Proof. exact (@lem2398131 (NUMERAL 0) term28). Qed.
Lemma lem2398133 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398134 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398135 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398134 h1) (fun h1 : term206 = True => @lem2398133)). Qed.
Lemma lem2398136 : term206 = True.
Proof. exact (EQ_MP (@lem2398135) (@lem2398133)). Qed.
Lemma lem2398137 : term199 = True.
Proof. exact (TRANS (@lem2398132) (@lem2398136)). Qed.
Lemma lem2398138 : True = term199.
Proof. exact (SYM (@lem2398137)). Qed.
Lemma lem2398139 : term199.
Proof. exact (EQ_MP (@lem2398138) (@lem0)). Qed.
Lemma lem2398140 : term237.
Proof. exact (@lem2398129 (@lem2398139)). Qed.
Lemma lem2398142 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398143 : term199 = term206.
Proof. exact (@lem2398142 (NUMERAL 0) term28). Qed.
Lemma lem2398144 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398145 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398146 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398145 h1) (fun h1 : term206 = True => @lem2398144)). Qed.
Lemma lem2398147 : term206 = True.
Proof. exact (EQ_MP (@lem2398146) (@lem2398144)). Qed.
Lemma lem2398148 : term199 = True.
Proof. exact (TRANS (@lem2398143) (@lem2398147)). Qed.
Lemma lem2398149 : True = term199.
Proof. exact (SYM (@lem2398148)). Qed.
Lemma lem2398150 : term199.
Proof. exact (EQ_MP (@lem2398149) (@lem0)). Qed.
Lemma lem2398151 : term238.
Proof. exact (@lem2398140 (@lem2398150)). Qed.
Lemma lem2398153 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398154 : term199 = term206.
Proof. exact (@lem2398153 (NUMERAL 0) term28). Qed.
Lemma lem2398155 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398156 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398157 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398156 h1) (fun h1 : term206 = True => @lem2398155)). Qed.
Lemma lem2398158 : term206 = True.
Proof. exact (EQ_MP (@lem2398157) (@lem2398155)). Qed.
Lemma lem2398159 : term199 = True.
Proof. exact (TRANS (@lem2398154) (@lem2398158)). Qed.
Lemma lem2398160 : True = term199.
Proof. exact (SYM (@lem2398159)). Qed.
Lemma lem2398161 : term199.
Proof. exact (EQ_MP (@lem2398160) (@lem0)). Qed.
Lemma lem2398162 : term239.
Proof. exact (@lem2398151 (@lem2398161)). Qed.
Lemma lem2398164 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398165 : term102 = term103.
Proof. exact (@lem2398164 term28 term28). Qed.
Lemma lem2398166 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398167 : term105 = term28.
Proof. exact (EQ_MP (@lem2398166) (@lem940073)). Qed.
Lemma lem2398168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398169 : term103 = term27.
Proof. exact (MK_COMB (@lem2398168) (@lem2398167)). Qed.
Lemma lem2398170 : term102 = term27.
Proof. exact (TRANS (@lem2398165) (@lem2398169)). Qed.
Lemma lem2398172 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2398173 : term129 = term134.
Proof. exact (@lem2398172 term28 term28). Qed.
Lemma lem2398174 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398175 : term105 = term28.
Proof. exact (EQ_MP (@lem2398174) (@lem940073)). Qed.
Lemma lem2398176 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398177 : term103 = term27.
Proof. exact (MK_COMB (@lem2398176) (@lem2398175)). Qed.
Lemma lem2398178 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2398179 : term134 = term88.
Proof. exact (MK_COMB (@lem2398178) (@lem2398177)). Qed.
Lemma lem2398180 : term129 = term88.
Proof. exact (TRANS (@lem2398173) (@lem2398179)). Qed.
Lemma lem2398181 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398182 : term240 = term232.
Proof. exact (MK_COMB (@lem2398181) (@lem2398180)). Qed.
Lemma lem2398183 : term241 = term234.
Proof. exact (MK_COMB (@lem2398182) (@lem2398170)). Qed.
Lemma lem2398185 (m : nat) : (term242 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2398186 : term234 = term81.
Proof. exact (@lem2398185 term28). Qed.
Lemma lem2398187 : term241 = term81.
Proof. exact (TRANS (@lem2398183) (@lem2398186)). Qed.
Lemma lem2398188 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398189 : term243 = term244.
Proof. exact (MK_COMB (@lem2398188) (@lem2398187)). Qed.
Lemma lem2398190 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2398191 : term245 = term211.
Proof. exact (MK_COMB (@lem2398189) (@lem2398190)). Qed.
Lemma lem2398193 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398194 : term211 = term81.
Proof. exact (@lem2398193 term28). Qed.
Lemma lem2398195 : term245 = term81.
Proof. exact (TRANS (@lem2398191) (@lem2398194)). Qed.
Lemma lem2398197 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398198 : term102 = term103.
Proof. exact (@lem2398197 term28 term28). Qed.
Lemma lem2398199 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398200 : term105 = term28.
Proof. exact (EQ_MP (@lem2398199) (@lem940073)). Qed.
Lemma lem2398201 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398202 : term103 = term27.
Proof. exact (MK_COMB (@lem2398201) (@lem2398200)). Qed.
Lemma lem2398203 : term102 = term27.
Proof. exact (TRANS (@lem2398198) (@lem2398202)). Qed.
Lemma lem2398204 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem2398205 : term246 = term211.
Proof. exact (MK_COMB (@lem2398204) (@lem2398203)). Qed.
Lemma lem2398207 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398208 : term211 = term81.
Proof. exact (@lem2398207 term28). Qed.
Lemma lem2398209 : term246 = term81.
Proof. exact (TRANS (@lem2398205) (@lem2398208)). Qed.
Lemma lem2398210 : term81 = term246.
Proof. exact (SYM (@lem2398209)). Qed.
Lemma lem2398211 : term245 = term246.
Proof. exact (TRANS (@lem2398195) (@lem2398210)). Qed.
Lemma lem2398212 : term235 = term200.
Proof. exact (@lem2398162 (@lem2398211)). Qed.
Lemma lem2398213 : term234 = term200.
Proof. exact (TRANS (@lem2398128) (@lem2398212)). Qed.
Lemma lem2398215 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2398216 : term200 = term81.
Proof. exact (@lem2398215 term81). Qed.
Lemma lem2398217 : term234 = term81.
Proof. exact (TRANS (@lem2398213) (@lem2398216)). Qed.
Lemma lem2398218 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398219 : term247 = term244.
Proof. exact (MK_COMB (@lem2398218) (@lem2398217)). Qed.
Lemma lem2398220 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2398221 (b : int) : (term231 b) = (term248 b).
Proof. exact (MK_COMB (@lem2398219) (@lem2398220 b)). Qed.
Lemma lem2398222 (b : int) : (term253 b) = (term248 b).
Proof. exact (TRANS (@lem2398119 b) (@lem2398221 b)). Qed.
Lemma lem2398223 (b : int) : (term248 b) = term81.
Proof. exact (@lem1982719 (real_of_int b)). Qed.
Lemma lem2398224 (b : int) : (term253 b) = term81.
Proof. exact (TRANS (@lem2398222 b) (@lem2398223 b)). Qed.
Lemma lem2398225 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398226 (b : int) : (term254 b) = term250.
Proof. exact (MK_COMB (@lem2398225) (@lem2398224 b)). Qed.
Lemma lem2398227 (c : int) : (term255 c) = (term256 c).
Proof. exact (@lem1982763 (real_of_int c) (term89 c) term88). Qed.
Lemma lem2398228 (c : int) : (term230 c) = (term231 c).
Proof. exact (@lem1982715 term88 (real_of_int c)). Qed.
Lemma lem2398230 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2398231 : term27 = term109.
Proof. exact (@lem2398230 term28). Qed.
Lemma lem2398233 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2398234 : term88 = term94.
Proof. exact (@lem2398233 term28). Qed.
Lemma lem2398235 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398236 : term232 = term233.
Proof. exact (MK_COMB (@lem2398235) (@lem2398234)). Qed.
Lemma lem2398237 : term234 = term235.
Proof. exact (MK_COMB (@lem2398236) (@lem2398231)). Qed.
Lemma lem2398238 : term236.
Proof. exact (@lem1981473 term88 term27 term27 term27 term81 term27). Qed.
Lemma lem2398240 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398241 : term199 = term206.
Proof. exact (@lem2398240 (NUMERAL 0) term28). Qed.
Lemma lem2398242 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398243 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398244 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398243 h1) (fun h1 : term206 = True => @lem2398242)). Qed.
Lemma lem2398245 : term206 = True.
Proof. exact (EQ_MP (@lem2398244) (@lem2398242)). Qed.
Lemma lem2398246 : term199 = True.
Proof. exact (TRANS (@lem2398241) (@lem2398245)). Qed.
Lemma lem2398247 : True = term199.
Proof. exact (SYM (@lem2398246)). Qed.
Lemma lem2398248 : term199.
Proof. exact (EQ_MP (@lem2398247) (@lem0)). Qed.
Lemma lem2398249 : term237.
Proof. exact (@lem2398238 (@lem2398248)). Qed.
Lemma lem2398251 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398252 : term199 = term206.
Proof. exact (@lem2398251 (NUMERAL 0) term28). Qed.
Lemma lem2398253 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398254 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398255 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398254 h1) (fun h1 : term206 = True => @lem2398253)). Qed.
Lemma lem2398256 : term206 = True.
Proof. exact (EQ_MP (@lem2398255) (@lem2398253)). Qed.
Lemma lem2398257 : term199 = True.
Proof. exact (TRANS (@lem2398252) (@lem2398256)). Qed.
Lemma lem2398258 : True = term199.
Proof. exact (SYM (@lem2398257)). Qed.
Lemma lem2398259 : term199.
Proof. exact (EQ_MP (@lem2398258) (@lem0)). Qed.
Lemma lem2398260 : term238.
Proof. exact (@lem2398249 (@lem2398259)). Qed.
Lemma lem2398262 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398263 : term199 = term206.
Proof. exact (@lem2398262 (NUMERAL 0) term28). Qed.
Lemma lem2398264 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398265 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398266 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398265 h1) (fun h1 : term206 = True => @lem2398264)). Qed.
Lemma lem2398267 : term206 = True.
Proof. exact (EQ_MP (@lem2398266) (@lem2398264)). Qed.
Lemma lem2398268 : term199 = True.
Proof. exact (TRANS (@lem2398263) (@lem2398267)). Qed.
Lemma lem2398269 : True = term199.
Proof. exact (SYM (@lem2398268)). Qed.
Lemma lem2398270 : term199.
Proof. exact (EQ_MP (@lem2398269) (@lem0)). Qed.
Lemma lem2398271 : term239.
Proof. exact (@lem2398260 (@lem2398270)). Qed.
Lemma lem2398273 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398274 : term102 = term103.
Proof. exact (@lem2398273 term28 term28). Qed.
Lemma lem2398275 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398276 : term105 = term28.
Proof. exact (EQ_MP (@lem2398275) (@lem940073)). Qed.
Lemma lem2398277 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398278 : term103 = term27.
Proof. exact (MK_COMB (@lem2398277) (@lem2398276)). Qed.
Lemma lem2398279 : term102 = term27.
Proof. exact (TRANS (@lem2398274) (@lem2398278)). Qed.
Lemma lem2398281 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2398282 : term129 = term134.
Proof. exact (@lem2398281 term28 term28). Qed.
Lemma lem2398283 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398284 : term105 = term28.
Proof. exact (EQ_MP (@lem2398283) (@lem940073)). Qed.
Lemma lem2398285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398286 : term103 = term27.
Proof. exact (MK_COMB (@lem2398285) (@lem2398284)). Qed.
Lemma lem2398287 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2398288 : term134 = term88.
Proof. exact (MK_COMB (@lem2398287) (@lem2398286)). Qed.
Lemma lem2398289 : term129 = term88.
Proof. exact (TRANS (@lem2398282) (@lem2398288)). Qed.
Lemma lem2398290 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398291 : term240 = term232.
Proof. exact (MK_COMB (@lem2398290) (@lem2398289)). Qed.
Lemma lem2398292 : term241 = term234.
Proof. exact (MK_COMB (@lem2398291) (@lem2398279)). Qed.
Lemma lem2398294 (m : nat) : (term242 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2398295 : term234 = term81.
Proof. exact (@lem2398294 term28). Qed.
Lemma lem2398296 : term241 = term81.
Proof. exact (TRANS (@lem2398292) (@lem2398295)). Qed.
Lemma lem2398297 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398298 : term243 = term244.
Proof. exact (MK_COMB (@lem2398297) (@lem2398296)). Qed.
Lemma lem2398299 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2398300 : term245 = term211.
Proof. exact (MK_COMB (@lem2398298) (@lem2398299)). Qed.
Lemma lem2398302 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398303 : term211 = term81.
Proof. exact (@lem2398302 term28). Qed.
Lemma lem2398304 : term245 = term81.
Proof. exact (TRANS (@lem2398300) (@lem2398303)). Qed.
Lemma lem2398306 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398307 : term102 = term103.
Proof. exact (@lem2398306 term28 term28). Qed.
Lemma lem2398308 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398309 : term105 = term28.
Proof. exact (EQ_MP (@lem2398308) (@lem940073)). Qed.
Lemma lem2398310 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398311 : term103 = term27.
Proof. exact (MK_COMB (@lem2398310) (@lem2398309)). Qed.
Lemma lem2398312 : term102 = term27.
Proof. exact (TRANS (@lem2398307) (@lem2398311)). Qed.
Lemma lem2398313 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem2398314 : term246 = term211.
Proof. exact (MK_COMB (@lem2398313) (@lem2398312)). Qed.
Lemma lem2398316 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398317 : term211 = term81.
Proof. exact (@lem2398316 term28). Qed.
Lemma lem2398318 : term246 = term81.
Proof. exact (TRANS (@lem2398314) (@lem2398317)). Qed.
Lemma lem2398319 : term81 = term246.
Proof. exact (SYM (@lem2398318)). Qed.
Lemma lem2398320 : term245 = term246.
Proof. exact (TRANS (@lem2398304) (@lem2398319)). Qed.
Lemma lem2398321 : term235 = term200.
Proof. exact (@lem2398271 (@lem2398320)). Qed.
Lemma lem2398322 : term234 = term200.
Proof. exact (TRANS (@lem2398237) (@lem2398321)). Qed.
Lemma lem2398324 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2398325 : term200 = term81.
Proof. exact (@lem2398324 term81). Qed.
Lemma lem2398326 : term234 = term81.
Proof. exact (TRANS (@lem2398322) (@lem2398325)). Qed.
Lemma lem2398327 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398328 : term247 = term244.
Proof. exact (MK_COMB (@lem2398327) (@lem2398326)). Qed.
Lemma lem2398329 (c : int) : (real_of_int c) = (real_of_int c).
Proof. exact (eq_refl (real_of_int c)). Qed.
Lemma lem2398330 (c : int) : (term231 c) = (term248 c).
Proof. exact (MK_COMB (@lem2398328) (@lem2398329 c)). Qed.
Lemma lem2398331 (c : int) : (term230 c) = (term248 c).
Proof. exact (TRANS (@lem2398228 c) (@lem2398330 c)). Qed.
Lemma lem2398332 (c : int) : (term248 c) = term81.
Proof. exact (@lem1982719 (real_of_int c)). Qed.
Lemma lem2398333 (c : int) : (term230 c) = term81.
Proof. exact (TRANS (@lem2398331 c) (@lem2398332 c)). Qed.
Lemma lem2398334 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398335 (c : int) : (term249 c) = term250.
Proof. exact (MK_COMB (@lem2398334) (@lem2398333 c)). Qed.
Lemma lem2398336 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem2398337 (c : int) : (term256 c) = term257.
Proof. exact (MK_COMB (@lem2398335 c) (@lem2398336)). Qed.
Lemma lem2398338 (c : int) : (term255 c) = term257.
Proof. exact (TRANS (@lem2398227 c) (@lem2398337 c)). Qed.
Lemma lem2398339 : term257 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem2398340 (c : int) : (term255 c) = term88.
Proof. exact (TRANS (@lem2398338 c) (@lem2398339)). Qed.
Lemma lem2398341 (b : int) (c : int) : (term252 b c) = term257.
Proof. exact (MK_COMB (@lem2398226 b) (@lem2398340 c)). Qed.
Lemma lem2398342 (b : int) (c : int) : (term251 b c) = term257.
Proof. exact (TRANS (@lem2398118 b c) (@lem2398341 b c)). Qed.
Lemma lem2398343 : term257 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem2398344 (b : int) (c : int) : (term251 b c) = term88.
Proof. exact (TRANS (@lem2398342 b c) (@lem2398343)). Qed.
Lemma lem2398345 (a : int) (b : int) (c : int) : (term229 a b c) = term257.
Proof. exact (MK_COMB (@lem2398117 a) (@lem2398344 b c)). Qed.
Lemma lem2398346 (a : int) (b : int) (c : int) : (term228 a b c) = term257.
Proof. exact (TRANS (@lem2398009 a b c) (@lem2398345 a b c)). Qed.
Lemma lem2398347 : term257 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem2398348 (a : int) (b : int) (c : int) : (term228 a b c) = term88.
Proof. exact (TRANS (@lem2398346 a b c) (@lem2398347)). Qed.
Lemma lem2398349 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2398350 (a : int) (b : int) (c : int) : (term258 a b c) = term259.
Proof. exact (MK_COMB (@lem2398349) (@lem2398348 a b c)). Qed.
Lemma lem2398351 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2398352 (a : int) (b : int) (c : int) : (term227 a b c) = term260.
Proof. exact (MK_COMB (@lem2398350 a b c) (@lem2398351)). Qed.
Lemma lem2398353 (a : int) (b : int) (c : int) (h1 : term197 a b c) : term260.
Proof. exact (EQ_MP (@lem2398352 a b c) (@lem2398008 a b c h1)). Qed.
Lemma lem2398355 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2398356 : term260 = term261.
Proof. exact (@lem2398355 term81 term88). Qed.
Lemma lem2398358 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2398359 : term88 = term94.
Proof. exact (@lem2398358 term28). Qed.
Lemma lem2398361 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2398362 : term81 = term200.
Proof. exact (@lem2398361 (NUMERAL 0)). Qed.
Lemma lem2398363 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2398364 : term262 = term263.
Proof. exact (MK_COMB (@lem2398363) (@lem2398362)). Qed.
Lemma lem2398365 : term261 = term264.
Proof. exact (MK_COMB (@lem2398364) (@lem2398359)). Qed.
Lemma lem2398366 : term265.
Proof. exact (@lem1980026 term81 term27 term88 term27). Qed.
Lemma lem2398368 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398369 : term199 = term206.
Proof. exact (@lem2398368 (NUMERAL 0) term28). Qed.
Lemma lem2398370 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398371 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398372 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398371 h1) (fun h1 : term206 = True => @lem2398370)). Qed.
Lemma lem2398373 : term206 = True.
Proof. exact (EQ_MP (@lem2398372) (@lem2398370)). Qed.
Lemma lem2398374 : term199 = True.
Proof. exact (TRANS (@lem2398369) (@lem2398373)). Qed.
Lemma lem2398375 : True = term199.
Proof. exact (SYM (@lem2398374)). Qed.
Lemma lem2398376 : term199.
Proof. exact (EQ_MP (@lem2398375) (@lem0)). Qed.
Lemma lem2398377 : term266.
Proof. exact (@lem2398366 (@lem2398376)). Qed.
Lemma lem2398379 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398380 : term199 = term206.
Proof. exact (@lem2398379 (NUMERAL 0) term28). Qed.
Lemma lem2398381 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398382 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398383 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398382 h1) (fun h1 : term206 = True => @lem2398381)). Qed.
Lemma lem2398384 : term206 = True.
Proof. exact (EQ_MP (@lem2398383) (@lem2398381)). Qed.
Lemma lem2398385 : term199 = True.
Proof. exact (TRANS (@lem2398380) (@lem2398384)). Qed.
Lemma lem2398386 : True = term199.
Proof. exact (SYM (@lem2398385)). Qed.
Lemma lem2398387 : term199.
Proof. exact (EQ_MP (@lem2398386) (@lem0)). Qed.
Lemma lem2398388 : term264 = term267.
Proof. exact (@lem2398377 (@lem2398387)). Qed.
Lemma lem2398390 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2398391 : term129 = term134.
Proof. exact (@lem2398390 term28 term28). Qed.
Lemma lem2398392 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398393 : term105 = term28.
Proof. exact (EQ_MP (@lem2398392) (@lem940073)). Qed.
Lemma lem2398394 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398395 : term103 = term27.
Proof. exact (MK_COMB (@lem2398394) (@lem2398393)). Qed.
Lemma lem2398396 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2398397 : term134 = term88.
Proof. exact (MK_COMB (@lem2398396) (@lem2398395)). Qed.
Lemma lem2398398 : term129 = term88.
Proof. exact (TRANS (@lem2398391) (@lem2398397)). Qed.
Lemma lem2398400 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398401 : term211 = term81.
Proof. exact (@lem2398400 term28). Qed.
Lemma lem2398402 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2398403 : term268 = term262.
Proof. exact (MK_COMB (@lem2398402) (@lem2398401)). Qed.
Lemma lem2398404 : term267 = term261.
Proof. exact (MK_COMB (@lem2398403) (@lem2398398)). Qed.
Lemma lem2398406 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2398407 : term261 = term271.
Proof. exact (@lem2398406 (NUMERAL 0) term28). Qed.
Lemma lem2398408 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398409 (h1 : term207 = (BIT1 0)) : (term28 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2398410 : (term207 = (BIT1 0)) = ((term28 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398409 h1) (fun h1 : (term28 = (NUMERAL 0)) = False => @lem2398408)). Qed.
Lemma lem2398411 : (term28 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2398410) (@lem2398408)). Qed.
Lemma lem2398412 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2398413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2398414 : term272 = (and True).
Proof. exact (MK_COMB (@lem2398413) (@lem2398412)). Qed.
Lemma lem2398415 : term271 = (True /\ False).
Proof. exact (MK_COMB (@lem2398414) (@lem2398411)). Qed.
Lemma lem2398417 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2398418 : term271 = False.
Proof. exact (TRANS (@lem2398415) (@lem2398417)). Qed.
Lemma lem2398419 : term261 = False.
Proof. exact (TRANS (@lem2398407) (@lem2398418)). Qed.
Lemma lem2398420 : term267 = False.
Proof. exact (TRANS (@lem2398404) (@lem2398419)). Qed.
Lemma lem2398421 : term264 = False.
Proof. exact (TRANS (@lem2398388) (@lem2398420)). Qed.
Lemma lem2398422 : term261 = False.
Proof. exact (TRANS (@lem2398365) (@lem2398421)). Qed.
Lemma lem2398423 : term260 = False.
Proof. exact (TRANS (@lem2398356) (@lem2398422)). Qed.
Lemma lem2398424 (a : int) (b : int) (c : int) (h1 : term197 a b c) : False.
Proof. exact (EQ_MP (@lem2398423) (@lem2398353 a b c h1)). Qed.
Lemma lem2398425 (a : int) (b : int) (c : int) (h1 : term273 a b c) : term273 a b c.
Proof. exact (h1). Qed.
Lemma lem2398426 (a : int) (b : int) (c : int) (h1 : term273 a b c) : term155 a b c.
Proof. exact (proj2 (@lem2398425 a b c h1)). Qed.
Lemma lem2398427 (a : int) (b : int) (c : int) (h1 : term273 a b c) : (term116 a b c) = term81.
Proof. exact (proj1 (@lem2398425 a b c h1)). Qed.
Lemma lem2398429 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2398430 : term198 = term199.
Proof. exact (@lem2398429 term81 term27). Qed.
Lemma lem2398432 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2398433 : term27 = term109.
Proof. exact (@lem2398432 term28). Qed.
Lemma lem2398435 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2398436 : term81 = term200.
Proof. exact (@lem2398435 (NUMERAL 0)). Qed.
Lemma lem2398437 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2398438 : term201 = term202.
Proof. exact (MK_COMB (@lem2398437) (@lem2398436)). Qed.
Lemma lem2398439 : term199 = term203.
Proof. exact (MK_COMB (@lem2398438) (@lem2398433)). Qed.
Lemma lem2398440 : term204.
Proof. exact (@lem1980255 term81 term27 term27 term27). Qed.
Lemma lem2398442 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398443 : term199 = term206.
Proof. exact (@lem2398442 (NUMERAL 0) term28). Qed.
Lemma lem2398444 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398445 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398446 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398445 h1) (fun h1 : term206 = True => @lem2398444)). Qed.
Lemma lem2398447 : term206 = True.
Proof. exact (EQ_MP (@lem2398446) (@lem2398444)). Qed.
Lemma lem2398448 : term199 = True.
Proof. exact (TRANS (@lem2398443) (@lem2398447)). Qed.
Lemma lem2398449 : True = term199.
Proof. exact (SYM (@lem2398448)). Qed.
Lemma lem2398450 : term199.
Proof. exact (EQ_MP (@lem2398449) (@lem0)). Qed.
Lemma lem2398451 : term208.
Proof. exact (@lem2398440 (@lem2398450)). Qed.
Lemma lem2398453 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398454 : term199 = term206.
Proof. exact (@lem2398453 (NUMERAL 0) term28). Qed.
Lemma lem2398455 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398456 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398457 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398456 h1) (fun h1 : term206 = True => @lem2398455)). Qed.
Lemma lem2398458 : term206 = True.
Proof. exact (EQ_MP (@lem2398457) (@lem2398455)). Qed.
Lemma lem2398459 : term199 = True.
Proof. exact (TRANS (@lem2398454) (@lem2398458)). Qed.
Lemma lem2398460 : True = term199.
Proof. exact (SYM (@lem2398459)). Qed.
Lemma lem2398461 : term199.
Proof. exact (EQ_MP (@lem2398460) (@lem0)). Qed.
Lemma lem2398462 : term203 = term209.
Proof. exact (@lem2398451 (@lem2398461)). Qed.
Lemma lem2398464 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398465 : term102 = term103.
Proof. exact (@lem2398464 term28 term28). Qed.
Lemma lem2398466 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398467 : term105 = term28.
Proof. exact (EQ_MP (@lem2398466) (@lem940073)). Qed.
Lemma lem2398468 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398469 : term103 = term27.
Proof. exact (MK_COMB (@lem2398468) (@lem2398467)). Qed.
Lemma lem2398470 : term102 = term27.
Proof. exact (TRANS (@lem2398465) (@lem2398469)). Qed.
Lemma lem2398472 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398473 : term211 = term81.
Proof. exact (@lem2398472 term28). Qed.
Lemma lem2398474 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2398475 : term212 = term201.
Proof. exact (MK_COMB (@lem2398474) (@lem2398473)). Qed.
Lemma lem2398476 : term209 = term199.
Proof. exact (MK_COMB (@lem2398475) (@lem2398470)). Qed.
Lemma lem2398478 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398479 : term199 = term206.
Proof. exact (@lem2398478 (NUMERAL 0) term28). Qed.
Lemma lem2398480 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398481 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398482 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398481 h1) (fun h1 : term206 = True => @lem2398480)). Qed.
Lemma lem2398483 : term206 = True.
Proof. exact (EQ_MP (@lem2398482) (@lem2398480)). Qed.
Lemma lem2398484 : term199 = True.
Proof. exact (TRANS (@lem2398479) (@lem2398483)). Qed.
Lemma lem2398485 : term209 = True.
Proof. exact (TRANS (@lem2398476) (@lem2398484)). Qed.
Lemma lem2398486 : term203 = True.
Proof. exact (TRANS (@lem2398462) (@lem2398485)). Qed.
Lemma lem2398487 : term199 = True.
Proof. exact (TRANS (@lem2398439) (@lem2398486)). Qed.
Lemma lem2398488 : term198 = True.
Proof. exact (TRANS (@lem2398430) (@lem2398487)). Qed.
Lemma lem2398489 : True = term198.
Proof. exact (SYM (@lem2398488)). Qed.
Lemma lem2398490 : term198.
Proof. exact (EQ_MP (@lem2398489) (@lem0)). Qed.
Lemma lem2398491 (a : int) (b : int) (c : int) (h1 : term273 a b c) : term274 a b c.
Proof. exact (conj (@lem2398490) (@lem2398426 a b c h1)). Qed.
Lemma lem2398493 (x : real) (y : real) : term214 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2398494 (a : int) (b : int) (c : int) : term275 a b c.
Proof. exact (@lem2398493 term27 (term152 a b c)). Qed.
Lemma lem2398495 (a : int) (b : int) (c : int) (h1 : term273 a b c) : term276 a b c.
Proof. exact (@lem2398494 a b c (@lem2398491 a b c h1)). Qed.
Lemma lem2398496 (a : int) (b : int) (c : int) : (term277 a b c) = (term152 a b c).
Proof. exact (@lem1982733 (term152 a b c)). Qed.
Lemma lem2398497 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2398498 (a : int) (b : int) (c : int) : (term278 a b c) = (term154 a b c).
Proof. exact (MK_COMB (@lem2398497) (@lem2398496 a b c)). Qed.
Lemma lem2398499 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2398500 (a : int) (b : int) (c : int) : (term276 a b c) = (term155 a b c).
Proof. exact (MK_COMB (@lem2398498 a b c) (@lem2398499)). Qed.
Lemma lem2398501 (a : int) (b : int) (c : int) (h1 : term273 a b c) : term155 a b c.
Proof. exact (EQ_MP (@lem2398500 a b c) (@lem2398495 a b c h1)). Qed.
Lemma lem2398503 (y : real) : term219 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2398504 (a : int) (b : int) (c : int) : term220 a b c.
Proof. exact (@lem2398503 (term116 a b c)). Qed.
Lemma lem2398505 (a : int) (b : int) (c : int) (h1 : term273 a b c) : term221 a b c.
Proof. exact (@lem2398504 a b c (@lem2398427 a b c h1)). Qed.
Lemma lem2398506 (a : int) (b : int) (c : int) (h1 : term273 a b c) : term279 a b c.
Proof. exact (@lem2398505 a b c h1 term88). Qed.
Lemma lem2398507 (a : int) (b : int) (c : int) : (term279 a b c) = ((term280 a b c) = term81).
Proof. exact (eq_refl (term279 a b c)). Qed.
Lemma lem2398508 (a : int) (b : int) (c : int) (h1 : term273 a b c) : (term280 a b c) = term81.
Proof. exact (EQ_MP (@lem2398507 a b c) (@lem2398506 a b c h1)). Qed.
Lemma lem2398509 (a : int) (b : int) (c : int) : (term280 a b c) = (term281 a b c).
Proof. exact (@lem1982781 (real_of_int a) term88 (term115 b c)). Qed.
Lemma lem2398510 (b : int) (c : int) : (term282 b c) = (term283 b c).
Proof. exact (@lem1982781 (term89 b) term88 (real_of_int c)). Qed.
Lemma lem2398511 (c : int) : (term89 c) = (term89 c).
Proof. exact (eq_refl (term89 c)). Qed.
Lemma lem2398512 (b : int) : (term90 b) = (term91 b).
Proof. exact (@lem1982749 term88 term88 (real_of_int b)). Qed.
Lemma lem2398514 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2398515 : term88 = term94.
Proof. exact (@lem2398514 term28). Qed.
Lemma lem2398517 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2398518 : term88 = term94.
Proof. exact (@lem2398517 term28). Qed.
Lemma lem2398519 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398520 : term95 = term96.
Proof. exact (MK_COMB (@lem2398519) (@lem2398518)). Qed.
Lemma lem2398521 : term97 = term98.
Proof. exact (MK_COMB (@lem2398520) (@lem2398515)). Qed.
Lemma lem2398522 : term98 = term99.
Proof. exact (@lem1981613 term88 term88 term27 term27). Qed.
Lemma lem2398524 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398525 : term102 = term103.
Proof. exact (@lem2398524 term28 term28). Qed.
Lemma lem2398526 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398527 : term105 = term28.
Proof. exact (EQ_MP (@lem2398526) (@lem940073)). Qed.
Lemma lem2398528 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398529 : term103 = term27.
Proof. exact (MK_COMB (@lem2398528) (@lem2398527)). Qed.
Lemma lem2398530 : term102 = term27.
Proof. exact (TRANS (@lem2398525) (@lem2398529)). Qed.
Lemma lem2398532 (m : nat) (n : nat) : (term106 m n) = (term101 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2398533 : term97 = term103.
Proof. exact (@lem2398532 term28 term28). Qed.
Lemma lem2398534 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398535 : term105 = term28.
Proof. exact (EQ_MP (@lem2398534) (@lem940073)). Qed.
Lemma lem2398536 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398537 : term103 = term27.
Proof. exact (MK_COMB (@lem2398536) (@lem2398535)). Qed.
Lemma lem2398538 : term97 = term27.
Proof. exact (TRANS (@lem2398533) (@lem2398537)). Qed.
Lemma lem2398539 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2398540 : term107 = term108.
Proof. exact (MK_COMB (@lem2398539) (@lem2398538)). Qed.
Lemma lem2398541 : term99 = term109.
Proof. exact (MK_COMB (@lem2398540) (@lem2398530)). Qed.
Lemma lem2398542 : term98 = term109.
Proof. exact (TRANS (@lem2398522) (@lem2398541)). Qed.
Lemma lem2398543 : term97 = term109.
Proof. exact (TRANS (@lem2398521) (@lem2398542)). Qed.
Lemma lem2398545 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2398546 : term109 = term27.
Proof. exact (@lem2398545 term27). Qed.
Lemma lem2398547 : term97 = term27.
Proof. exact (TRANS (@lem2398543) (@lem2398546)). Qed.
Lemma lem2398548 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398549 : term111 = term112.
Proof. exact (MK_COMB (@lem2398548) (@lem2398547)). Qed.
Lemma lem2398550 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2398551 (b : int) : (term91 b) = (term113 b).
Proof. exact (MK_COMB (@lem2398549) (@lem2398550 b)). Qed.
Lemma lem2398552 (b : int) : (term90 b) = (term113 b).
Proof. exact (TRANS (@lem2398512 b) (@lem2398551 b)). Qed.
Lemma lem2398553 (b : int) : (term113 b) = (real_of_int b).
Proof. exact (@lem1982709 (real_of_int b)). Qed.
Lemma lem2398554 (b : int) : (term90 b) = (real_of_int b).
Proof. exact (TRANS (@lem2398552 b) (@lem2398553 b)). Qed.
Lemma lem2398555 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398556 (b : int) : (term182 b) = (term40 b).
Proof. exact (MK_COMB (@lem2398555) (@lem2398554 b)). Qed.
Lemma lem2398557 (b : int) (c : int) : (term283 b c) = (term82 b c).
Proof. exact (MK_COMB (@lem2398556 b) (@lem2398511 c)). Qed.
Lemma lem2398558 (b : int) (c : int) : (term282 b c) = (term82 b c).
Proof. exact (TRANS (@lem2398510 b c) (@lem2398557 b c)). Qed.
Lemma lem2398561 (a : int) : (term114 a) = (term114 a).
Proof. exact (eq_refl (term114 a)). Qed.
Lemma lem2398562 (a : int) (b : int) (c : int) : (term281 a b c) = (term284 a b c).
Proof. exact (MK_COMB (@lem2398561 a) (@lem2398558 b c)). Qed.
Lemma lem2398563 (a : int) (b : int) (c : int) : (term280 a b c) = (term284 a b c).
Proof. exact (TRANS (@lem2398509 a b c) (@lem2398562 a b c)). Qed.
Lemma lem2398564 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2398565 (a : int) (b : int) (c : int) : (term285 a b c) = (term286 a b c).
Proof. exact (MK_COMB (@lem2398564) (@lem2398563 a b c)). Qed.
Lemma lem2398566 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2398567 (a : int) (b : int) (c : int) : ((term280 a b c) = term81) = ((term284 a b c) = term81).
Proof. exact (MK_COMB (@lem2398565 a b c) (@lem2398566)). Qed.
Lemma lem2398568 (a : int) (b : int) (c : int) (h1 : term273 a b c) : (term284 a b c) = term81.
Proof. exact (EQ_MP (@lem2398567 a b c) (@lem2398508 a b c h1)). Qed.
Lemma lem2398569 (a : int) (b : int) (c : int) (h1 : term273 a b c) : term287 a b c.
Proof. exact (conj (@lem2398568 a b c h1) (@lem2398501 a b c h1)). Qed.
Lemma lem2398571 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2398572 (a : int) (b : int) (c : int) : term288 a b c.
Proof. exact (@lem2398571 (term284 a b c) (term152 a b c)). Qed.
Lemma lem2398573 (a : int) (b : int) (c : int) (h1 : term273 a b c) : term289 a b c.
Proof. exact (@lem2398572 a b c (@lem2398569 a b c h1)). Qed.
Lemma lem2398574 (a : int) (b : int) (c : int) : (term290 a b c) = (term291 a b c).
Proof. exact (@lem1982753 (term89 a) (real_of_int a) (term82 b c) (term151 b c)). Qed.
Lemma lem2398575 (a : int) : (term253 a) = (term231 a).
Proof. exact (@lem1982713 term88 (real_of_int a)). Qed.
Lemma lem2398577 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2398578 : term27 = term109.
Proof. exact (@lem2398577 term28). Qed.
Lemma lem2398580 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2398581 : term88 = term94.
Proof. exact (@lem2398580 term28). Qed.
Lemma lem2398582 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398583 : term232 = term233.
Proof. exact (MK_COMB (@lem2398582) (@lem2398581)). Qed.
Lemma lem2398584 : term234 = term235.
Proof. exact (MK_COMB (@lem2398583) (@lem2398578)). Qed.
Lemma lem2398585 : term236.
Proof. exact (@lem1981473 term88 term27 term27 term27 term81 term27). Qed.
Lemma lem2398587 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398588 : term199 = term206.
Proof. exact (@lem2398587 (NUMERAL 0) term28). Qed.
Lemma lem2398589 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398590 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398591 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398590 h1) (fun h1 : term206 = True => @lem2398589)). Qed.
Lemma lem2398592 : term206 = True.
Proof. exact (EQ_MP (@lem2398591) (@lem2398589)). Qed.
Lemma lem2398593 : term199 = True.
Proof. exact (TRANS (@lem2398588) (@lem2398592)). Qed.
Lemma lem2398594 : True = term199.
Proof. exact (SYM (@lem2398593)). Qed.
Lemma lem2398595 : term199.
Proof. exact (EQ_MP (@lem2398594) (@lem0)). Qed.
Lemma lem2398596 : term237.
Proof. exact (@lem2398585 (@lem2398595)). Qed.
Lemma lem2398598 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398599 : term199 = term206.
Proof. exact (@lem2398598 (NUMERAL 0) term28). Qed.
Lemma lem2398600 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398601 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398602 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398601 h1) (fun h1 : term206 = True => @lem2398600)). Qed.
Lemma lem2398603 : term206 = True.
Proof. exact (EQ_MP (@lem2398602) (@lem2398600)). Qed.
Lemma lem2398604 : term199 = True.
Proof. exact (TRANS (@lem2398599) (@lem2398603)). Qed.
Lemma lem2398605 : True = term199.
Proof. exact (SYM (@lem2398604)). Qed.
Lemma lem2398606 : term199.
Proof. exact (EQ_MP (@lem2398605) (@lem0)). Qed.
Lemma lem2398607 : term238.
Proof. exact (@lem2398596 (@lem2398606)). Qed.
Lemma lem2398609 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398610 : term199 = term206.
Proof. exact (@lem2398609 (NUMERAL 0) term28). Qed.
Lemma lem2398611 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398612 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398613 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398612 h1) (fun h1 : term206 = True => @lem2398611)). Qed.
Lemma lem2398614 : term206 = True.
Proof. exact (EQ_MP (@lem2398613) (@lem2398611)). Qed.
Lemma lem2398615 : term199 = True.
Proof. exact (TRANS (@lem2398610) (@lem2398614)). Qed.
Lemma lem2398616 : True = term199.
Proof. exact (SYM (@lem2398615)). Qed.
Lemma lem2398617 : term199.
Proof. exact (EQ_MP (@lem2398616) (@lem0)). Qed.
Lemma lem2398618 : term239.
Proof. exact (@lem2398607 (@lem2398617)). Qed.
Lemma lem2398620 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398621 : term102 = term103.
Proof. exact (@lem2398620 term28 term28). Qed.
Lemma lem2398622 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398623 : term105 = term28.
Proof. exact (EQ_MP (@lem2398622) (@lem940073)). Qed.
Lemma lem2398624 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398625 : term103 = term27.
Proof. exact (MK_COMB (@lem2398624) (@lem2398623)). Qed.
Lemma lem2398626 : term102 = term27.
Proof. exact (TRANS (@lem2398621) (@lem2398625)). Qed.
Lemma lem2398628 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2398629 : term129 = term134.
Proof. exact (@lem2398628 term28 term28). Qed.
Lemma lem2398630 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398631 : term105 = term28.
Proof. exact (EQ_MP (@lem2398630) (@lem940073)). Qed.
Lemma lem2398632 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398633 : term103 = term27.
Proof. exact (MK_COMB (@lem2398632) (@lem2398631)). Qed.
Lemma lem2398634 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2398635 : term134 = term88.
Proof. exact (MK_COMB (@lem2398634) (@lem2398633)). Qed.
Lemma lem2398636 : term129 = term88.
Proof. exact (TRANS (@lem2398629) (@lem2398635)). Qed.
Lemma lem2398637 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398638 : term240 = term232.
Proof. exact (MK_COMB (@lem2398637) (@lem2398636)). Qed.
Lemma lem2398639 : term241 = term234.
Proof. exact (MK_COMB (@lem2398638) (@lem2398626)). Qed.
Lemma lem2398641 (m : nat) : (term242 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2398642 : term234 = term81.
Proof. exact (@lem2398641 term28). Qed.
Lemma lem2398643 : term241 = term81.
Proof. exact (TRANS (@lem2398639) (@lem2398642)). Qed.
Lemma lem2398644 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398645 : term243 = term244.
Proof. exact (MK_COMB (@lem2398644) (@lem2398643)). Qed.
Lemma lem2398646 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2398647 : term245 = term211.
Proof. exact (MK_COMB (@lem2398645) (@lem2398646)). Qed.
Lemma lem2398649 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398650 : term211 = term81.
Proof. exact (@lem2398649 term28). Qed.
Lemma lem2398651 : term245 = term81.
Proof. exact (TRANS (@lem2398647) (@lem2398650)). Qed.
Lemma lem2398653 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398654 : term102 = term103.
Proof. exact (@lem2398653 term28 term28). Qed.
Lemma lem2398655 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398656 : term105 = term28.
Proof. exact (EQ_MP (@lem2398655) (@lem940073)). Qed.
Lemma lem2398657 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398658 : term103 = term27.
Proof. exact (MK_COMB (@lem2398657) (@lem2398656)). Qed.
Lemma lem2398659 : term102 = term27.
Proof. exact (TRANS (@lem2398654) (@lem2398658)). Qed.
Lemma lem2398660 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem2398661 : term246 = term211.
Proof. exact (MK_COMB (@lem2398660) (@lem2398659)). Qed.
Lemma lem2398663 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398664 : term211 = term81.
Proof. exact (@lem2398663 term28). Qed.
Lemma lem2398665 : term246 = term81.
Proof. exact (TRANS (@lem2398661) (@lem2398664)). Qed.
Lemma lem2398666 : term81 = term246.
Proof. exact (SYM (@lem2398665)). Qed.
Lemma lem2398667 : term245 = term246.
Proof. exact (TRANS (@lem2398651) (@lem2398666)). Qed.
Lemma lem2398668 : term235 = term200.
Proof. exact (@lem2398618 (@lem2398667)). Qed.
Lemma lem2398669 : term234 = term200.
Proof. exact (TRANS (@lem2398584) (@lem2398668)). Qed.
Lemma lem2398671 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2398672 : term200 = term81.
Proof. exact (@lem2398671 term81). Qed.
Lemma lem2398673 : term234 = term81.
Proof. exact (TRANS (@lem2398669) (@lem2398672)). Qed.
Lemma lem2398674 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398675 : term247 = term244.
Proof. exact (MK_COMB (@lem2398674) (@lem2398673)). Qed.
Lemma lem2398676 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2398677 (a : int) : (term231 a) = (term248 a).
Proof. exact (MK_COMB (@lem2398675) (@lem2398676 a)). Qed.
Lemma lem2398678 (a : int) : (term253 a) = (term248 a).
Proof. exact (TRANS (@lem2398575 a) (@lem2398677 a)). Qed.
Lemma lem2398679 (a : int) : (term248 a) = term81.
Proof. exact (@lem1982719 (real_of_int a)). Qed.
Lemma lem2398680 (a : int) : (term253 a) = term81.
Proof. exact (TRANS (@lem2398678 a) (@lem2398679 a)). Qed.
Lemma lem2398681 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398682 (a : int) : (term254 a) = term250.
Proof. exact (MK_COMB (@lem2398681) (@lem2398680 a)). Qed.
Lemma lem2398683 (b : int) (c : int) : (term292 b c) = (term293 b c).
Proof. exact (@lem1982753 (real_of_int b) (term89 b) (term89 c) (term183 c)). Qed.
Lemma lem2398684 (b : int) : (term230 b) = (term231 b).
Proof. exact (@lem1982715 term88 (real_of_int b)). Qed.
Lemma lem2398686 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2398687 : term27 = term109.
Proof. exact (@lem2398686 term28). Qed.
Lemma lem2398689 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2398690 : term88 = term94.
Proof. exact (@lem2398689 term28). Qed.
Lemma lem2398691 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398692 : term232 = term233.
Proof. exact (MK_COMB (@lem2398691) (@lem2398690)). Qed.
Lemma lem2398693 : term234 = term235.
Proof. exact (MK_COMB (@lem2398692) (@lem2398687)). Qed.
Lemma lem2398694 : term236.
Proof. exact (@lem1981473 term88 term27 term27 term27 term81 term27). Qed.
Lemma lem2398696 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398697 : term199 = term206.
Proof. exact (@lem2398696 (NUMERAL 0) term28). Qed.
Lemma lem2398698 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398699 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398700 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398699 h1) (fun h1 : term206 = True => @lem2398698)). Qed.
Lemma lem2398701 : term206 = True.
Proof. exact (EQ_MP (@lem2398700) (@lem2398698)). Qed.
Lemma lem2398702 : term199 = True.
Proof. exact (TRANS (@lem2398697) (@lem2398701)). Qed.
Lemma lem2398703 : True = term199.
Proof. exact (SYM (@lem2398702)). Qed.
Lemma lem2398704 : term199.
Proof. exact (EQ_MP (@lem2398703) (@lem0)). Qed.
Lemma lem2398705 : term237.
Proof. exact (@lem2398694 (@lem2398704)). Qed.
Lemma lem2398707 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398708 : term199 = term206.
Proof. exact (@lem2398707 (NUMERAL 0) term28). Qed.
Lemma lem2398709 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398710 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398711 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398710 h1) (fun h1 : term206 = True => @lem2398709)). Qed.
Lemma lem2398712 : term206 = True.
Proof. exact (EQ_MP (@lem2398711) (@lem2398709)). Qed.
Lemma lem2398713 : term199 = True.
Proof. exact (TRANS (@lem2398708) (@lem2398712)). Qed.
Lemma lem2398714 : True = term199.
Proof. exact (SYM (@lem2398713)). Qed.
Lemma lem2398715 : term199.
Proof. exact (EQ_MP (@lem2398714) (@lem0)). Qed.
Lemma lem2398716 : term238.
Proof. exact (@lem2398705 (@lem2398715)). Qed.
Lemma lem2398718 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398719 : term199 = term206.
Proof. exact (@lem2398718 (NUMERAL 0) term28). Qed.
Lemma lem2398720 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398721 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398722 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398721 h1) (fun h1 : term206 = True => @lem2398720)). Qed.
Lemma lem2398723 : term206 = True.
Proof. exact (EQ_MP (@lem2398722) (@lem2398720)). Qed.
Lemma lem2398724 : term199 = True.
Proof. exact (TRANS (@lem2398719) (@lem2398723)). Qed.
Lemma lem2398725 : True = term199.
Proof. exact (SYM (@lem2398724)). Qed.
Lemma lem2398726 : term199.
Proof. exact (EQ_MP (@lem2398725) (@lem0)). Qed.
Lemma lem2398727 : term239.
Proof. exact (@lem2398716 (@lem2398726)). Qed.
Lemma lem2398729 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398730 : term102 = term103.
Proof. exact (@lem2398729 term28 term28). Qed.
Lemma lem2398731 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398732 : term105 = term28.
Proof. exact (EQ_MP (@lem2398731) (@lem940073)). Qed.
Lemma lem2398733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398734 : term103 = term27.
Proof. exact (MK_COMB (@lem2398733) (@lem2398732)). Qed.
Lemma lem2398735 : term102 = term27.
Proof. exact (TRANS (@lem2398730) (@lem2398734)). Qed.
Lemma lem2398737 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2398738 : term129 = term134.
Proof. exact (@lem2398737 term28 term28). Qed.
Lemma lem2398739 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398740 : term105 = term28.
Proof. exact (EQ_MP (@lem2398739) (@lem940073)). Qed.
Lemma lem2398741 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398742 : term103 = term27.
Proof. exact (MK_COMB (@lem2398741) (@lem2398740)). Qed.
Lemma lem2398743 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2398744 : term134 = term88.
Proof. exact (MK_COMB (@lem2398743) (@lem2398742)). Qed.
Lemma lem2398745 : term129 = term88.
Proof. exact (TRANS (@lem2398738) (@lem2398744)). Qed.
Lemma lem2398746 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398747 : term240 = term232.
Proof. exact (MK_COMB (@lem2398746) (@lem2398745)). Qed.
Lemma lem2398748 : term241 = term234.
Proof. exact (MK_COMB (@lem2398747) (@lem2398735)). Qed.
Lemma lem2398750 (m : nat) : (term242 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2398751 : term234 = term81.
Proof. exact (@lem2398750 term28). Qed.
Lemma lem2398752 : term241 = term81.
Proof. exact (TRANS (@lem2398748) (@lem2398751)). Qed.
Lemma lem2398753 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398754 : term243 = term244.
Proof. exact (MK_COMB (@lem2398753) (@lem2398752)). Qed.
Lemma lem2398755 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2398756 : term245 = term211.
Proof. exact (MK_COMB (@lem2398754) (@lem2398755)). Qed.
Lemma lem2398758 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398759 : term211 = term81.
Proof. exact (@lem2398758 term28). Qed.
Lemma lem2398760 : term245 = term81.
Proof. exact (TRANS (@lem2398756) (@lem2398759)). Qed.
Lemma lem2398762 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398763 : term102 = term103.
Proof. exact (@lem2398762 term28 term28). Qed.
Lemma lem2398764 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398765 : term105 = term28.
Proof. exact (EQ_MP (@lem2398764) (@lem940073)). Qed.
Lemma lem2398766 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398767 : term103 = term27.
Proof. exact (MK_COMB (@lem2398766) (@lem2398765)). Qed.
Lemma lem2398768 : term102 = term27.
Proof. exact (TRANS (@lem2398763) (@lem2398767)). Qed.
Lemma lem2398769 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem2398770 : term246 = term211.
Proof. exact (MK_COMB (@lem2398769) (@lem2398768)). Qed.
Lemma lem2398772 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398773 : term211 = term81.
Proof. exact (@lem2398772 term28). Qed.
Lemma lem2398774 : term246 = term81.
Proof. exact (TRANS (@lem2398770) (@lem2398773)). Qed.
Lemma lem2398775 : term81 = term246.
Proof. exact (SYM (@lem2398774)). Qed.
Lemma lem2398776 : term245 = term246.
Proof. exact (TRANS (@lem2398760) (@lem2398775)). Qed.
Lemma lem2398777 : term235 = term200.
Proof. exact (@lem2398727 (@lem2398776)). Qed.
Lemma lem2398778 : term234 = term200.
Proof. exact (TRANS (@lem2398693) (@lem2398777)). Qed.
Lemma lem2398780 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2398781 : term200 = term81.
Proof. exact (@lem2398780 term81). Qed.
Lemma lem2398782 : term234 = term81.
Proof. exact (TRANS (@lem2398778) (@lem2398781)). Qed.
Lemma lem2398783 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398784 : term247 = term244.
Proof. exact (MK_COMB (@lem2398783) (@lem2398782)). Qed.
Lemma lem2398785 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2398786 (b : int) : (term231 b) = (term248 b).
Proof. exact (MK_COMB (@lem2398784) (@lem2398785 b)). Qed.
Lemma lem2398787 (b : int) : (term230 b) = (term248 b).
Proof. exact (TRANS (@lem2398684 b) (@lem2398786 b)). Qed.
Lemma lem2398788 (b : int) : (term248 b) = term81.
Proof. exact (@lem1982719 (real_of_int b)). Qed.
Lemma lem2398789 (b : int) : (term230 b) = term81.
Proof. exact (TRANS (@lem2398787 b) (@lem2398788 b)). Qed.
Lemma lem2398790 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398791 (b : int) : (term249 b) = term250.
Proof. exact (MK_COMB (@lem2398790) (@lem2398789 b)). Qed.
Lemma lem2398792 (c : int) : (term294 c) = (term295 c).
Proof. exact (@lem1982763 (term89 c) (real_of_int c) term88). Qed.
Lemma lem2398793 (c : int) : (term253 c) = (term231 c).
Proof. exact (@lem1982713 term88 (real_of_int c)). Qed.
Lemma lem2398795 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2398796 : term27 = term109.
Proof. exact (@lem2398795 term28). Qed.
Lemma lem2398798 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2398799 : term88 = term94.
Proof. exact (@lem2398798 term28). Qed.
Lemma lem2398800 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398801 : term232 = term233.
Proof. exact (MK_COMB (@lem2398800) (@lem2398799)). Qed.
Lemma lem2398802 : term234 = term235.
Proof. exact (MK_COMB (@lem2398801) (@lem2398796)). Qed.
Lemma lem2398803 : term236.
Proof. exact (@lem1981473 term88 term27 term27 term27 term81 term27). Qed.
Lemma lem2398805 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398806 : term199 = term206.
Proof. exact (@lem2398805 (NUMERAL 0) term28). Qed.
Lemma lem2398807 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398808 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398809 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398808 h1) (fun h1 : term206 = True => @lem2398807)). Qed.
Lemma lem2398810 : term206 = True.
Proof. exact (EQ_MP (@lem2398809) (@lem2398807)). Qed.
Lemma lem2398811 : term199 = True.
Proof. exact (TRANS (@lem2398806) (@lem2398810)). Qed.
Lemma lem2398812 : True = term199.
Proof. exact (SYM (@lem2398811)). Qed.
Lemma lem2398813 : term199.
Proof. exact (EQ_MP (@lem2398812) (@lem0)). Qed.
Lemma lem2398814 : term237.
Proof. exact (@lem2398803 (@lem2398813)). Qed.
Lemma lem2398816 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398817 : term199 = term206.
Proof. exact (@lem2398816 (NUMERAL 0) term28). Qed.
Lemma lem2398818 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398819 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398820 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398819 h1) (fun h1 : term206 = True => @lem2398818)). Qed.
Lemma lem2398821 : term206 = True.
Proof. exact (EQ_MP (@lem2398820) (@lem2398818)). Qed.
Lemma lem2398822 : term199 = True.
Proof. exact (TRANS (@lem2398817) (@lem2398821)). Qed.
Lemma lem2398823 : True = term199.
Proof. exact (SYM (@lem2398822)). Qed.
Lemma lem2398824 : term199.
Proof. exact (EQ_MP (@lem2398823) (@lem0)). Qed.
Lemma lem2398825 : term238.
Proof. exact (@lem2398814 (@lem2398824)). Qed.
Lemma lem2398827 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398828 : term199 = term206.
Proof. exact (@lem2398827 (NUMERAL 0) term28). Qed.
Lemma lem2398829 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398830 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398831 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398830 h1) (fun h1 : term206 = True => @lem2398829)). Qed.
Lemma lem2398832 : term206 = True.
Proof. exact (EQ_MP (@lem2398831) (@lem2398829)). Qed.
Lemma lem2398833 : term199 = True.
Proof. exact (TRANS (@lem2398828) (@lem2398832)). Qed.
Lemma lem2398834 : True = term199.
Proof. exact (SYM (@lem2398833)). Qed.
Lemma lem2398835 : term199.
Proof. exact (EQ_MP (@lem2398834) (@lem0)). Qed.
Lemma lem2398836 : term239.
Proof. exact (@lem2398825 (@lem2398835)). Qed.
Lemma lem2398838 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398839 : term102 = term103.
Proof. exact (@lem2398838 term28 term28). Qed.
Lemma lem2398840 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398841 : term105 = term28.
Proof. exact (EQ_MP (@lem2398840) (@lem940073)). Qed.
Lemma lem2398842 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398843 : term103 = term27.
Proof. exact (MK_COMB (@lem2398842) (@lem2398841)). Qed.
Lemma lem2398844 : term102 = term27.
Proof. exact (TRANS (@lem2398839) (@lem2398843)). Qed.
Lemma lem2398846 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2398847 : term129 = term134.
Proof. exact (@lem2398846 term28 term28). Qed.
Lemma lem2398848 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398849 : term105 = term28.
Proof. exact (EQ_MP (@lem2398848) (@lem940073)). Qed.
Lemma lem2398850 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398851 : term103 = term27.
Proof. exact (MK_COMB (@lem2398850) (@lem2398849)). Qed.
Lemma lem2398852 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2398853 : term134 = term88.
Proof. exact (MK_COMB (@lem2398852) (@lem2398851)). Qed.
Lemma lem2398854 : term129 = term88.
Proof. exact (TRANS (@lem2398847) (@lem2398853)). Qed.
Lemma lem2398855 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398856 : term240 = term232.
Proof. exact (MK_COMB (@lem2398855) (@lem2398854)). Qed.
Lemma lem2398857 : term241 = term234.
Proof. exact (MK_COMB (@lem2398856) (@lem2398844)). Qed.
Lemma lem2398859 (m : nat) : (term242 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2398860 : term234 = term81.
Proof. exact (@lem2398859 term28). Qed.
Lemma lem2398861 : term241 = term81.
Proof. exact (TRANS (@lem2398857) (@lem2398860)). Qed.
Lemma lem2398862 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398863 : term243 = term244.
Proof. exact (MK_COMB (@lem2398862) (@lem2398861)). Qed.
Lemma lem2398864 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2398865 : term245 = term211.
Proof. exact (MK_COMB (@lem2398863) (@lem2398864)). Qed.
Lemma lem2398867 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398868 : term211 = term81.
Proof. exact (@lem2398867 term28). Qed.
Lemma lem2398869 : term245 = term81.
Proof. exact (TRANS (@lem2398865) (@lem2398868)). Qed.
Lemma lem2398871 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2398872 : term102 = term103.
Proof. exact (@lem2398871 term28 term28). Qed.
Lemma lem2398873 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398874 : term105 = term28.
Proof. exact (EQ_MP (@lem2398873) (@lem940073)). Qed.
Lemma lem2398875 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398876 : term103 = term27.
Proof. exact (MK_COMB (@lem2398875) (@lem2398874)). Qed.
Lemma lem2398877 : term102 = term27.
Proof. exact (TRANS (@lem2398872) (@lem2398876)). Qed.
Lemma lem2398878 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem2398879 : term246 = term211.
Proof. exact (MK_COMB (@lem2398878) (@lem2398877)). Qed.
Lemma lem2398881 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398882 : term211 = term81.
Proof. exact (@lem2398881 term28). Qed.
Lemma lem2398883 : term246 = term81.
Proof. exact (TRANS (@lem2398879) (@lem2398882)). Qed.
Lemma lem2398884 : term81 = term246.
Proof. exact (SYM (@lem2398883)). Qed.
Lemma lem2398885 : term245 = term246.
Proof. exact (TRANS (@lem2398869) (@lem2398884)). Qed.
Lemma lem2398886 : term235 = term200.
Proof. exact (@lem2398836 (@lem2398885)). Qed.
Lemma lem2398887 : term234 = term200.
Proof. exact (TRANS (@lem2398802) (@lem2398886)). Qed.
Lemma lem2398889 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2398890 : term200 = term81.
Proof. exact (@lem2398889 term81). Qed.
Lemma lem2398891 : term234 = term81.
Proof. exact (TRANS (@lem2398887) (@lem2398890)). Qed.
Lemma lem2398892 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2398893 : term247 = term244.
Proof. exact (MK_COMB (@lem2398892) (@lem2398891)). Qed.
Lemma lem2398894 (c : int) : (real_of_int c) = (real_of_int c).
Proof. exact (eq_refl (real_of_int c)). Qed.
Lemma lem2398895 (c : int) : (term231 c) = (term248 c).
Proof. exact (MK_COMB (@lem2398893) (@lem2398894 c)). Qed.
Lemma lem2398896 (c : int) : (term253 c) = (term248 c).
Proof. exact (TRANS (@lem2398793 c) (@lem2398895 c)). Qed.
Lemma lem2398897 (c : int) : (term248 c) = term81.
Proof. exact (@lem1982719 (real_of_int c)). Qed.
Lemma lem2398898 (c : int) : (term253 c) = term81.
Proof. exact (TRANS (@lem2398896 c) (@lem2398897 c)). Qed.
Lemma lem2398899 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2398900 (c : int) : (term254 c) = term250.
Proof. exact (MK_COMB (@lem2398899) (@lem2398898 c)). Qed.
Lemma lem2398901 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem2398902 (c : int) : (term295 c) = term257.
Proof. exact (MK_COMB (@lem2398900 c) (@lem2398901)). Qed.
Lemma lem2398903 (c : int) : (term294 c) = term257.
Proof. exact (TRANS (@lem2398792 c) (@lem2398902 c)). Qed.
Lemma lem2398904 : term257 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem2398905 (c : int) : (term294 c) = term88.
Proof. exact (TRANS (@lem2398903 c) (@lem2398904)). Qed.
Lemma lem2398906 (b : int) (c : int) : (term293 b c) = term257.
Proof. exact (MK_COMB (@lem2398791 b) (@lem2398905 c)). Qed.
Lemma lem2398907 (b : int) (c : int) : (term292 b c) = term257.
Proof. exact (TRANS (@lem2398683 b c) (@lem2398906 b c)). Qed.
Lemma lem2398908 : term257 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem2398909 (b : int) (c : int) : (term292 b c) = term88.
Proof. exact (TRANS (@lem2398907 b c) (@lem2398908)). Qed.
Lemma lem2398910 (a : int) (b : int) (c : int) : (term291 a b c) = term257.
Proof. exact (MK_COMB (@lem2398682 a) (@lem2398909 b c)). Qed.
Lemma lem2398911 (a : int) (b : int) (c : int) : (term290 a b c) = term257.
Proof. exact (TRANS (@lem2398574 a b c) (@lem2398910 a b c)). Qed.
Lemma lem2398912 : term257 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem2398913 (a : int) (b : int) (c : int) : (term290 a b c) = term88.
Proof. exact (TRANS (@lem2398911 a b c) (@lem2398912)). Qed.
Lemma lem2398914 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2398915 (a : int) (b : int) (c : int) : (term296 a b c) = term259.
Proof. exact (MK_COMB (@lem2398914) (@lem2398913 a b c)). Qed.
Lemma lem2398916 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2398917 (a : int) (b : int) (c : int) : (term289 a b c) = term260.
Proof. exact (MK_COMB (@lem2398915 a b c) (@lem2398916)). Qed.
Lemma lem2398918 (a : int) (b : int) (c : int) (h1 : term273 a b c) : term260.
Proof. exact (EQ_MP (@lem2398917 a b c) (@lem2398573 a b c h1)). Qed.
Lemma lem2398920 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2398921 : term260 = term261.
Proof. exact (@lem2398920 term81 term88). Qed.
Lemma lem2398923 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2398924 : term88 = term94.
Proof. exact (@lem2398923 term28). Qed.
Lemma lem2398926 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2398927 : term81 = term200.
Proof. exact (@lem2398926 (NUMERAL 0)). Qed.
Lemma lem2398928 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2398929 : term262 = term263.
Proof. exact (MK_COMB (@lem2398928) (@lem2398927)). Qed.
Lemma lem2398930 : term261 = term264.
Proof. exact (MK_COMB (@lem2398929) (@lem2398924)). Qed.
Lemma lem2398931 : term265.
Proof. exact (@lem1980026 term81 term27 term88 term27). Qed.
Lemma lem2398933 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398934 : term199 = term206.
Proof. exact (@lem2398933 (NUMERAL 0) term28). Qed.
Lemma lem2398935 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398936 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398937 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398936 h1) (fun h1 : term206 = True => @lem2398935)). Qed.
Lemma lem2398938 : term206 = True.
Proof. exact (EQ_MP (@lem2398937) (@lem2398935)). Qed.
Lemma lem2398939 : term199 = True.
Proof. exact (TRANS (@lem2398934) (@lem2398938)). Qed.
Lemma lem2398940 : True = term199.
Proof. exact (SYM (@lem2398939)). Qed.
Lemma lem2398941 : term199.
Proof. exact (EQ_MP (@lem2398940) (@lem0)). Qed.
Lemma lem2398942 : term266.
Proof. exact (@lem2398931 (@lem2398941)). Qed.
Lemma lem2398944 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2398945 : term199 = term206.
Proof. exact (@lem2398944 (NUMERAL 0) term28). Qed.
Lemma lem2398946 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398947 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2398948 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398947 h1) (fun h1 : term206 = True => @lem2398946)). Qed.
Lemma lem2398949 : term206 = True.
Proof. exact (EQ_MP (@lem2398948) (@lem2398946)). Qed.
Lemma lem2398950 : term199 = True.
Proof. exact (TRANS (@lem2398945) (@lem2398949)). Qed.
Lemma lem2398951 : True = term199.
Proof. exact (SYM (@lem2398950)). Qed.
Lemma lem2398952 : term199.
Proof. exact (EQ_MP (@lem2398951) (@lem0)). Qed.
Lemma lem2398953 : term264 = term267.
Proof. exact (@lem2398942 (@lem2398952)). Qed.
Lemma lem2398955 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2398956 : term129 = term134.
Proof. exact (@lem2398955 term28 term28). Qed.
Lemma lem2398957 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2398958 : term105 = term28.
Proof. exact (EQ_MP (@lem2398957) (@lem940073)). Qed.
Lemma lem2398959 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2398960 : term103 = term27.
Proof. exact (MK_COMB (@lem2398959) (@lem2398958)). Qed.
Lemma lem2398961 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2398962 : term134 = term88.
Proof. exact (MK_COMB (@lem2398961) (@lem2398960)). Qed.
Lemma lem2398963 : term129 = term88.
Proof. exact (TRANS (@lem2398956) (@lem2398962)). Qed.
Lemma lem2398965 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2398966 : term211 = term81.
Proof. exact (@lem2398965 term28). Qed.
Lemma lem2398967 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2398968 : term268 = term262.
Proof. exact (MK_COMB (@lem2398967) (@lem2398966)). Qed.
Lemma lem2398969 : term267 = term261.
Proof. exact (MK_COMB (@lem2398968) (@lem2398963)). Qed.
Lemma lem2398971 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2398972 : term261 = term271.
Proof. exact (@lem2398971 (NUMERAL 0) term28). Qed.
Lemma lem2398973 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2398974 (h1 : term207 = (BIT1 0)) : (term28 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2398975 : (term207 = (BIT1 0)) = ((term28 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2398974 h1) (fun h1 : (term28 = (NUMERAL 0)) = False => @lem2398973)). Qed.
Lemma lem2398976 : (term28 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2398975) (@lem2398973)). Qed.
Lemma lem2398977 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2398978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2398979 : term272 = (and True).
Proof. exact (MK_COMB (@lem2398978) (@lem2398977)). Qed.
Lemma lem2398980 : term271 = (True /\ False).
Proof. exact (MK_COMB (@lem2398979) (@lem2398976)). Qed.
Lemma lem2398982 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2398983 : term271 = False.
Proof. exact (TRANS (@lem2398980) (@lem2398982)). Qed.
Lemma lem2398984 : term261 = False.
Proof. exact (TRANS (@lem2398972) (@lem2398983)). Qed.
Lemma lem2398985 : term267 = False.
Proof. exact (TRANS (@lem2398969) (@lem2398984)). Qed.
Lemma lem2398986 : term264 = False.
Proof. exact (TRANS (@lem2398953) (@lem2398985)). Qed.
Lemma lem2398987 : term261 = False.
Proof. exact (TRANS (@lem2398930) (@lem2398986)). Qed.
Lemma lem2398988 : term260 = False.
Proof. exact (TRANS (@lem2398921) (@lem2398987)). Qed.
Lemma lem2398989 (a : int) (b : int) (c : int) (h1 : term273 a b c) : False.
Proof. exact (EQ_MP (@lem2398988) (@lem2398918 a b c h1)). Qed.
Lemma lem2398990 (a : int) (b : int) (c : int) (h1 : term194 a b c) : False.
Proof. exact (or_elim (@lem2397913 a b c h1) (fun h0 : term197 a b c => @lem2398424 a b c h0) (fun h0 : term273 a b c => @lem2398989 a b c h0)). Qed.
Lemma lem2398991 (a : int) (b : int) (c : int) (h1 : term193 a b c) : term193 a b c.
Proof. exact (h1). Qed.
Lemma lem2398992 (a : int) (b : int) (c : int) (h1 : term297 a b c) : term297 a b c.
Proof. exact (h1). Qed.
Lemma lem2398993 (a : int) (b : int) (c : int) (h1 : term297 a b c) : (term116 a b c) = term81.
Proof. exact (proj2 (@lem2398992 a b c h1)). Qed.
Lemma lem2398994 (a : int) (b : int) (c : int) (h1 : term297 a b c) : term143 a b c.
Proof. exact (proj1 (@lem2398992 a b c h1)). Qed.
Lemma lem2398996 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2398997 : term198 = term199.
Proof. exact (@lem2398996 term81 term27). Qed.
Lemma lem2398999 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2399000 : term27 = term109.
Proof. exact (@lem2398999 term28). Qed.
Lemma lem2399002 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2399003 : term81 = term200.
Proof. exact (@lem2399002 (NUMERAL 0)). Qed.
Lemma lem2399004 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2399005 : term201 = term202.
Proof. exact (MK_COMB (@lem2399004) (@lem2399003)). Qed.
Lemma lem2399006 : term199 = term203.
Proof. exact (MK_COMB (@lem2399005) (@lem2399000)). Qed.
Lemma lem2399007 : term204.
Proof. exact (@lem1980255 term81 term27 term27 term27). Qed.
Lemma lem2399009 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399010 : term199 = term206.
Proof. exact (@lem2399009 (NUMERAL 0) term28). Qed.
Lemma lem2399011 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399012 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399013 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399012 h1) (fun h1 : term206 = True => @lem2399011)). Qed.
Lemma lem2399014 : term206 = True.
Proof. exact (EQ_MP (@lem2399013) (@lem2399011)). Qed.
Lemma lem2399015 : term199 = True.
Proof. exact (TRANS (@lem2399010) (@lem2399014)). Qed.
Lemma lem2399016 : True = term199.
Proof. exact (SYM (@lem2399015)). Qed.
Lemma lem2399017 : term199.
Proof. exact (EQ_MP (@lem2399016) (@lem0)). Qed.
Lemma lem2399018 : term208.
Proof. exact (@lem2399007 (@lem2399017)). Qed.
Lemma lem2399020 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399021 : term199 = term206.
Proof. exact (@lem2399020 (NUMERAL 0) term28). Qed.
Lemma lem2399022 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399023 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399024 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399023 h1) (fun h1 : term206 = True => @lem2399022)). Qed.
Lemma lem2399025 : term206 = True.
Proof. exact (EQ_MP (@lem2399024) (@lem2399022)). Qed.
Lemma lem2399026 : term199 = True.
Proof. exact (TRANS (@lem2399021) (@lem2399025)). Qed.
Lemma lem2399027 : True = term199.
Proof. exact (SYM (@lem2399026)). Qed.
Lemma lem2399028 : term199.
Proof. exact (EQ_MP (@lem2399027) (@lem0)). Qed.
Lemma lem2399029 : term203 = term209.
Proof. exact (@lem2399018 (@lem2399028)). Qed.
Lemma lem2399031 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399032 : term102 = term103.
Proof. exact (@lem2399031 term28 term28). Qed.
Lemma lem2399033 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399034 : term105 = term28.
Proof. exact (EQ_MP (@lem2399033) (@lem940073)). Qed.
Lemma lem2399035 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399036 : term103 = term27.
Proof. exact (MK_COMB (@lem2399035) (@lem2399034)). Qed.
Lemma lem2399037 : term102 = term27.
Proof. exact (TRANS (@lem2399032) (@lem2399036)). Qed.
Lemma lem2399039 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399040 : term211 = term81.
Proof. exact (@lem2399039 term28). Qed.
Lemma lem2399041 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2399042 : term212 = term201.
Proof. exact (MK_COMB (@lem2399041) (@lem2399040)). Qed.
Lemma lem2399043 : term209 = term199.
Proof. exact (MK_COMB (@lem2399042) (@lem2399037)). Qed.
Lemma lem2399045 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399046 : term199 = term206.
Proof. exact (@lem2399045 (NUMERAL 0) term28). Qed.
Lemma lem2399047 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399048 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399049 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399048 h1) (fun h1 : term206 = True => @lem2399047)). Qed.
Lemma lem2399050 : term206 = True.
Proof. exact (EQ_MP (@lem2399049) (@lem2399047)). Qed.
Lemma lem2399051 : term199 = True.
Proof. exact (TRANS (@lem2399046) (@lem2399050)). Qed.
Lemma lem2399052 : term209 = True.
Proof. exact (TRANS (@lem2399043) (@lem2399051)). Qed.
Lemma lem2399053 : term203 = True.
Proof. exact (TRANS (@lem2399029) (@lem2399052)). Qed.
Lemma lem2399054 : term199 = True.
Proof. exact (TRANS (@lem2399006) (@lem2399053)). Qed.
Lemma lem2399055 : term198 = True.
Proof. exact (TRANS (@lem2398997) (@lem2399054)). Qed.
Lemma lem2399056 : True = term198.
Proof. exact (SYM (@lem2399055)). Qed.
Lemma lem2399057 : term198.
Proof. exact (EQ_MP (@lem2399056) (@lem0)). Qed.
Lemma lem2399058 (a : int) (b : int) (c : int) (h1 : term297 a b c) : term213 a b c.
Proof. exact (conj (@lem2399057) (@lem2398994 a b c h1)). Qed.
Lemma lem2399060 (x : real) (y : real) : term214 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2399061 (a : int) (b : int) (c : int) : term215 a b c.
Proof. exact (@lem2399060 term27 (term140 a b c)). Qed.
Lemma lem2399062 (a : int) (b : int) (c : int) (h1 : term297 a b c) : term216 a b c.
Proof. exact (@lem2399061 a b c (@lem2399058 a b c h1)). Qed.
Lemma lem2399063 (a : int) (b : int) (c : int) : (term217 a b c) = (term140 a b c).
Proof. exact (@lem1982733 (term140 a b c)). Qed.
Lemma lem2399064 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2399065 (a : int) (b : int) (c : int) : (term218 a b c) = (term142 a b c).
Proof. exact (MK_COMB (@lem2399064) (@lem2399063 a b c)). Qed.
Lemma lem2399066 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2399067 (a : int) (b : int) (c : int) : (term216 a b c) = (term143 a b c).
Proof. exact (MK_COMB (@lem2399065 a b c) (@lem2399066)). Qed.
Lemma lem2399068 (a : int) (b : int) (c : int) (h1 : term297 a b c) : term143 a b c.
Proof. exact (EQ_MP (@lem2399067 a b c) (@lem2399062 a b c h1)). Qed.
Lemma lem2399070 (y : real) : term219 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2399071 (a : int) (b : int) (c : int) : term220 a b c.
Proof. exact (@lem2399070 (term116 a b c)). Qed.
Lemma lem2399072 (a : int) (b : int) (c : int) (h1 : term297 a b c) : term221 a b c.
Proof. exact (@lem2399071 a b c (@lem2398993 a b c h1)). Qed.
Lemma lem2399073 (a : int) (b : int) (c : int) (h1 : term297 a b c) : term222 a b c.
Proof. exact (@lem2399072 a b c h1 term27). Qed.
Lemma lem2399074 (a : int) (b : int) (c : int) : (term222 a b c) = ((term223 a b c) = term81).
Proof. exact (eq_refl (term222 a b c)). Qed.
Lemma lem2399075 (a : int) (b : int) (c : int) (h1 : term297 a b c) : (term223 a b c) = term81.
Proof. exact (EQ_MP (@lem2399074 a b c) (@lem2399073 a b c h1)). Qed.
Lemma lem2399076 (a : int) (b : int) (c : int) : (term223 a b c) = (term116 a b c).
Proof. exact (@lem1982733 (term116 a b c)). Qed.
Lemma lem2399077 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2399078 (a : int) (b : int) (c : int) : (term224 a b c) = (term118 a b c).
Proof. exact (MK_COMB (@lem2399077) (@lem2399076 a b c)). Qed.
Lemma lem2399079 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2399080 (a : int) (b : int) (c : int) : ((term223 a b c) = term81) = ((term116 a b c) = term81).
Proof. exact (MK_COMB (@lem2399078 a b c) (@lem2399079)). Qed.
Lemma lem2399081 (a : int) (b : int) (c : int) (h1 : term297 a b c) : (term116 a b c) = term81.
Proof. exact (EQ_MP (@lem2399080 a b c) (@lem2399075 a b c h1)). Qed.
Lemma lem2399082 (a : int) (b : int) (c : int) (h1 : term297 a b c) : term197 a b c.
Proof. exact (conj (@lem2399081 a b c h1) (@lem2399068 a b c h1)). Qed.
Lemma lem2399084 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2399085 (a : int) (b : int) (c : int) : term226 a b c.
Proof. exact (@lem2399084 (term116 a b c) (term140 a b c)). Qed.
Lemma lem2399086 (a : int) (b : int) (c : int) (h1 : term297 a b c) : term227 a b c.
Proof. exact (@lem2399085 a b c (@lem2399082 a b c h1)). Qed.
Lemma lem2399087 (a : int) (b : int) (c : int) : (term228 a b c) = (term229 a b c).
Proof. exact (@lem1982753 (real_of_int a) (term89 a) (term115 b c) (term150 b c)). Qed.
Lemma lem2399088 (a : int) : (term230 a) = (term231 a).
Proof. exact (@lem1982715 term88 (real_of_int a)). Qed.
Lemma lem2399090 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2399091 : term27 = term109.
Proof. exact (@lem2399090 term28). Qed.
Lemma lem2399093 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2399094 : term88 = term94.
Proof. exact (@lem2399093 term28). Qed.
Lemma lem2399095 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399096 : term232 = term233.
Proof. exact (MK_COMB (@lem2399095) (@lem2399094)). Qed.
Lemma lem2399097 : term234 = term235.
Proof. exact (MK_COMB (@lem2399096) (@lem2399091)). Qed.
Lemma lem2399098 : term236.
Proof. exact (@lem1981473 term88 term27 term27 term27 term81 term27). Qed.
Lemma lem2399100 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399101 : term199 = term206.
Proof. exact (@lem2399100 (NUMERAL 0) term28). Qed.
Lemma lem2399102 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399103 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399104 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399103 h1) (fun h1 : term206 = True => @lem2399102)). Qed.
Lemma lem2399105 : term206 = True.
Proof. exact (EQ_MP (@lem2399104) (@lem2399102)). Qed.
Lemma lem2399106 : term199 = True.
Proof. exact (TRANS (@lem2399101) (@lem2399105)). Qed.
Lemma lem2399107 : True = term199.
Proof. exact (SYM (@lem2399106)). Qed.
Lemma lem2399108 : term199.
Proof. exact (EQ_MP (@lem2399107) (@lem0)). Qed.
Lemma lem2399109 : term237.
Proof. exact (@lem2399098 (@lem2399108)). Qed.
Lemma lem2399111 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399112 : term199 = term206.
Proof. exact (@lem2399111 (NUMERAL 0) term28). Qed.
Lemma lem2399113 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399114 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399115 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399114 h1) (fun h1 : term206 = True => @lem2399113)). Qed.
Lemma lem2399116 : term206 = True.
Proof. exact (EQ_MP (@lem2399115) (@lem2399113)). Qed.
Lemma lem2399117 : term199 = True.
Proof. exact (TRANS (@lem2399112) (@lem2399116)). Qed.
Lemma lem2399118 : True = term199.
Proof. exact (SYM (@lem2399117)). Qed.
Lemma lem2399119 : term199.
Proof. exact (EQ_MP (@lem2399118) (@lem0)). Qed.
Lemma lem2399120 : term238.
Proof. exact (@lem2399109 (@lem2399119)). Qed.
Lemma lem2399122 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399123 : term199 = term206.
Proof. exact (@lem2399122 (NUMERAL 0) term28). Qed.
Lemma lem2399124 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399125 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399126 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399125 h1) (fun h1 : term206 = True => @lem2399124)). Qed.
Lemma lem2399127 : term206 = True.
Proof. exact (EQ_MP (@lem2399126) (@lem2399124)). Qed.
Lemma lem2399128 : term199 = True.
Proof. exact (TRANS (@lem2399123) (@lem2399127)). Qed.
Lemma lem2399129 : True = term199.
Proof. exact (SYM (@lem2399128)). Qed.
Lemma lem2399130 : term199.
Proof. exact (EQ_MP (@lem2399129) (@lem0)). Qed.
Lemma lem2399131 : term239.
Proof. exact (@lem2399120 (@lem2399130)). Qed.
Lemma lem2399133 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399134 : term102 = term103.
Proof. exact (@lem2399133 term28 term28). Qed.
Lemma lem2399135 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399136 : term105 = term28.
Proof. exact (EQ_MP (@lem2399135) (@lem940073)). Qed.
Lemma lem2399137 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399138 : term103 = term27.
Proof. exact (MK_COMB (@lem2399137) (@lem2399136)). Qed.
Lemma lem2399139 : term102 = term27.
Proof. exact (TRANS (@lem2399134) (@lem2399138)). Qed.
Lemma lem2399141 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2399142 : term129 = term134.
Proof. exact (@lem2399141 term28 term28). Qed.
Lemma lem2399143 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399144 : term105 = term28.
Proof. exact (EQ_MP (@lem2399143) (@lem940073)). Qed.
Lemma lem2399145 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399146 : term103 = term27.
Proof. exact (MK_COMB (@lem2399145) (@lem2399144)). Qed.
Lemma lem2399147 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2399148 : term134 = term88.
Proof. exact (MK_COMB (@lem2399147) (@lem2399146)). Qed.
Lemma lem2399149 : term129 = term88.
Proof. exact (TRANS (@lem2399142) (@lem2399148)). Qed.
Lemma lem2399150 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399151 : term240 = term232.
Proof. exact (MK_COMB (@lem2399150) (@lem2399149)). Qed.
Lemma lem2399152 : term241 = term234.
Proof. exact (MK_COMB (@lem2399151) (@lem2399139)). Qed.
Lemma lem2399154 (m : nat) : (term242 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2399155 : term234 = term81.
Proof. exact (@lem2399154 term28). Qed.
Lemma lem2399156 : term241 = term81.
Proof. exact (TRANS (@lem2399152) (@lem2399155)). Qed.
Lemma lem2399157 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399158 : term243 = term244.
Proof. exact (MK_COMB (@lem2399157) (@lem2399156)). Qed.
Lemma lem2399159 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2399160 : term245 = term211.
Proof. exact (MK_COMB (@lem2399158) (@lem2399159)). Qed.
Lemma lem2399162 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399163 : term211 = term81.
Proof. exact (@lem2399162 term28). Qed.
Lemma lem2399164 : term245 = term81.
Proof. exact (TRANS (@lem2399160) (@lem2399163)). Qed.
Lemma lem2399166 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399167 : term102 = term103.
Proof. exact (@lem2399166 term28 term28). Qed.
Lemma lem2399168 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399169 : term105 = term28.
Proof. exact (EQ_MP (@lem2399168) (@lem940073)). Qed.
Lemma lem2399170 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399171 : term103 = term27.
Proof. exact (MK_COMB (@lem2399170) (@lem2399169)). Qed.
Lemma lem2399172 : term102 = term27.
Proof. exact (TRANS (@lem2399167) (@lem2399171)). Qed.
Lemma lem2399173 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem2399174 : term246 = term211.
Proof. exact (MK_COMB (@lem2399173) (@lem2399172)). Qed.
Lemma lem2399176 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399177 : term211 = term81.
Proof. exact (@lem2399176 term28). Qed.
Lemma lem2399178 : term246 = term81.
Proof. exact (TRANS (@lem2399174) (@lem2399177)). Qed.
Lemma lem2399179 : term81 = term246.
Proof. exact (SYM (@lem2399178)). Qed.
Lemma lem2399180 : term245 = term246.
Proof. exact (TRANS (@lem2399164) (@lem2399179)). Qed.
Lemma lem2399181 : term235 = term200.
Proof. exact (@lem2399131 (@lem2399180)). Qed.
Lemma lem2399182 : term234 = term200.
Proof. exact (TRANS (@lem2399097) (@lem2399181)). Qed.
Lemma lem2399184 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2399185 : term200 = term81.
Proof. exact (@lem2399184 term81). Qed.
Lemma lem2399186 : term234 = term81.
Proof. exact (TRANS (@lem2399182) (@lem2399185)). Qed.
Lemma lem2399187 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399188 : term247 = term244.
Proof. exact (MK_COMB (@lem2399187) (@lem2399186)). Qed.
Lemma lem2399189 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2399190 (a : int) : (term231 a) = (term248 a).
Proof. exact (MK_COMB (@lem2399188) (@lem2399189 a)). Qed.
Lemma lem2399191 (a : int) : (term230 a) = (term248 a).
Proof. exact (TRANS (@lem2399088 a) (@lem2399190 a)). Qed.
Lemma lem2399192 (a : int) : (term248 a) = term81.
Proof. exact (@lem1982719 (real_of_int a)). Qed.
Lemma lem2399193 (a : int) : (term230 a) = term81.
Proof. exact (TRANS (@lem2399191 a) (@lem2399192 a)). Qed.
Lemma lem2399194 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399195 (a : int) : (term249 a) = term250.
Proof. exact (MK_COMB (@lem2399194) (@lem2399193 a)). Qed.
Lemma lem2399196 (b : int) (c : int) : (term251 b c) = (term252 b c).
Proof. exact (@lem1982753 (term89 b) (real_of_int b) (real_of_int c) (term137 c)). Qed.
Lemma lem2399197 (b : int) : (term253 b) = (term231 b).
Proof. exact (@lem1982713 term88 (real_of_int b)). Qed.
Lemma lem2399199 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2399200 : term27 = term109.
Proof. exact (@lem2399199 term28). Qed.
Lemma lem2399202 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2399203 : term88 = term94.
Proof. exact (@lem2399202 term28). Qed.
Lemma lem2399204 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399205 : term232 = term233.
Proof. exact (MK_COMB (@lem2399204) (@lem2399203)). Qed.
Lemma lem2399206 : term234 = term235.
Proof. exact (MK_COMB (@lem2399205) (@lem2399200)). Qed.
Lemma lem2399207 : term236.
Proof. exact (@lem1981473 term88 term27 term27 term27 term81 term27). Qed.
Lemma lem2399209 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399210 : term199 = term206.
Proof. exact (@lem2399209 (NUMERAL 0) term28). Qed.
Lemma lem2399211 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399212 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399213 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399212 h1) (fun h1 : term206 = True => @lem2399211)). Qed.
Lemma lem2399214 : term206 = True.
Proof. exact (EQ_MP (@lem2399213) (@lem2399211)). Qed.
Lemma lem2399215 : term199 = True.
Proof. exact (TRANS (@lem2399210) (@lem2399214)). Qed.
Lemma lem2399216 : True = term199.
Proof. exact (SYM (@lem2399215)). Qed.
Lemma lem2399217 : term199.
Proof. exact (EQ_MP (@lem2399216) (@lem0)). Qed.
Lemma lem2399218 : term237.
Proof. exact (@lem2399207 (@lem2399217)). Qed.
Lemma lem2399220 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399221 : term199 = term206.
Proof. exact (@lem2399220 (NUMERAL 0) term28). Qed.
Lemma lem2399222 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399223 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399224 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399223 h1) (fun h1 : term206 = True => @lem2399222)). Qed.
Lemma lem2399225 : term206 = True.
Proof. exact (EQ_MP (@lem2399224) (@lem2399222)). Qed.
Lemma lem2399226 : term199 = True.
Proof. exact (TRANS (@lem2399221) (@lem2399225)). Qed.
Lemma lem2399227 : True = term199.
Proof. exact (SYM (@lem2399226)). Qed.
Lemma lem2399228 : term199.
Proof. exact (EQ_MP (@lem2399227) (@lem0)). Qed.
Lemma lem2399229 : term238.
Proof. exact (@lem2399218 (@lem2399228)). Qed.
Lemma lem2399231 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399232 : term199 = term206.
Proof. exact (@lem2399231 (NUMERAL 0) term28). Qed.
Lemma lem2399233 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399234 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399235 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399234 h1) (fun h1 : term206 = True => @lem2399233)). Qed.
Lemma lem2399236 : term206 = True.
Proof. exact (EQ_MP (@lem2399235) (@lem2399233)). Qed.
Lemma lem2399237 : term199 = True.
Proof. exact (TRANS (@lem2399232) (@lem2399236)). Qed.
Lemma lem2399238 : True = term199.
Proof. exact (SYM (@lem2399237)). Qed.
Lemma lem2399239 : term199.
Proof. exact (EQ_MP (@lem2399238) (@lem0)). Qed.
Lemma lem2399240 : term239.
Proof. exact (@lem2399229 (@lem2399239)). Qed.
Lemma lem2399242 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399243 : term102 = term103.
Proof. exact (@lem2399242 term28 term28). Qed.
Lemma lem2399244 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399245 : term105 = term28.
Proof. exact (EQ_MP (@lem2399244) (@lem940073)). Qed.
Lemma lem2399246 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399247 : term103 = term27.
Proof. exact (MK_COMB (@lem2399246) (@lem2399245)). Qed.
Lemma lem2399248 : term102 = term27.
Proof. exact (TRANS (@lem2399243) (@lem2399247)). Qed.
Lemma lem2399250 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2399251 : term129 = term134.
Proof. exact (@lem2399250 term28 term28). Qed.
Lemma lem2399252 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399253 : term105 = term28.
Proof. exact (EQ_MP (@lem2399252) (@lem940073)). Qed.
Lemma lem2399254 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399255 : term103 = term27.
Proof. exact (MK_COMB (@lem2399254) (@lem2399253)). Qed.
Lemma lem2399256 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2399257 : term134 = term88.
Proof. exact (MK_COMB (@lem2399256) (@lem2399255)). Qed.
Lemma lem2399258 : term129 = term88.
Proof. exact (TRANS (@lem2399251) (@lem2399257)). Qed.
Lemma lem2399259 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399260 : term240 = term232.
Proof. exact (MK_COMB (@lem2399259) (@lem2399258)). Qed.
Lemma lem2399261 : term241 = term234.
Proof. exact (MK_COMB (@lem2399260) (@lem2399248)). Qed.
Lemma lem2399263 (m : nat) : (term242 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2399264 : term234 = term81.
Proof. exact (@lem2399263 term28). Qed.
Lemma lem2399265 : term241 = term81.
Proof. exact (TRANS (@lem2399261) (@lem2399264)). Qed.
Lemma lem2399266 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399267 : term243 = term244.
Proof. exact (MK_COMB (@lem2399266) (@lem2399265)). Qed.
Lemma lem2399268 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2399269 : term245 = term211.
Proof. exact (MK_COMB (@lem2399267) (@lem2399268)). Qed.
Lemma lem2399271 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399272 : term211 = term81.
Proof. exact (@lem2399271 term28). Qed.
Lemma lem2399273 : term245 = term81.
Proof. exact (TRANS (@lem2399269) (@lem2399272)). Qed.
Lemma lem2399275 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399276 : term102 = term103.
Proof. exact (@lem2399275 term28 term28). Qed.
Lemma lem2399277 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399278 : term105 = term28.
Proof. exact (EQ_MP (@lem2399277) (@lem940073)). Qed.
Lemma lem2399279 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399280 : term103 = term27.
Proof. exact (MK_COMB (@lem2399279) (@lem2399278)). Qed.
Lemma lem2399281 : term102 = term27.
Proof. exact (TRANS (@lem2399276) (@lem2399280)). Qed.
Lemma lem2399282 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem2399283 : term246 = term211.
Proof. exact (MK_COMB (@lem2399282) (@lem2399281)). Qed.
Lemma lem2399285 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399286 : term211 = term81.
Proof. exact (@lem2399285 term28). Qed.
Lemma lem2399287 : term246 = term81.
Proof. exact (TRANS (@lem2399283) (@lem2399286)). Qed.
Lemma lem2399288 : term81 = term246.
Proof. exact (SYM (@lem2399287)). Qed.
Lemma lem2399289 : term245 = term246.
Proof. exact (TRANS (@lem2399273) (@lem2399288)). Qed.
Lemma lem2399290 : term235 = term200.
Proof. exact (@lem2399240 (@lem2399289)). Qed.
Lemma lem2399291 : term234 = term200.
Proof. exact (TRANS (@lem2399206) (@lem2399290)). Qed.
Lemma lem2399293 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2399294 : term200 = term81.
Proof. exact (@lem2399293 term81). Qed.
Lemma lem2399295 : term234 = term81.
Proof. exact (TRANS (@lem2399291) (@lem2399294)). Qed.
Lemma lem2399296 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399297 : term247 = term244.
Proof. exact (MK_COMB (@lem2399296) (@lem2399295)). Qed.
Lemma lem2399298 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2399299 (b : int) : (term231 b) = (term248 b).
Proof. exact (MK_COMB (@lem2399297) (@lem2399298 b)). Qed.
Lemma lem2399300 (b : int) : (term253 b) = (term248 b).
Proof. exact (TRANS (@lem2399197 b) (@lem2399299 b)). Qed.
Lemma lem2399301 (b : int) : (term248 b) = term81.
Proof. exact (@lem1982719 (real_of_int b)). Qed.
Lemma lem2399302 (b : int) : (term253 b) = term81.
Proof. exact (TRANS (@lem2399300 b) (@lem2399301 b)). Qed.
Lemma lem2399303 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399304 (b : int) : (term254 b) = term250.
Proof. exact (MK_COMB (@lem2399303) (@lem2399302 b)). Qed.
Lemma lem2399305 (c : int) : (term255 c) = (term256 c).
Proof. exact (@lem1982763 (real_of_int c) (term89 c) term88). Qed.
Lemma lem2399306 (c : int) : (term230 c) = (term231 c).
Proof. exact (@lem1982715 term88 (real_of_int c)). Qed.
Lemma lem2399308 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2399309 : term27 = term109.
Proof. exact (@lem2399308 term28). Qed.
Lemma lem2399311 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2399312 : term88 = term94.
Proof. exact (@lem2399311 term28). Qed.
Lemma lem2399313 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399314 : term232 = term233.
Proof. exact (MK_COMB (@lem2399313) (@lem2399312)). Qed.
Lemma lem2399315 : term234 = term235.
Proof. exact (MK_COMB (@lem2399314) (@lem2399309)). Qed.
Lemma lem2399316 : term236.
Proof. exact (@lem1981473 term88 term27 term27 term27 term81 term27). Qed.
Lemma lem2399318 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399319 : term199 = term206.
Proof. exact (@lem2399318 (NUMERAL 0) term28). Qed.
Lemma lem2399320 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399321 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399322 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399321 h1) (fun h1 : term206 = True => @lem2399320)). Qed.
Lemma lem2399323 : term206 = True.
Proof. exact (EQ_MP (@lem2399322) (@lem2399320)). Qed.
Lemma lem2399324 : term199 = True.
Proof. exact (TRANS (@lem2399319) (@lem2399323)). Qed.
Lemma lem2399325 : True = term199.
Proof. exact (SYM (@lem2399324)). Qed.
Lemma lem2399326 : term199.
Proof. exact (EQ_MP (@lem2399325) (@lem0)). Qed.
Lemma lem2399327 : term237.
Proof. exact (@lem2399316 (@lem2399326)). Qed.
Lemma lem2399329 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399330 : term199 = term206.
Proof. exact (@lem2399329 (NUMERAL 0) term28). Qed.
Lemma lem2399331 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399332 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399333 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399332 h1) (fun h1 : term206 = True => @lem2399331)). Qed.
Lemma lem2399334 : term206 = True.
Proof. exact (EQ_MP (@lem2399333) (@lem2399331)). Qed.
Lemma lem2399335 : term199 = True.
Proof. exact (TRANS (@lem2399330) (@lem2399334)). Qed.
Lemma lem2399336 : True = term199.
Proof. exact (SYM (@lem2399335)). Qed.
Lemma lem2399337 : term199.
Proof. exact (EQ_MP (@lem2399336) (@lem0)). Qed.
Lemma lem2399338 : term238.
Proof. exact (@lem2399327 (@lem2399337)). Qed.
Lemma lem2399340 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399341 : term199 = term206.
Proof. exact (@lem2399340 (NUMERAL 0) term28). Qed.
Lemma lem2399342 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399343 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399344 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399343 h1) (fun h1 : term206 = True => @lem2399342)). Qed.
Lemma lem2399345 : term206 = True.
Proof. exact (EQ_MP (@lem2399344) (@lem2399342)). Qed.
Lemma lem2399346 : term199 = True.
Proof. exact (TRANS (@lem2399341) (@lem2399345)). Qed.
Lemma lem2399347 : True = term199.
Proof. exact (SYM (@lem2399346)). Qed.
Lemma lem2399348 : term199.
Proof. exact (EQ_MP (@lem2399347) (@lem0)). Qed.
Lemma lem2399349 : term239.
Proof. exact (@lem2399338 (@lem2399348)). Qed.
Lemma lem2399351 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399352 : term102 = term103.
Proof. exact (@lem2399351 term28 term28). Qed.
Lemma lem2399353 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399354 : term105 = term28.
Proof. exact (EQ_MP (@lem2399353) (@lem940073)). Qed.
Lemma lem2399355 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399356 : term103 = term27.
Proof. exact (MK_COMB (@lem2399355) (@lem2399354)). Qed.
Lemma lem2399357 : term102 = term27.
Proof. exact (TRANS (@lem2399352) (@lem2399356)). Qed.
Lemma lem2399359 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2399360 : term129 = term134.
Proof. exact (@lem2399359 term28 term28). Qed.
Lemma lem2399361 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399362 : term105 = term28.
Proof. exact (EQ_MP (@lem2399361) (@lem940073)). Qed.
Lemma lem2399363 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399364 : term103 = term27.
Proof. exact (MK_COMB (@lem2399363) (@lem2399362)). Qed.
Lemma lem2399365 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2399366 : term134 = term88.
Proof. exact (MK_COMB (@lem2399365) (@lem2399364)). Qed.
Lemma lem2399367 : term129 = term88.
Proof. exact (TRANS (@lem2399360) (@lem2399366)). Qed.
Lemma lem2399368 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399369 : term240 = term232.
Proof. exact (MK_COMB (@lem2399368) (@lem2399367)). Qed.
Lemma lem2399370 : term241 = term234.
Proof. exact (MK_COMB (@lem2399369) (@lem2399357)). Qed.
Lemma lem2399372 (m : nat) : (term242 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2399373 : term234 = term81.
Proof. exact (@lem2399372 term28). Qed.
Lemma lem2399374 : term241 = term81.
Proof. exact (TRANS (@lem2399370) (@lem2399373)). Qed.
Lemma lem2399375 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399376 : term243 = term244.
Proof. exact (MK_COMB (@lem2399375) (@lem2399374)). Qed.
Lemma lem2399377 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2399378 : term245 = term211.
Proof. exact (MK_COMB (@lem2399376) (@lem2399377)). Qed.
Lemma lem2399380 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399381 : term211 = term81.
Proof. exact (@lem2399380 term28). Qed.
Lemma lem2399382 : term245 = term81.
Proof. exact (TRANS (@lem2399378) (@lem2399381)). Qed.
Lemma lem2399384 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399385 : term102 = term103.
Proof. exact (@lem2399384 term28 term28). Qed.
Lemma lem2399386 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399387 : term105 = term28.
Proof. exact (EQ_MP (@lem2399386) (@lem940073)). Qed.
Lemma lem2399388 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399389 : term103 = term27.
Proof. exact (MK_COMB (@lem2399388) (@lem2399387)). Qed.
Lemma lem2399390 : term102 = term27.
Proof. exact (TRANS (@lem2399385) (@lem2399389)). Qed.
Lemma lem2399391 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem2399392 : term246 = term211.
Proof. exact (MK_COMB (@lem2399391) (@lem2399390)). Qed.
Lemma lem2399394 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399395 : term211 = term81.
Proof. exact (@lem2399394 term28). Qed.
Lemma lem2399396 : term246 = term81.
Proof. exact (TRANS (@lem2399392) (@lem2399395)). Qed.
Lemma lem2399397 : term81 = term246.
Proof. exact (SYM (@lem2399396)). Qed.
Lemma lem2399398 : term245 = term246.
Proof. exact (TRANS (@lem2399382) (@lem2399397)). Qed.
Lemma lem2399399 : term235 = term200.
Proof. exact (@lem2399349 (@lem2399398)). Qed.
Lemma lem2399400 : term234 = term200.
Proof. exact (TRANS (@lem2399315) (@lem2399399)). Qed.
Lemma lem2399402 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2399403 : term200 = term81.
Proof. exact (@lem2399402 term81). Qed.
Lemma lem2399404 : term234 = term81.
Proof. exact (TRANS (@lem2399400) (@lem2399403)). Qed.
Lemma lem2399405 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399406 : term247 = term244.
Proof. exact (MK_COMB (@lem2399405) (@lem2399404)). Qed.
Lemma lem2399407 (c : int) : (real_of_int c) = (real_of_int c).
Proof. exact (eq_refl (real_of_int c)). Qed.
Lemma lem2399408 (c : int) : (term231 c) = (term248 c).
Proof. exact (MK_COMB (@lem2399406) (@lem2399407 c)). Qed.
Lemma lem2399409 (c : int) : (term230 c) = (term248 c).
Proof. exact (TRANS (@lem2399306 c) (@lem2399408 c)). Qed.
Lemma lem2399410 (c : int) : (term248 c) = term81.
Proof. exact (@lem1982719 (real_of_int c)). Qed.
Lemma lem2399411 (c : int) : (term230 c) = term81.
Proof. exact (TRANS (@lem2399409 c) (@lem2399410 c)). Qed.
Lemma lem2399412 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399413 (c : int) : (term249 c) = term250.
Proof. exact (MK_COMB (@lem2399412) (@lem2399411 c)). Qed.
Lemma lem2399414 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem2399415 (c : int) : (term256 c) = term257.
Proof. exact (MK_COMB (@lem2399413 c) (@lem2399414)). Qed.
Lemma lem2399416 (c : int) : (term255 c) = term257.
Proof. exact (TRANS (@lem2399305 c) (@lem2399415 c)). Qed.
Lemma lem2399417 : term257 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem2399418 (c : int) : (term255 c) = term88.
Proof. exact (TRANS (@lem2399416 c) (@lem2399417)). Qed.
Lemma lem2399419 (b : int) (c : int) : (term252 b c) = term257.
Proof. exact (MK_COMB (@lem2399304 b) (@lem2399418 c)). Qed.
Lemma lem2399420 (b : int) (c : int) : (term251 b c) = term257.
Proof. exact (TRANS (@lem2399196 b c) (@lem2399419 b c)). Qed.
Lemma lem2399421 : term257 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem2399422 (b : int) (c : int) : (term251 b c) = term88.
Proof. exact (TRANS (@lem2399420 b c) (@lem2399421)). Qed.
Lemma lem2399423 (a : int) (b : int) (c : int) : (term229 a b c) = term257.
Proof. exact (MK_COMB (@lem2399195 a) (@lem2399422 b c)). Qed.
Lemma lem2399424 (a : int) (b : int) (c : int) : (term228 a b c) = term257.
Proof. exact (TRANS (@lem2399087 a b c) (@lem2399423 a b c)). Qed.
Lemma lem2399425 : term257 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem2399426 (a : int) (b : int) (c : int) : (term228 a b c) = term88.
Proof. exact (TRANS (@lem2399424 a b c) (@lem2399425)). Qed.
Lemma lem2399427 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2399428 (a : int) (b : int) (c : int) : (term258 a b c) = term259.
Proof. exact (MK_COMB (@lem2399427) (@lem2399426 a b c)). Qed.
Lemma lem2399429 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2399430 (a : int) (b : int) (c : int) : (term227 a b c) = term260.
Proof. exact (MK_COMB (@lem2399428 a b c) (@lem2399429)). Qed.
Lemma lem2399431 (a : int) (b : int) (c : int) (h1 : term297 a b c) : term260.
Proof. exact (EQ_MP (@lem2399430 a b c) (@lem2399086 a b c h1)). Qed.
Lemma lem2399433 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2399434 : term260 = term261.
Proof. exact (@lem2399433 term81 term88). Qed.
Lemma lem2399436 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2399437 : term88 = term94.
Proof. exact (@lem2399436 term28). Qed.
Lemma lem2399439 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2399440 : term81 = term200.
Proof. exact (@lem2399439 (NUMERAL 0)). Qed.
Lemma lem2399441 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2399442 : term262 = term263.
Proof. exact (MK_COMB (@lem2399441) (@lem2399440)). Qed.
Lemma lem2399443 : term261 = term264.
Proof. exact (MK_COMB (@lem2399442) (@lem2399437)). Qed.
Lemma lem2399444 : term265.
Proof. exact (@lem1980026 term81 term27 term88 term27). Qed.
Lemma lem2399446 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399447 : term199 = term206.
Proof. exact (@lem2399446 (NUMERAL 0) term28). Qed.
Lemma lem2399448 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399449 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399450 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399449 h1) (fun h1 : term206 = True => @lem2399448)). Qed.
Lemma lem2399451 : term206 = True.
Proof. exact (EQ_MP (@lem2399450) (@lem2399448)). Qed.
Lemma lem2399452 : term199 = True.
Proof. exact (TRANS (@lem2399447) (@lem2399451)). Qed.
Lemma lem2399453 : True = term199.
Proof. exact (SYM (@lem2399452)). Qed.
Lemma lem2399454 : term199.
Proof. exact (EQ_MP (@lem2399453) (@lem0)). Qed.
Lemma lem2399455 : term266.
Proof. exact (@lem2399444 (@lem2399454)). Qed.
Lemma lem2399457 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399458 : term199 = term206.
Proof. exact (@lem2399457 (NUMERAL 0) term28). Qed.
Lemma lem2399459 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399460 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399461 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399460 h1) (fun h1 : term206 = True => @lem2399459)). Qed.
Lemma lem2399462 : term206 = True.
Proof. exact (EQ_MP (@lem2399461) (@lem2399459)). Qed.
Lemma lem2399463 : term199 = True.
Proof. exact (TRANS (@lem2399458) (@lem2399462)). Qed.
Lemma lem2399464 : True = term199.
Proof. exact (SYM (@lem2399463)). Qed.
Lemma lem2399465 : term199.
Proof. exact (EQ_MP (@lem2399464) (@lem0)). Qed.
Lemma lem2399466 : term264 = term267.
Proof. exact (@lem2399455 (@lem2399465)). Qed.
Lemma lem2399468 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2399469 : term129 = term134.
Proof. exact (@lem2399468 term28 term28). Qed.
Lemma lem2399470 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399471 : term105 = term28.
Proof. exact (EQ_MP (@lem2399470) (@lem940073)). Qed.
Lemma lem2399472 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399473 : term103 = term27.
Proof. exact (MK_COMB (@lem2399472) (@lem2399471)). Qed.
Lemma lem2399474 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2399475 : term134 = term88.
Proof. exact (MK_COMB (@lem2399474) (@lem2399473)). Qed.
Lemma lem2399476 : term129 = term88.
Proof. exact (TRANS (@lem2399469) (@lem2399475)). Qed.
Lemma lem2399478 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399479 : term211 = term81.
Proof. exact (@lem2399478 term28). Qed.
Lemma lem2399480 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2399481 : term268 = term262.
Proof. exact (MK_COMB (@lem2399480) (@lem2399479)). Qed.
Lemma lem2399482 : term267 = term261.
Proof. exact (MK_COMB (@lem2399481) (@lem2399476)). Qed.
Lemma lem2399484 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2399485 : term261 = term271.
Proof. exact (@lem2399484 (NUMERAL 0) term28). Qed.
Lemma lem2399486 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399487 (h1 : term207 = (BIT1 0)) : (term28 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2399488 : (term207 = (BIT1 0)) = ((term28 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399487 h1) (fun h1 : (term28 = (NUMERAL 0)) = False => @lem2399486)). Qed.
Lemma lem2399489 : (term28 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2399488) (@lem2399486)). Qed.
Lemma lem2399490 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2399491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2399492 : term272 = (and True).
Proof. exact (MK_COMB (@lem2399491) (@lem2399490)). Qed.
Lemma lem2399493 : term271 = (True /\ False).
Proof. exact (MK_COMB (@lem2399492) (@lem2399489)). Qed.
Lemma lem2399495 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2399496 : term271 = False.
Proof. exact (TRANS (@lem2399493) (@lem2399495)). Qed.
Lemma lem2399497 : term261 = False.
Proof. exact (TRANS (@lem2399485) (@lem2399496)). Qed.
Lemma lem2399498 : term267 = False.
Proof. exact (TRANS (@lem2399482) (@lem2399497)). Qed.
Lemma lem2399499 : term264 = False.
Proof. exact (TRANS (@lem2399466) (@lem2399498)). Qed.
Lemma lem2399500 : term261 = False.
Proof. exact (TRANS (@lem2399443) (@lem2399499)). Qed.
Lemma lem2399501 : term260 = False.
Proof. exact (TRANS (@lem2399434) (@lem2399500)). Qed.
Lemma lem2399502 (a : int) (b : int) (c : int) (h1 : term297 a b c) : False.
Proof. exact (EQ_MP (@lem2399501) (@lem2399431 a b c h1)). Qed.
Lemma lem2399503 (a : int) (b : int) (c : int) (h1 : term298 a b c) : term298 a b c.
Proof. exact (h1). Qed.
Lemma lem2399504 (a : int) (b : int) (c : int) (h1 : term298 a b c) : (term116 a b c) = term81.
Proof. exact (proj2 (@lem2399503 a b c h1)). Qed.
Lemma lem2399505 (a : int) (b : int) (c : int) (h1 : term298 a b c) : term155 a b c.
Proof. exact (proj1 (@lem2399503 a b c h1)). Qed.
Lemma lem2399507 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2399508 : term198 = term199.
Proof. exact (@lem2399507 term81 term27). Qed.
Lemma lem2399510 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2399511 : term27 = term109.
Proof. exact (@lem2399510 term28). Qed.
Lemma lem2399513 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2399514 : term81 = term200.
Proof. exact (@lem2399513 (NUMERAL 0)). Qed.
Lemma lem2399515 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2399516 : term201 = term202.
Proof. exact (MK_COMB (@lem2399515) (@lem2399514)). Qed.
Lemma lem2399517 : term199 = term203.
Proof. exact (MK_COMB (@lem2399516) (@lem2399511)). Qed.
Lemma lem2399518 : term204.
Proof. exact (@lem1980255 term81 term27 term27 term27). Qed.
Lemma lem2399520 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399521 : term199 = term206.
Proof. exact (@lem2399520 (NUMERAL 0) term28). Qed.
Lemma lem2399522 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399523 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399524 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399523 h1) (fun h1 : term206 = True => @lem2399522)). Qed.
Lemma lem2399525 : term206 = True.
Proof. exact (EQ_MP (@lem2399524) (@lem2399522)). Qed.
Lemma lem2399526 : term199 = True.
Proof. exact (TRANS (@lem2399521) (@lem2399525)). Qed.
Lemma lem2399527 : True = term199.
Proof. exact (SYM (@lem2399526)). Qed.
Lemma lem2399528 : term199.
Proof. exact (EQ_MP (@lem2399527) (@lem0)). Qed.
Lemma lem2399529 : term208.
Proof. exact (@lem2399518 (@lem2399528)). Qed.
Lemma lem2399531 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399532 : term199 = term206.
Proof. exact (@lem2399531 (NUMERAL 0) term28). Qed.
Lemma lem2399533 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399534 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399535 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399534 h1) (fun h1 : term206 = True => @lem2399533)). Qed.
Lemma lem2399536 : term206 = True.
Proof. exact (EQ_MP (@lem2399535) (@lem2399533)). Qed.
Lemma lem2399537 : term199 = True.
Proof. exact (TRANS (@lem2399532) (@lem2399536)). Qed.
Lemma lem2399538 : True = term199.
Proof. exact (SYM (@lem2399537)). Qed.
Lemma lem2399539 : term199.
Proof. exact (EQ_MP (@lem2399538) (@lem0)). Qed.
Lemma lem2399540 : term203 = term209.
Proof. exact (@lem2399529 (@lem2399539)). Qed.
Lemma lem2399542 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399543 : term102 = term103.
Proof. exact (@lem2399542 term28 term28). Qed.
Lemma lem2399544 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399545 : term105 = term28.
Proof. exact (EQ_MP (@lem2399544) (@lem940073)). Qed.
Lemma lem2399546 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399547 : term103 = term27.
Proof. exact (MK_COMB (@lem2399546) (@lem2399545)). Qed.
Lemma lem2399548 : term102 = term27.
Proof. exact (TRANS (@lem2399543) (@lem2399547)). Qed.
Lemma lem2399550 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399551 : term211 = term81.
Proof. exact (@lem2399550 term28). Qed.
Lemma lem2399552 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2399553 : term212 = term201.
Proof. exact (MK_COMB (@lem2399552) (@lem2399551)). Qed.
Lemma lem2399554 : term209 = term199.
Proof. exact (MK_COMB (@lem2399553) (@lem2399548)). Qed.
Lemma lem2399556 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399557 : term199 = term206.
Proof. exact (@lem2399556 (NUMERAL 0) term28). Qed.
Lemma lem2399558 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399559 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399560 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399559 h1) (fun h1 : term206 = True => @lem2399558)). Qed.
Lemma lem2399561 : term206 = True.
Proof. exact (EQ_MP (@lem2399560) (@lem2399558)). Qed.
Lemma lem2399562 : term199 = True.
Proof. exact (TRANS (@lem2399557) (@lem2399561)). Qed.
Lemma lem2399563 : term209 = True.
Proof. exact (TRANS (@lem2399554) (@lem2399562)). Qed.
Lemma lem2399564 : term203 = True.
Proof. exact (TRANS (@lem2399540) (@lem2399563)). Qed.
Lemma lem2399565 : term199 = True.
Proof. exact (TRANS (@lem2399517) (@lem2399564)). Qed.
Lemma lem2399566 : term198 = True.
Proof. exact (TRANS (@lem2399508) (@lem2399565)). Qed.
Lemma lem2399567 : True = term198.
Proof. exact (SYM (@lem2399566)). Qed.
Lemma lem2399568 : term198.
Proof. exact (EQ_MP (@lem2399567) (@lem0)). Qed.
Lemma lem2399569 (a : int) (b : int) (c : int) (h1 : term298 a b c) : term274 a b c.
Proof. exact (conj (@lem2399568) (@lem2399505 a b c h1)). Qed.
Lemma lem2399571 (x : real) (y : real) : term214 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2399572 (a : int) (b : int) (c : int) : term275 a b c.
Proof. exact (@lem2399571 term27 (term152 a b c)). Qed.
Lemma lem2399573 (a : int) (b : int) (c : int) (h1 : term298 a b c) : term276 a b c.
Proof. exact (@lem2399572 a b c (@lem2399569 a b c h1)). Qed.
Lemma lem2399574 (a : int) (b : int) (c : int) : (term277 a b c) = (term152 a b c).
Proof. exact (@lem1982733 (term152 a b c)). Qed.
Lemma lem2399575 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2399576 (a : int) (b : int) (c : int) : (term278 a b c) = (term154 a b c).
Proof. exact (MK_COMB (@lem2399575) (@lem2399574 a b c)). Qed.
Lemma lem2399577 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2399578 (a : int) (b : int) (c : int) : (term276 a b c) = (term155 a b c).
Proof. exact (MK_COMB (@lem2399576 a b c) (@lem2399577)). Qed.
Lemma lem2399579 (a : int) (b : int) (c : int) (h1 : term298 a b c) : term155 a b c.
Proof. exact (EQ_MP (@lem2399578 a b c) (@lem2399573 a b c h1)). Qed.
Lemma lem2399581 (y : real) : term219 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2399582 (a : int) (b : int) (c : int) : term220 a b c.
Proof. exact (@lem2399581 (term116 a b c)). Qed.
Lemma lem2399583 (a : int) (b : int) (c : int) (h1 : term298 a b c) : term221 a b c.
Proof. exact (@lem2399582 a b c (@lem2399504 a b c h1)). Qed.
Lemma lem2399584 (a : int) (b : int) (c : int) (h1 : term298 a b c) : term279 a b c.
Proof. exact (@lem2399583 a b c h1 term88). Qed.
Lemma lem2399585 (a : int) (b : int) (c : int) : (term279 a b c) = ((term280 a b c) = term81).
Proof. exact (eq_refl (term279 a b c)). Qed.
Lemma lem2399586 (a : int) (b : int) (c : int) (h1 : term298 a b c) : (term280 a b c) = term81.
Proof. exact (EQ_MP (@lem2399585 a b c) (@lem2399584 a b c h1)). Qed.
Lemma lem2399587 (a : int) (b : int) (c : int) : (term280 a b c) = (term281 a b c).
Proof. exact (@lem1982781 (real_of_int a) term88 (term115 b c)). Qed.
Lemma lem2399588 (b : int) (c : int) : (term282 b c) = (term283 b c).
Proof. exact (@lem1982781 (term89 b) term88 (real_of_int c)). Qed.
Lemma lem2399589 (c : int) : (term89 c) = (term89 c).
Proof. exact (eq_refl (term89 c)). Qed.
Lemma lem2399590 (b : int) : (term90 b) = (term91 b).
Proof. exact (@lem1982749 term88 term88 (real_of_int b)). Qed.
Lemma lem2399592 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2399593 : term88 = term94.
Proof. exact (@lem2399592 term28). Qed.
Lemma lem2399595 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2399596 : term88 = term94.
Proof. exact (@lem2399595 term28). Qed.
Lemma lem2399597 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399598 : term95 = term96.
Proof. exact (MK_COMB (@lem2399597) (@lem2399596)). Qed.
Lemma lem2399599 : term97 = term98.
Proof. exact (MK_COMB (@lem2399598) (@lem2399593)). Qed.
Lemma lem2399600 : term98 = term99.
Proof. exact (@lem1981613 term88 term88 term27 term27). Qed.
Lemma lem2399602 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399603 : term102 = term103.
Proof. exact (@lem2399602 term28 term28). Qed.
Lemma lem2399604 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399605 : term105 = term28.
Proof. exact (EQ_MP (@lem2399604) (@lem940073)). Qed.
Lemma lem2399606 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399607 : term103 = term27.
Proof. exact (MK_COMB (@lem2399606) (@lem2399605)). Qed.
Lemma lem2399608 : term102 = term27.
Proof. exact (TRANS (@lem2399603) (@lem2399607)). Qed.
Lemma lem2399610 (m : nat) (n : nat) : (term106 m n) = (term101 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2399611 : term97 = term103.
Proof. exact (@lem2399610 term28 term28). Qed.
Lemma lem2399612 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399613 : term105 = term28.
Proof. exact (EQ_MP (@lem2399612) (@lem940073)). Qed.
Lemma lem2399614 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399615 : term103 = term27.
Proof. exact (MK_COMB (@lem2399614) (@lem2399613)). Qed.
Lemma lem2399616 : term97 = term27.
Proof. exact (TRANS (@lem2399611) (@lem2399615)). Qed.
Lemma lem2399617 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2399618 : term107 = term108.
Proof. exact (MK_COMB (@lem2399617) (@lem2399616)). Qed.
Lemma lem2399619 : term99 = term109.
Proof. exact (MK_COMB (@lem2399618) (@lem2399608)). Qed.
Lemma lem2399620 : term98 = term109.
Proof. exact (TRANS (@lem2399600) (@lem2399619)). Qed.
Lemma lem2399621 : term97 = term109.
Proof. exact (TRANS (@lem2399599) (@lem2399620)). Qed.
Lemma lem2399623 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2399624 : term109 = term27.
Proof. exact (@lem2399623 term27). Qed.
Lemma lem2399625 : term97 = term27.
Proof. exact (TRANS (@lem2399621) (@lem2399624)). Qed.
Lemma lem2399626 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399627 : term111 = term112.
Proof. exact (MK_COMB (@lem2399626) (@lem2399625)). Qed.
Lemma lem2399628 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2399629 (b : int) : (term91 b) = (term113 b).
Proof. exact (MK_COMB (@lem2399627) (@lem2399628 b)). Qed.
Lemma lem2399630 (b : int) : (term90 b) = (term113 b).
Proof. exact (TRANS (@lem2399590 b) (@lem2399629 b)). Qed.
Lemma lem2399631 (b : int) : (term113 b) = (real_of_int b).
Proof. exact (@lem1982709 (real_of_int b)). Qed.
Lemma lem2399632 (b : int) : (term90 b) = (real_of_int b).
Proof. exact (TRANS (@lem2399630 b) (@lem2399631 b)). Qed.
Lemma lem2399633 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399634 (b : int) : (term182 b) = (term40 b).
Proof. exact (MK_COMB (@lem2399633) (@lem2399632 b)). Qed.
Lemma lem2399635 (b : int) (c : int) : (term283 b c) = (term82 b c).
Proof. exact (MK_COMB (@lem2399634 b) (@lem2399589 c)). Qed.
Lemma lem2399636 (b : int) (c : int) : (term282 b c) = (term82 b c).
Proof. exact (TRANS (@lem2399588 b c) (@lem2399635 b c)). Qed.
Lemma lem2399639 (a : int) : (term114 a) = (term114 a).
Proof. exact (eq_refl (term114 a)). Qed.
Lemma lem2399640 (a : int) (b : int) (c : int) : (term281 a b c) = (term284 a b c).
Proof. exact (MK_COMB (@lem2399639 a) (@lem2399636 b c)). Qed.
Lemma lem2399641 (a : int) (b : int) (c : int) : (term280 a b c) = (term284 a b c).
Proof. exact (TRANS (@lem2399587 a b c) (@lem2399640 a b c)). Qed.
Lemma lem2399642 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2399643 (a : int) (b : int) (c : int) : (term285 a b c) = (term286 a b c).
Proof. exact (MK_COMB (@lem2399642) (@lem2399641 a b c)). Qed.
Lemma lem2399644 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2399645 (a : int) (b : int) (c : int) : ((term280 a b c) = term81) = ((term284 a b c) = term81).
Proof. exact (MK_COMB (@lem2399643 a b c) (@lem2399644)). Qed.
Lemma lem2399646 (a : int) (b : int) (c : int) (h1 : term298 a b c) : (term284 a b c) = term81.
Proof. exact (EQ_MP (@lem2399645 a b c) (@lem2399586 a b c h1)). Qed.
Lemma lem2399647 (a : int) (b : int) (c : int) (h1 : term298 a b c) : term287 a b c.
Proof. exact (conj (@lem2399646 a b c h1) (@lem2399579 a b c h1)). Qed.
Lemma lem2399649 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2399650 (a : int) (b : int) (c : int) : term288 a b c.
Proof. exact (@lem2399649 (term284 a b c) (term152 a b c)). Qed.
Lemma lem2399651 (a : int) (b : int) (c : int) (h1 : term298 a b c) : term289 a b c.
Proof. exact (@lem2399650 a b c (@lem2399647 a b c h1)). Qed.
Lemma lem2399652 (a : int) (b : int) (c : int) : (term290 a b c) = (term291 a b c).
Proof. exact (@lem1982753 (term89 a) (real_of_int a) (term82 b c) (term151 b c)). Qed.
Lemma lem2399653 (a : int) : (term253 a) = (term231 a).
Proof. exact (@lem1982713 term88 (real_of_int a)). Qed.
Lemma lem2399655 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2399656 : term27 = term109.
Proof. exact (@lem2399655 term28). Qed.
Lemma lem2399658 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2399659 : term88 = term94.
Proof. exact (@lem2399658 term28). Qed.
Lemma lem2399660 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399661 : term232 = term233.
Proof. exact (MK_COMB (@lem2399660) (@lem2399659)). Qed.
Lemma lem2399662 : term234 = term235.
Proof. exact (MK_COMB (@lem2399661) (@lem2399656)). Qed.
Lemma lem2399663 : term236.
Proof. exact (@lem1981473 term88 term27 term27 term27 term81 term27). Qed.
Lemma lem2399665 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399666 : term199 = term206.
Proof. exact (@lem2399665 (NUMERAL 0) term28). Qed.
Lemma lem2399667 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399668 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399669 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399668 h1) (fun h1 : term206 = True => @lem2399667)). Qed.
Lemma lem2399670 : term206 = True.
Proof. exact (EQ_MP (@lem2399669) (@lem2399667)). Qed.
Lemma lem2399671 : term199 = True.
Proof. exact (TRANS (@lem2399666) (@lem2399670)). Qed.
Lemma lem2399672 : True = term199.
Proof. exact (SYM (@lem2399671)). Qed.
Lemma lem2399673 : term199.
Proof. exact (EQ_MP (@lem2399672) (@lem0)). Qed.
Lemma lem2399674 : term237.
Proof. exact (@lem2399663 (@lem2399673)). Qed.
Lemma lem2399676 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399677 : term199 = term206.
Proof. exact (@lem2399676 (NUMERAL 0) term28). Qed.
Lemma lem2399678 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399679 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399680 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399679 h1) (fun h1 : term206 = True => @lem2399678)). Qed.
Lemma lem2399681 : term206 = True.
Proof. exact (EQ_MP (@lem2399680) (@lem2399678)). Qed.
Lemma lem2399682 : term199 = True.
Proof. exact (TRANS (@lem2399677) (@lem2399681)). Qed.
Lemma lem2399683 : True = term199.
Proof. exact (SYM (@lem2399682)). Qed.
Lemma lem2399684 : term199.
Proof. exact (EQ_MP (@lem2399683) (@lem0)). Qed.
Lemma lem2399685 : term238.
Proof. exact (@lem2399674 (@lem2399684)). Qed.
Lemma lem2399687 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399688 : term199 = term206.
Proof. exact (@lem2399687 (NUMERAL 0) term28). Qed.
Lemma lem2399689 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399690 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399691 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399690 h1) (fun h1 : term206 = True => @lem2399689)). Qed.
Lemma lem2399692 : term206 = True.
Proof. exact (EQ_MP (@lem2399691) (@lem2399689)). Qed.
Lemma lem2399693 : term199 = True.
Proof. exact (TRANS (@lem2399688) (@lem2399692)). Qed.
Lemma lem2399694 : True = term199.
Proof. exact (SYM (@lem2399693)). Qed.
Lemma lem2399695 : term199.
Proof. exact (EQ_MP (@lem2399694) (@lem0)). Qed.
Lemma lem2399696 : term239.
Proof. exact (@lem2399685 (@lem2399695)). Qed.
Lemma lem2399698 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399699 : term102 = term103.
Proof. exact (@lem2399698 term28 term28). Qed.
Lemma lem2399700 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399701 : term105 = term28.
Proof. exact (EQ_MP (@lem2399700) (@lem940073)). Qed.
Lemma lem2399702 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399703 : term103 = term27.
Proof. exact (MK_COMB (@lem2399702) (@lem2399701)). Qed.
Lemma lem2399704 : term102 = term27.
Proof. exact (TRANS (@lem2399699) (@lem2399703)). Qed.
Lemma lem2399706 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2399707 : term129 = term134.
Proof. exact (@lem2399706 term28 term28). Qed.
Lemma lem2399708 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399709 : term105 = term28.
Proof. exact (EQ_MP (@lem2399708) (@lem940073)). Qed.
Lemma lem2399710 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399711 : term103 = term27.
Proof. exact (MK_COMB (@lem2399710) (@lem2399709)). Qed.
Lemma lem2399712 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2399713 : term134 = term88.
Proof. exact (MK_COMB (@lem2399712) (@lem2399711)). Qed.
Lemma lem2399714 : term129 = term88.
Proof. exact (TRANS (@lem2399707) (@lem2399713)). Qed.
Lemma lem2399715 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399716 : term240 = term232.
Proof. exact (MK_COMB (@lem2399715) (@lem2399714)). Qed.
Lemma lem2399717 : term241 = term234.
Proof. exact (MK_COMB (@lem2399716) (@lem2399704)). Qed.
Lemma lem2399719 (m : nat) : (term242 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2399720 : term234 = term81.
Proof. exact (@lem2399719 term28). Qed.
Lemma lem2399721 : term241 = term81.
Proof. exact (TRANS (@lem2399717) (@lem2399720)). Qed.
Lemma lem2399722 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399723 : term243 = term244.
Proof. exact (MK_COMB (@lem2399722) (@lem2399721)). Qed.
Lemma lem2399724 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2399725 : term245 = term211.
Proof. exact (MK_COMB (@lem2399723) (@lem2399724)). Qed.
Lemma lem2399727 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399728 : term211 = term81.
Proof. exact (@lem2399727 term28). Qed.
Lemma lem2399729 : term245 = term81.
Proof. exact (TRANS (@lem2399725) (@lem2399728)). Qed.
Lemma lem2399731 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399732 : term102 = term103.
Proof. exact (@lem2399731 term28 term28). Qed.
Lemma lem2399733 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399734 : term105 = term28.
Proof. exact (EQ_MP (@lem2399733) (@lem940073)). Qed.
Lemma lem2399735 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399736 : term103 = term27.
Proof. exact (MK_COMB (@lem2399735) (@lem2399734)). Qed.
Lemma lem2399737 : term102 = term27.
Proof. exact (TRANS (@lem2399732) (@lem2399736)). Qed.
Lemma lem2399738 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem2399739 : term246 = term211.
Proof. exact (MK_COMB (@lem2399738) (@lem2399737)). Qed.
Lemma lem2399741 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399742 : term211 = term81.
Proof. exact (@lem2399741 term28). Qed.
Lemma lem2399743 : term246 = term81.
Proof. exact (TRANS (@lem2399739) (@lem2399742)). Qed.
Lemma lem2399744 : term81 = term246.
Proof. exact (SYM (@lem2399743)). Qed.
Lemma lem2399745 : term245 = term246.
Proof. exact (TRANS (@lem2399729) (@lem2399744)). Qed.
Lemma lem2399746 : term235 = term200.
Proof. exact (@lem2399696 (@lem2399745)). Qed.
Lemma lem2399747 : term234 = term200.
Proof. exact (TRANS (@lem2399662) (@lem2399746)). Qed.
Lemma lem2399749 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2399750 : term200 = term81.
Proof. exact (@lem2399749 term81). Qed.
Lemma lem2399751 : term234 = term81.
Proof. exact (TRANS (@lem2399747) (@lem2399750)). Qed.
Lemma lem2399752 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399753 : term247 = term244.
Proof. exact (MK_COMB (@lem2399752) (@lem2399751)). Qed.
Lemma lem2399754 (a : int) : (real_of_int a) = (real_of_int a).
Proof. exact (eq_refl (real_of_int a)). Qed.
Lemma lem2399755 (a : int) : (term231 a) = (term248 a).
Proof. exact (MK_COMB (@lem2399753) (@lem2399754 a)). Qed.
Lemma lem2399756 (a : int) : (term253 a) = (term248 a).
Proof. exact (TRANS (@lem2399653 a) (@lem2399755 a)). Qed.
Lemma lem2399757 (a : int) : (term248 a) = term81.
Proof. exact (@lem1982719 (real_of_int a)). Qed.
Lemma lem2399758 (a : int) : (term253 a) = term81.
Proof. exact (TRANS (@lem2399756 a) (@lem2399757 a)). Qed.
Lemma lem2399759 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399760 (a : int) : (term254 a) = term250.
Proof. exact (MK_COMB (@lem2399759) (@lem2399758 a)). Qed.
Lemma lem2399761 (b : int) (c : int) : (term292 b c) = (term293 b c).
Proof. exact (@lem1982753 (real_of_int b) (term89 b) (term89 c) (term183 c)). Qed.
Lemma lem2399762 (b : int) : (term230 b) = (term231 b).
Proof. exact (@lem1982715 term88 (real_of_int b)). Qed.
Lemma lem2399764 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2399765 : term27 = term109.
Proof. exact (@lem2399764 term28). Qed.
Lemma lem2399767 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2399768 : term88 = term94.
Proof. exact (@lem2399767 term28). Qed.
Lemma lem2399769 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399770 : term232 = term233.
Proof. exact (MK_COMB (@lem2399769) (@lem2399768)). Qed.
Lemma lem2399771 : term234 = term235.
Proof. exact (MK_COMB (@lem2399770) (@lem2399765)). Qed.
Lemma lem2399772 : term236.
Proof. exact (@lem1981473 term88 term27 term27 term27 term81 term27). Qed.
Lemma lem2399774 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399775 : term199 = term206.
Proof. exact (@lem2399774 (NUMERAL 0) term28). Qed.
Lemma lem2399776 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399777 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399778 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399777 h1) (fun h1 : term206 = True => @lem2399776)). Qed.
Lemma lem2399779 : term206 = True.
Proof. exact (EQ_MP (@lem2399778) (@lem2399776)). Qed.
Lemma lem2399780 : term199 = True.
Proof. exact (TRANS (@lem2399775) (@lem2399779)). Qed.
Lemma lem2399781 : True = term199.
Proof. exact (SYM (@lem2399780)). Qed.
Lemma lem2399782 : term199.
Proof. exact (EQ_MP (@lem2399781) (@lem0)). Qed.
Lemma lem2399783 : term237.
Proof. exact (@lem2399772 (@lem2399782)). Qed.
Lemma lem2399785 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399786 : term199 = term206.
Proof. exact (@lem2399785 (NUMERAL 0) term28). Qed.
Lemma lem2399787 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399788 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399789 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399788 h1) (fun h1 : term206 = True => @lem2399787)). Qed.
Lemma lem2399790 : term206 = True.
Proof. exact (EQ_MP (@lem2399789) (@lem2399787)). Qed.
Lemma lem2399791 : term199 = True.
Proof. exact (TRANS (@lem2399786) (@lem2399790)). Qed.
Lemma lem2399792 : True = term199.
Proof. exact (SYM (@lem2399791)). Qed.
Lemma lem2399793 : term199.
Proof. exact (EQ_MP (@lem2399792) (@lem0)). Qed.
Lemma lem2399794 : term238.
Proof. exact (@lem2399783 (@lem2399793)). Qed.
Lemma lem2399796 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399797 : term199 = term206.
Proof. exact (@lem2399796 (NUMERAL 0) term28). Qed.
Lemma lem2399798 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399799 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399800 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399799 h1) (fun h1 : term206 = True => @lem2399798)). Qed.
Lemma lem2399801 : term206 = True.
Proof. exact (EQ_MP (@lem2399800) (@lem2399798)). Qed.
Lemma lem2399802 : term199 = True.
Proof. exact (TRANS (@lem2399797) (@lem2399801)). Qed.
Lemma lem2399803 : True = term199.
Proof. exact (SYM (@lem2399802)). Qed.
Lemma lem2399804 : term199.
Proof. exact (EQ_MP (@lem2399803) (@lem0)). Qed.
Lemma lem2399805 : term239.
Proof. exact (@lem2399794 (@lem2399804)). Qed.
Lemma lem2399807 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399808 : term102 = term103.
Proof. exact (@lem2399807 term28 term28). Qed.
Lemma lem2399809 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399810 : term105 = term28.
Proof. exact (EQ_MP (@lem2399809) (@lem940073)). Qed.
Lemma lem2399811 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399812 : term103 = term27.
Proof. exact (MK_COMB (@lem2399811) (@lem2399810)). Qed.
Lemma lem2399813 : term102 = term27.
Proof. exact (TRANS (@lem2399808) (@lem2399812)). Qed.
Lemma lem2399815 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2399816 : term129 = term134.
Proof. exact (@lem2399815 term28 term28). Qed.
Lemma lem2399817 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399818 : term105 = term28.
Proof. exact (EQ_MP (@lem2399817) (@lem940073)). Qed.
Lemma lem2399819 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399820 : term103 = term27.
Proof. exact (MK_COMB (@lem2399819) (@lem2399818)). Qed.
Lemma lem2399821 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2399822 : term134 = term88.
Proof. exact (MK_COMB (@lem2399821) (@lem2399820)). Qed.
Lemma lem2399823 : term129 = term88.
Proof. exact (TRANS (@lem2399816) (@lem2399822)). Qed.
Lemma lem2399824 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399825 : term240 = term232.
Proof. exact (MK_COMB (@lem2399824) (@lem2399823)). Qed.
Lemma lem2399826 : term241 = term234.
Proof. exact (MK_COMB (@lem2399825) (@lem2399813)). Qed.
Lemma lem2399828 (m : nat) : (term242 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2399829 : term234 = term81.
Proof. exact (@lem2399828 term28). Qed.
Lemma lem2399830 : term241 = term81.
Proof. exact (TRANS (@lem2399826) (@lem2399829)). Qed.
Lemma lem2399831 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399832 : term243 = term244.
Proof. exact (MK_COMB (@lem2399831) (@lem2399830)). Qed.
Lemma lem2399833 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2399834 : term245 = term211.
Proof. exact (MK_COMB (@lem2399832) (@lem2399833)). Qed.
Lemma lem2399836 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399837 : term211 = term81.
Proof. exact (@lem2399836 term28). Qed.
Lemma lem2399838 : term245 = term81.
Proof. exact (TRANS (@lem2399834) (@lem2399837)). Qed.
Lemma lem2399840 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399841 : term102 = term103.
Proof. exact (@lem2399840 term28 term28). Qed.
Lemma lem2399842 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399843 : term105 = term28.
Proof. exact (EQ_MP (@lem2399842) (@lem940073)). Qed.
Lemma lem2399844 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399845 : term103 = term27.
Proof. exact (MK_COMB (@lem2399844) (@lem2399843)). Qed.
Lemma lem2399846 : term102 = term27.
Proof. exact (TRANS (@lem2399841) (@lem2399845)). Qed.
Lemma lem2399847 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem2399848 : term246 = term211.
Proof. exact (MK_COMB (@lem2399847) (@lem2399846)). Qed.
Lemma lem2399850 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399851 : term211 = term81.
Proof. exact (@lem2399850 term28). Qed.
Lemma lem2399852 : term246 = term81.
Proof. exact (TRANS (@lem2399848) (@lem2399851)). Qed.
Lemma lem2399853 : term81 = term246.
Proof. exact (SYM (@lem2399852)). Qed.
Lemma lem2399854 : term245 = term246.
Proof. exact (TRANS (@lem2399838) (@lem2399853)). Qed.
Lemma lem2399855 : term235 = term200.
Proof. exact (@lem2399805 (@lem2399854)). Qed.
Lemma lem2399856 : term234 = term200.
Proof. exact (TRANS (@lem2399771) (@lem2399855)). Qed.
Lemma lem2399858 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2399859 : term200 = term81.
Proof. exact (@lem2399858 term81). Qed.
Lemma lem2399860 : term234 = term81.
Proof. exact (TRANS (@lem2399856) (@lem2399859)). Qed.
Lemma lem2399861 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399862 : term247 = term244.
Proof. exact (MK_COMB (@lem2399861) (@lem2399860)). Qed.
Lemma lem2399863 (b : int) : (real_of_int b) = (real_of_int b).
Proof. exact (eq_refl (real_of_int b)). Qed.
Lemma lem2399864 (b : int) : (term231 b) = (term248 b).
Proof. exact (MK_COMB (@lem2399862) (@lem2399863 b)). Qed.
Lemma lem2399865 (b : int) : (term230 b) = (term248 b).
Proof. exact (TRANS (@lem2399762 b) (@lem2399864 b)). Qed.
Lemma lem2399866 (b : int) : (term248 b) = term81.
Proof. exact (@lem1982719 (real_of_int b)). Qed.
Lemma lem2399867 (b : int) : (term230 b) = term81.
Proof. exact (TRANS (@lem2399865 b) (@lem2399866 b)). Qed.
Lemma lem2399868 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399869 (b : int) : (term249 b) = term250.
Proof. exact (MK_COMB (@lem2399868) (@lem2399867 b)). Qed.
Lemma lem2399870 (c : int) : (term294 c) = (term295 c).
Proof. exact (@lem1982763 (term89 c) (real_of_int c) term88). Qed.
Lemma lem2399871 (c : int) : (term253 c) = (term231 c).
Proof. exact (@lem1982713 term88 (real_of_int c)). Qed.
Lemma lem2399873 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2399874 : term27 = term109.
Proof. exact (@lem2399873 term28). Qed.
Lemma lem2399876 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2399877 : term88 = term94.
Proof. exact (@lem2399876 term28). Qed.
Lemma lem2399878 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399879 : term232 = term233.
Proof. exact (MK_COMB (@lem2399878) (@lem2399877)). Qed.
Lemma lem2399880 : term234 = term235.
Proof. exact (MK_COMB (@lem2399879) (@lem2399874)). Qed.
Lemma lem2399881 : term236.
Proof. exact (@lem1981473 term88 term27 term27 term27 term81 term27). Qed.
Lemma lem2399883 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399884 : term199 = term206.
Proof. exact (@lem2399883 (NUMERAL 0) term28). Qed.
Lemma lem2399885 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399886 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399887 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399886 h1) (fun h1 : term206 = True => @lem2399885)). Qed.
Lemma lem2399888 : term206 = True.
Proof. exact (EQ_MP (@lem2399887) (@lem2399885)). Qed.
Lemma lem2399889 : term199 = True.
Proof. exact (TRANS (@lem2399884) (@lem2399888)). Qed.
Lemma lem2399890 : True = term199.
Proof. exact (SYM (@lem2399889)). Qed.
Lemma lem2399891 : term199.
Proof. exact (EQ_MP (@lem2399890) (@lem0)). Qed.
Lemma lem2399892 : term237.
Proof. exact (@lem2399881 (@lem2399891)). Qed.
Lemma lem2399894 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399895 : term199 = term206.
Proof. exact (@lem2399894 (NUMERAL 0) term28). Qed.
Lemma lem2399896 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399897 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399898 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399897 h1) (fun h1 : term206 = True => @lem2399896)). Qed.
Lemma lem2399899 : term206 = True.
Proof. exact (EQ_MP (@lem2399898) (@lem2399896)). Qed.
Lemma lem2399900 : term199 = True.
Proof. exact (TRANS (@lem2399895) (@lem2399899)). Qed.
Lemma lem2399901 : True = term199.
Proof. exact (SYM (@lem2399900)). Qed.
Lemma lem2399902 : term199.
Proof. exact (EQ_MP (@lem2399901) (@lem0)). Qed.
Lemma lem2399903 : term238.
Proof. exact (@lem2399892 (@lem2399902)). Qed.
Lemma lem2399905 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2399906 : term199 = term206.
Proof. exact (@lem2399905 (NUMERAL 0) term28). Qed.
Lemma lem2399907 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2399908 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2399909 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2399908 h1) (fun h1 : term206 = True => @lem2399907)). Qed.
Lemma lem2399910 : term206 = True.
Proof. exact (EQ_MP (@lem2399909) (@lem2399907)). Qed.
Lemma lem2399911 : term199 = True.
Proof. exact (TRANS (@lem2399906) (@lem2399910)). Qed.
Lemma lem2399912 : True = term199.
Proof. exact (SYM (@lem2399911)). Qed.
Lemma lem2399913 : term199.
Proof. exact (EQ_MP (@lem2399912) (@lem0)). Qed.
Lemma lem2399914 : term239.
Proof. exact (@lem2399903 (@lem2399913)). Qed.
Lemma lem2399916 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399917 : term102 = term103.
Proof. exact (@lem2399916 term28 term28). Qed.
Lemma lem2399918 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399919 : term105 = term28.
Proof. exact (EQ_MP (@lem2399918) (@lem940073)). Qed.
Lemma lem2399920 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399921 : term103 = term27.
Proof. exact (MK_COMB (@lem2399920) (@lem2399919)). Qed.
Lemma lem2399922 : term102 = term27.
Proof. exact (TRANS (@lem2399917) (@lem2399921)). Qed.
Lemma lem2399924 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2399925 : term129 = term134.
Proof. exact (@lem2399924 term28 term28). Qed.
Lemma lem2399926 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399927 : term105 = term28.
Proof. exact (EQ_MP (@lem2399926) (@lem940073)). Qed.
Lemma lem2399928 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399929 : term103 = term27.
Proof. exact (MK_COMB (@lem2399928) (@lem2399927)). Qed.
Lemma lem2399930 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2399931 : term134 = term88.
Proof. exact (MK_COMB (@lem2399930) (@lem2399929)). Qed.
Lemma lem2399932 : term129 = term88.
Proof. exact (TRANS (@lem2399925) (@lem2399931)). Qed.
Lemma lem2399933 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399934 : term240 = term232.
Proof. exact (MK_COMB (@lem2399933) (@lem2399932)). Qed.
Lemma lem2399935 : term241 = term234.
Proof. exact (MK_COMB (@lem2399934) (@lem2399922)). Qed.
Lemma lem2399937 (m : nat) : (term242 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2399938 : term234 = term81.
Proof. exact (@lem2399937 term28). Qed.
Lemma lem2399939 : term241 = term81.
Proof. exact (TRANS (@lem2399935) (@lem2399938)). Qed.
Lemma lem2399940 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399941 : term243 = term244.
Proof. exact (MK_COMB (@lem2399940) (@lem2399939)). Qed.
Lemma lem2399942 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem2399943 : term245 = term211.
Proof. exact (MK_COMB (@lem2399941) (@lem2399942)). Qed.
Lemma lem2399945 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399946 : term211 = term81.
Proof. exact (@lem2399945 term28). Qed.
Lemma lem2399947 : term245 = term81.
Proof. exact (TRANS (@lem2399943) (@lem2399946)). Qed.
Lemma lem2399949 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2399950 : term102 = term103.
Proof. exact (@lem2399949 term28 term28). Qed.
Lemma lem2399951 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2399952 : term105 = term28.
Proof. exact (EQ_MP (@lem2399951) (@lem940073)). Qed.
Lemma lem2399953 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2399954 : term103 = term27.
Proof. exact (MK_COMB (@lem2399953) (@lem2399952)). Qed.
Lemma lem2399955 : term102 = term27.
Proof. exact (TRANS (@lem2399950) (@lem2399954)). Qed.
Lemma lem2399956 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem2399957 : term246 = term211.
Proof. exact (MK_COMB (@lem2399956) (@lem2399955)). Qed.
Lemma lem2399959 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2399960 : term211 = term81.
Proof. exact (@lem2399959 term28). Qed.
Lemma lem2399961 : term246 = term81.
Proof. exact (TRANS (@lem2399957) (@lem2399960)). Qed.
Lemma lem2399962 : term81 = term246.
Proof. exact (SYM (@lem2399961)). Qed.
Lemma lem2399963 : term245 = term246.
Proof. exact (TRANS (@lem2399947) (@lem2399962)). Qed.
Lemma lem2399964 : term235 = term200.
Proof. exact (@lem2399914 (@lem2399963)). Qed.
Lemma lem2399965 : term234 = term200.
Proof. exact (TRANS (@lem2399880) (@lem2399964)). Qed.
Lemma lem2399967 (x : real) : (term110 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2399968 : term200 = term81.
Proof. exact (@lem2399967 term81). Qed.
Lemma lem2399969 : term234 = term81.
Proof. exact (TRANS (@lem2399965) (@lem2399968)). Qed.
Lemma lem2399970 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2399971 : term247 = term244.
Proof. exact (MK_COMB (@lem2399970) (@lem2399969)). Qed.
Lemma lem2399972 (c : int) : (real_of_int c) = (real_of_int c).
Proof. exact (eq_refl (real_of_int c)). Qed.
Lemma lem2399973 (c : int) : (term231 c) = (term248 c).
Proof. exact (MK_COMB (@lem2399971) (@lem2399972 c)). Qed.
Lemma lem2399974 (c : int) : (term253 c) = (term248 c).
Proof. exact (TRANS (@lem2399871 c) (@lem2399973 c)). Qed.
Lemma lem2399975 (c : int) : (term248 c) = term81.
Proof. exact (@lem1982719 (real_of_int c)). Qed.
Lemma lem2399976 (c : int) : (term253 c) = term81.
Proof. exact (TRANS (@lem2399974 c) (@lem2399975 c)). Qed.
Lemma lem2399977 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2399978 (c : int) : (term254 c) = term250.
Proof. exact (MK_COMB (@lem2399977) (@lem2399976 c)). Qed.
Lemma lem2399979 : term88 = term88.
Proof. exact (eq_refl term88). Qed.
Lemma lem2399980 (c : int) : (term295 c) = term257.
Proof. exact (MK_COMB (@lem2399978 c) (@lem2399979)). Qed.
Lemma lem2399981 (c : int) : (term294 c) = term257.
Proof. exact (TRANS (@lem2399870 c) (@lem2399980 c)). Qed.
Lemma lem2399982 : term257 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem2399983 (c : int) : (term294 c) = term88.
Proof. exact (TRANS (@lem2399981 c) (@lem2399982)). Qed.
Lemma lem2399984 (b : int) (c : int) : (term293 b c) = term257.
Proof. exact (MK_COMB (@lem2399869 b) (@lem2399983 c)). Qed.
Lemma lem2399985 (b : int) (c : int) : (term292 b c) = term257.
Proof. exact (TRANS (@lem2399761 b c) (@lem2399984 b c)). Qed.
Lemma lem2399986 : term257 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem2399987 (b : int) (c : int) : (term292 b c) = term88.
Proof. exact (TRANS (@lem2399985 b c) (@lem2399986)). Qed.
Lemma lem2399988 (a : int) (b : int) (c : int) : (term291 a b c) = term257.
Proof. exact (MK_COMB (@lem2399760 a) (@lem2399987 b c)). Qed.
Lemma lem2399989 (a : int) (b : int) (c : int) : (term290 a b c) = term257.
Proof. exact (TRANS (@lem2399652 a b c) (@lem2399988 a b c)). Qed.
Lemma lem2399990 : term257 = term88.
Proof. exact (@lem1982721 term88). Qed.
Lemma lem2399991 (a : int) (b : int) (c : int) : (term290 a b c) = term88.
Proof. exact (TRANS (@lem2399989 a b c) (@lem2399990)). Qed.
Lemma lem2399992 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2399993 (a : int) (b : int) (c : int) : (term296 a b c) = term259.
Proof. exact (MK_COMB (@lem2399992) (@lem2399991 a b c)). Qed.
Lemma lem2399994 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2399995 (a : int) (b : int) (c : int) : (term289 a b c) = term260.
Proof. exact (MK_COMB (@lem2399993 a b c) (@lem2399994)). Qed.
Lemma lem2399996 (a : int) (b : int) (c : int) (h1 : term298 a b c) : term260.
Proof. exact (EQ_MP (@lem2399995 a b c) (@lem2399651 a b c h1)). Qed.
Lemma lem2399998 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2399999 : term260 = term261.
Proof. exact (@lem2399998 term81 term88). Qed.
Lemma lem2400001 (x : nat) : (term92 x) = (term93 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2400002 : term88 = term94.
Proof. exact (@lem2400001 term28). Qed.
Lemma lem2400004 (x : nat) : (real_of_num x) = (term128 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2400005 : term81 = term200.
Proof. exact (@lem2400004 (NUMERAL 0)). Qed.
Lemma lem2400006 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2400007 : term262 = term263.
Proof. exact (MK_COMB (@lem2400006) (@lem2400005)). Qed.
Lemma lem2400008 : term261 = term264.
Proof. exact (MK_COMB (@lem2400007) (@lem2400002)). Qed.
Lemma lem2400009 : term265.
Proof. exact (@lem1980026 term81 term27 term88 term27). Qed.
Lemma lem2400011 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2400012 : term199 = term206.
Proof. exact (@lem2400011 (NUMERAL 0) term28). Qed.
Lemma lem2400013 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2400014 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2400015 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2400014 h1) (fun h1 : term206 = True => @lem2400013)). Qed.
Lemma lem2400016 : term206 = True.
Proof. exact (EQ_MP (@lem2400015) (@lem2400013)). Qed.
Lemma lem2400017 : term199 = True.
Proof. exact (TRANS (@lem2400012) (@lem2400016)). Qed.
Lemma lem2400018 : True = term199.
Proof. exact (SYM (@lem2400017)). Qed.
Lemma lem2400019 : term199.
Proof. exact (EQ_MP (@lem2400018) (@lem0)). Qed.
Lemma lem2400020 : term266.
Proof. exact (@lem2400009 (@lem2400019)). Qed.
Lemma lem2400022 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2400023 : term199 = term206.
Proof. exact (@lem2400022 (NUMERAL 0) term28). Qed.
Lemma lem2400024 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2400025 (h1 : term207 = (BIT1 0)) : term206 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2400026 : (term207 = (BIT1 0)) = (term206 = True).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2400025 h1) (fun h1 : term206 = True => @lem2400024)). Qed.
Lemma lem2400027 : term206 = True.
Proof. exact (EQ_MP (@lem2400026) (@lem2400024)). Qed.
Lemma lem2400028 : term199 = True.
Proof. exact (TRANS (@lem2400023) (@lem2400027)). Qed.
Lemma lem2400029 : True = term199.
Proof. exact (SYM (@lem2400028)). Qed.
Lemma lem2400030 : term199.
Proof. exact (EQ_MP (@lem2400029) (@lem0)). Qed.
Lemma lem2400031 : term264 = term267.
Proof. exact (@lem2400020 (@lem2400030)). Qed.
Lemma lem2400033 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2400034 : term129 = term134.
Proof. exact (@lem2400033 term28 term28). Qed.
Lemma lem2400035 : (term104 = (BIT1 0)) = (term105 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2400036 : term105 = term28.
Proof. exact (EQ_MP (@lem2400035) (@lem940073)). Qed.
Lemma lem2400037 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2400038 : term103 = term27.
Proof. exact (MK_COMB (@lem2400037) (@lem2400036)). Qed.
Lemma lem2400039 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2400040 : term134 = term88.
Proof. exact (MK_COMB (@lem2400039) (@lem2400038)). Qed.
Lemma lem2400041 : term129 = term88.
Proof. exact (TRANS (@lem2400034) (@lem2400040)). Qed.
Lemma lem2400043 (x : nat) : (term210 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2400044 : term211 = term81.
Proof. exact (@lem2400043 term28). Qed.
Lemma lem2400045 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2400046 : term268 = term262.
Proof. exact (MK_COMB (@lem2400045) (@lem2400044)). Qed.
Lemma lem2400047 : term267 = term261.
Proof. exact (MK_COMB (@lem2400046) (@lem2400041)). Qed.
Lemma lem2400049 (m : nat) (n : nat) : (term269 m n) = (term270 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2400050 : term261 = term271.
Proof. exact (@lem2400049 (NUMERAL 0) term28). Qed.
Lemma lem2400051 : term207 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2400052 (h1 : term207 = (BIT1 0)) : (term28 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2400053 : (term207 = (BIT1 0)) = ((term28 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term207 = (BIT1 0) => @lem2400052 h1) (fun h1 : (term28 = (NUMERAL 0)) = False => @lem2400051)). Qed.
Lemma lem2400054 : (term28 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2400053) (@lem2400051)). Qed.
Lemma lem2400055 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2400056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2400057 : term272 = (and True).
Proof. exact (MK_COMB (@lem2400056) (@lem2400055)). Qed.
Lemma lem2400058 : term271 = (True /\ False).
Proof. exact (MK_COMB (@lem2400057) (@lem2400054)). Qed.
Lemma lem2400060 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2400061 : term271 = False.
Proof. exact (TRANS (@lem2400058) (@lem2400060)). Qed.
Lemma lem2400062 : term261 = False.
Proof. exact (TRANS (@lem2400050) (@lem2400061)). Qed.
Lemma lem2400063 : term267 = False.
Proof. exact (TRANS (@lem2400047) (@lem2400062)). Qed.
Lemma lem2400064 : term264 = False.
Proof. exact (TRANS (@lem2400031) (@lem2400063)). Qed.
Lemma lem2400065 : term261 = False.
Proof. exact (TRANS (@lem2400008) (@lem2400064)). Qed.
Lemma lem2400066 : term260 = False.
Proof. exact (TRANS (@lem2399999) (@lem2400065)). Qed.
Lemma lem2400067 (a : int) (b : int) (c : int) (h1 : term298 a b c) : False.
Proof. exact (EQ_MP (@lem2400066) (@lem2399996 a b c h1)). Qed.
Lemma lem2400068 (a : int) (b : int) (c : int) (h1 : term193 a b c) : False.
Proof. exact (or_elim (@lem2398991 a b c h1) (fun h0 : term297 a b c => @lem2399502 a b c h0) (fun h0 : term298 a b c => @lem2400067 a b c h0)). Qed.
Lemma lem2400069 (a : int) (b : int) (c : int) (h1 : term196 a b c) : False.
Proof. exact (or_elim (@lem2397912 a b c h1) (fun h0 : term194 a b c => @lem2398990 a b c h0) (fun h0 : term193 a b c => @lem2400068 a b c h0)). Qed.
Lemma lem2400071 (a : int) (b : int) (c : int) (h1 : term196 a b c) : term196 a b c.
Proof. exact (h1). Qed.
Lemma lem2400072 (a : int) (b : int) (c : int) (h1 : term196 a b c) : (term196 a b c) = False.
Proof. exact (prop_ext (fun h2 : term196 a b c => @lem2400069 a b c h1) (fun h2 : False => @lem2400071 a b c h1)). Qed.
Lemma lem2400073 (a : int) (b : int) (c : int) (h1 : term196 a b c) : False.
Proof. exact (EQ_MP (@lem2400072 a b c h1) (@lem2400071 a b c h1)). Qed.
Lemma lem2400074 (c : int) (a : int) (b : int) (h1 : term79 c a b) : term79 c a b.
Proof. exact (h1). Qed.
Lemma lem2400075 (c : int) (a : int) (b : int) (h1 : term79 c a b) : term196 a b c.
Proof. exact (EQ_MP (@lem2397890 a b c) (@lem2400074 c a b h1)). Qed.
Lemma lem2400076 (c : int) (a : int) (b : int) (h1 : term79 c a b) : (term196 a b c) = False.
Proof. exact (prop_ext (fun h2 : term196 a b c => @lem2400073 a b c h2) (fun h2 : False => @lem2400075 c a b h1)). Qed.
Lemma lem2400077 (c : int) (a : int) (b : int) (h1 : term79 c a b) : False.
Proof. exact (EQ_MP (@lem2400076 c a b h1) (@lem2400075 c a b h1)). Qed.
Lemma lem2400078 (c : int) (a : int) (b : int) : term299 c a b.
Proof. exact (fun h0 : term79 c a b => @lem2400077 c a b h0). Qed.
Lemma lem2400079 (c : int) (a : int) (b : int) : term300 c a b.
Proof. exact (@lem1386578 (term301 c a b)). Qed.
Lemma lem2400082 (c : int) (a : int) (b : int) : term301 c a b.
Proof. exact (@lem2400079 c a b (@lem2400078 c a b)). Qed.
Lemma lem2400083 (c : int) (a : int) (b : int) : (term77 c a b) = (term5 c a b).
Proof. exact (SYM (@lem2397276 c a b)). Qed.
Lemma lem2400084 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2400085 (c : int) (a : int) (b : int) : (term301 c a b) = (term4 c a b).
Proof. exact (MK_COMB (@lem2400084) (@lem2400083 c a b)). Qed.
Lemma lem2400086 (c : int) (a : int) (b : int) : term4 c a b.
Proof. exact (EQ_MP (@lem2400085 c a b) (@lem2400082 c a b)). Qed.
Lemma lem2400097 (c : int) (a : int) (b : int) : (a = (int_sub b c)) = ((int_add c a) = b).
Proof. exact (EQ_MP (@lem2397105 c a b) (@lem2400086 c a b)). Qed.
Lemma lem2400098 (n : int) (m : int) : ((rem m n) = (term302 m n)) = ((term3 m n) = m).
Proof. exact (@lem2400097 (term303 m n) (rem m n) m). Qed.
Lemma lem2400101 (m : int) : (term304 m) = (term305 m).
Proof. exact (fun_ext (fun n : int => @lem2400098 n m)). Qed.
Lemma lem2400102 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2400103 (m : int) : (term306 m) = (term1 m).
Proof. exact (MK_COMB (@lem2400102) (@lem2400101 m)). Qed.
Lemma lem2400108 : term307 = term308.
Proof. exact (fun_ext (fun m : int => @lem2400103 m)). Qed.
Lemma lem2400109 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2400110 : term309 = term310.
Proof. exact (MK_COMB (@lem2400109) (@lem2400108)). Qed.
Lemma lem2400115 : term310 = term309.
Proof. exact (SYM (@lem2400110)). Qed.
Lemma lem2400127 (n : int) (m : int) : (term3 m n) = m.
Proof. exact (EQ_MP (@lem2397103 n m) (@lem2397102 m n)). Qed.
Lemma lem2400128 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2400129 (n : int) (m : int) : (term311 m n) = (@eq int m).
Proof. exact (MK_COMB (@lem2400128) (@lem2400127 n m)). Qed.
Lemma lem2400130 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2400131 (n : int) (m : int) : ((term3 m n) = m) = (m = m).
Proof. exact (MK_COMB (@lem2400129 n m) (@lem2400130 m)). Qed.
Lemma lem2400133 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2400134 (x : int) : (x = x) = True.
Proof. exact (@lem2400133 int x). Qed.
Lemma lem2400135 (m : int) : (m = m) = True.
Proof. exact (@lem2400134 m). Qed.
Lemma lem2400136 (n : int) (m : int) : ((term3 m n) = m) = True.
Proof. exact (TRANS (@lem2400131 n m) (@lem2400135 m)). Qed.
Lemma lem2400137 (m : int) : (term305 m) = term312.
Proof. exact (fun_ext (fun n : int => @lem2400136 n m)). Qed.
Lemma lem2400138 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2400139 (m : int) : (term1 m) = term313.
Proof. exact (MK_COMB (@lem2400138) (@lem2400137 m)). Qed.
Lemma lem2400141 {A : Type'} (t : Prop) : (term314 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2400142 (t : Prop) : (term315 t) = t.
Proof. exact (@lem2400141 int t). Qed.
Lemma lem2400143 : term313 = True.
Proof. exact (@lem2400142 True). Qed.
Lemma lem2400144 (m : int) : (term1 m) = True.
Proof. exact (TRANS (@lem2400139 m) (@lem2400143)). Qed.
Lemma lem2400145 : term308 = term312.
Proof. exact (fun_ext (fun m : int => @lem2400144 m)). Qed.
Lemma lem2400146 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2400147 : term310 = term313.
Proof. exact (MK_COMB (@lem2400146) (@lem2400145)). Qed.
Lemma lem2400149 {A : Type'} (t : Prop) : (term314 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2400150 (t : Prop) : (term315 t) = t.
Proof. exact (@lem2400149 int t). Qed.
Lemma lem2400151 : term313 = True.
Proof. exact (@lem2400150 True). Qed.
Lemma lem2400152 : term310 = True.
Proof. exact (TRANS (@lem2400147) (@lem2400151)). Qed.
Lemma lem2400153 : True = term310.
Proof. exact (SYM (@lem2400152)). Qed.
Lemma lem2400154 : term310.
Proof. exact (EQ_MP (@lem2400153) (@lem0)). Qed.
Lemma lem2400155 : term309.
Proof. exact (EQ_MP (@lem2400115) (@lem2400154)). Qed.
