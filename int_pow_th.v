Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_pow_th_term_abbrevs.
Require Import int_mul_spec.
Require Import int_mul_th_spec.
Require Import int_of_num_spec.
Require Import int_of_num_th_spec.
Require Import int_pow_spec.
Require Import thm0_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem2294059 (x : int) (y : int) (h1 : (int_mul x y) = (term0 x y)) : (int_mul x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2294060 (x : int) (y : int) (h1 : (int_mul x y) = (term0 x y)) : (term0 x y) = (int_mul x y).
Proof. exact (SYM (@lem2294059 x y h1)). Qed.
Lemma lem2294061 (x : int) (y : int) (h1 : (term0 x y) = (int_mul x y)) : (term0 x y) = (int_mul x y).
Proof. exact (h1). Qed.
Lemma lem2294062 (x : int) (y : int) (h1 : (term0 x y) = (int_mul x y)) : (int_mul x y) = (term0 x y).
Proof. exact (SYM (@lem2294061 x y h1)). Qed.
Lemma lem2294063 (x : int) (y : int) : ((int_mul x y) = (term0 x y)) = ((term0 x y) = (int_mul x y)).
Proof. exact (prop_ext (fun h1 : (int_mul x y) = (term0 x y) => @lem2294060 x y h1) (fun h1 : (term0 x y) = (int_mul x y) => @lem2294062 x y h1)). Qed.
Lemma lem2294064 (x : int) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : int => @lem2294063 x y)). Qed.
Lemma lem2294065 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294066 (x : int) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem2294065) (@lem2294064 x)). Qed.
Lemma lem2294067 : term5 = term6.
Proof. exact (fun_ext (fun x : int => @lem2294066 x)). Qed.
Lemma lem2294068 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2294069 : term7 = term8.
Proof. exact (MK_COMB (@lem2294068) (@lem2294067)). Qed.
Lemma lem2294070 : term8.
Proof. exact (EQ_MP (@lem2294069) (@lem2286307)). Qed.
Lemma lem2294072 (n : nat) (h1 : (int_of_num n) = (term9 n)) : (int_of_num n) = (term9 n).
Proof. exact (h1). Qed.
Lemma lem2294073 (n : nat) (h1 : (int_of_num n) = (term9 n)) : (term9 n) = (int_of_num n).
Proof. exact (SYM (@lem2294072 n h1)). Qed.
Lemma lem2294074 (n : nat) (h1 : (term9 n) = (int_of_num n)) : (term9 n) = (int_of_num n).
Proof. exact (h1). Qed.
Lemma lem2294075 (n : nat) (h1 : (term9 n) = (int_of_num n)) : (int_of_num n) = (term9 n).
Proof. exact (SYM (@lem2294074 n h1)). Qed.
Lemma lem2294076 (n : nat) : ((int_of_num n) = (term9 n)) = ((term9 n) = (int_of_num n)).
Proof. exact (prop_ext (fun h1 : (int_of_num n) = (term9 n) => @lem2294073 n h1) (fun h1 : (term9 n) = (int_of_num n) => @lem2294075 n h1)). Qed.
Lemma lem2294077 : term10 = term11.
Proof. exact (fun_ext (fun n : nat => @lem2294076 n)). Qed.
Lemma lem2294078 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2294079 : term12 = term13.
Proof. exact (MK_COMB (@lem2294078) (@lem2294077)). Qed.
Lemma lem2294080 : term13.
Proof. exact (EQ_MP (@lem2294079) (@lem2271820)). Qed.
Lemma lem2294081 (n : nat) : term14 n.
Proof. exact (@lem2271980 n). Qed.
Lemma lem2294082 (n : nat) : (term14 n) = ((term15 n) = (real_of_num n)).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem2294084 (n : nat) : term16 n.
Proof. exact (@lem2294080 n). Qed.
Lemma lem2294085 (n : nat) : (term16 n) = ((term9 n) = (int_of_num n)).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem2294087 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem2294088 (x : real) (n : nat) : term18 x n.
Proof. exact (@lem2294087 x n). Qed.
Lemma lem2294089 (x : real) (n : nat) : (term18 x n) = ((term19 x n) = (term20 x n)).
Proof. exact (eq_refl (term18 x n)). Qed.
Lemma lem2294092 (x : int) : term21 x.
Proof. exact (@lem2294056 x). Qed.
Lemma lem2294093 (x : int) : (term21 x) = (term22 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem2294094 (x : int) : term22 x.
Proof. exact (EQ_MP (@lem2294093 x) (@lem2294092 x)). Qed.
Lemma lem2294095 (x : int) (n : nat) : term23 x n.
Proof. exact (@lem2294094 x n). Qed.
Lemma lem2294096 (x : int) (n : nat) : (term23 x n) = ((int_pow x n) = (term24 x n)).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem2294105 (x : int) (n : nat) : (int_pow x n) = (term24 x n).
Proof. exact (EQ_MP (@lem2294096 x n) (@lem2294095 x n)). Qed.
Lemma lem2294106 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2294107 (x : int) (n : nat) : (term25 x n) = (term26 x n).
Proof. exact (MK_COMB (@lem2294106) (@lem2294105 x n)). Qed.
Lemma lem2294108 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2294109 (x : int) (n : nat) : (term27 x n) = (term28 x n).
Proof. exact (MK_COMB (@lem2294108) (@lem2294107 x n)). Qed.
Lemma lem2294110 (x : int) (n : nat) : (term29 x n) = (term29 x n).
Proof. exact (eq_refl (term29 x n)). Qed.
Lemma lem2294111 (x : int) (n : nat) : ((term25 x n) = (term29 x n)) = ((term26 x n) = (term29 x n)).
Proof. exact (MK_COMB (@lem2294109 x n) (@lem2294110 x n)). Qed.
Lemma lem2294114 (x : int) : (term30 x) = (term31 x).
Proof. exact (fun_ext (fun n : nat => @lem2294111 x n)). Qed.
Lemma lem2294115 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2294116 (x : int) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem2294115) (@lem2294114 x)). Qed.
Lemma lem2294121 (x : int) : (term33 x) = (term32 x).
Proof. exact (SYM (@lem2294116 x)). Qed.
Lemma lem2294123 (P : nat -> Prop) : term34 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem2294124 (x : int) : term35 x.
Proof. exact (@lem2294123 (term31 x)). Qed.
Lemma lem2294125 (x : int) : (term36 x) = ((term37 x) = (term38 x)).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem2294126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2294127 (x : int) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem2294126) (@lem2294125 x)). Qed.
Lemma lem2294128 (x : int) (n : nat) : (term41 x n) = ((term26 x n) = (term29 x n)).
Proof. exact (eq_refl (term41 x n)). Qed.
Lemma lem2294129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2294130 (x : int) (n : nat) : (term42 x n) = (term43 x n).
Proof. exact (MK_COMB (@lem2294129) (@lem2294128 x n)). Qed.
Lemma lem2294131 (x : int) (n : nat) : (term44 x n) = ((term45 x n) = (term46 x n)).
Proof. exact (eq_refl (term44 x n)). Qed.
Lemma lem2294132 (x : int) (n : nat) : (term47 x n) = (term48 x n).
Proof. exact (MK_COMB (@lem2294130 x n) (@lem2294131 x n)). Qed.
Lemma lem2294133 (x : int) : (term49 x) = (term50 x).
Proof. exact (fun_ext (fun n : nat => @lem2294132 x n)). Qed.
Lemma lem2294134 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2294135 (x : int) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem2294134) (@lem2294133 x)). Qed.
Lemma lem2294136 (x : int) : (term53 x) = (term54 x).
Proof. exact (MK_COMB (@lem2294127 x) (@lem2294135 x)). Qed.
Lemma lem2294137 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2294138 (x : int) : (term55 x) = (term56 x).
Proof. exact (MK_COMB (@lem2294137) (@lem2294136 x)). Qed.
Lemma lem2294139 (x : int) (n : nat) : (term41 x n) = ((term26 x n) = (term29 x n)).
Proof. exact (eq_refl (term41 x n)). Qed.
Lemma lem2294140 (x : int) : (term57 x) = (term31 x).
Proof. exact (fun_ext (fun n : nat => @lem2294139 x n)). Qed.
Lemma lem2294141 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2294142 (x : int) : (term58 x) = (term33 x).
Proof. exact (MK_COMB (@lem2294141) (@lem2294140 x)). Qed.
Lemma lem2294143 (x : int) : (term35 x) = (term59 x).
Proof. exact (MK_COMB (@lem2294138 x) (@lem2294142 x)). Qed.
Lemma lem2294144 (x : int) : term59 x.
Proof. exact (EQ_MP (@lem2294143 x) (@lem2294124 x)). Qed.
Lemma lem2294145 (x : int) (n : nat) (h1 : (term26 x n) = (term29 x n)) : (term26 x n) = (term29 x n).
Proof. exact (h1). Qed.
Lemma lem2294149 (x : real) : (term60 x) = term61.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem2294150 (x : int) : (term38 x) = term61.
Proof. exact (@lem2294149 (real_of_int x)). Qed.
Lemma lem2294151 : int_of_real = int_of_real.
Proof. exact (eq_refl int_of_real). Qed.
Lemma lem2294152 (x : int) : (term62 x) = term63.
Proof. exact (MK_COMB (@lem2294151) (@lem2294150 x)). Qed.
Lemma lem2294153 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2294154 (x : int) : (term37 x) = term64.
Proof. exact (MK_COMB (@lem2294153) (@lem2294152 x)). Qed.
Lemma lem2294155 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2294156 (x : int) : (term65 x) = term66.
Proof. exact (MK_COMB (@lem2294155) (@lem2294154 x)). Qed.
Lemma lem2294158 (x : real) : (term60 x) = term61.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem2294159 (x : int) : (term38 x) = term61.
Proof. exact (@lem2294158 (real_of_int x)). Qed.
Lemma lem2294160 (x : int) : ((term37 x) = (term38 x)) = (term64 = term61).
Proof. exact (MK_COMB (@lem2294156 x) (@lem2294159 x)). Qed.
Lemma lem2294163 (x : int) : (term64 = term61) = ((term37 x) = (term38 x)).
Proof. exact (SYM (@lem2294160 x)). Qed.
Lemma lem2294167 (x : real) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (EQ_MP (@lem2294089 x n) (@lem2294088 x n)). Qed.
Lemma lem2294168 (x : int) (n : nat) : (term46 x n) = (term67 x n).
Proof. exact (@lem2294167 (real_of_int x) n). Qed.
Lemma lem2294169 : int_of_real = int_of_real.
Proof. exact (eq_refl int_of_real). Qed.
Lemma lem2294170 (x : int) (n : nat) : (term68 x n) = (term69 x n).
Proof. exact (MK_COMB (@lem2294169) (@lem2294168 x n)). Qed.
Lemma lem2294171 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2294172 (x : int) (n : nat) : (term45 x n) = (term70 x n).
Proof. exact (MK_COMB (@lem2294171) (@lem2294170 x n)). Qed.
Lemma lem2294173 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2294174 (x : int) (n : nat) : (term71 x n) = (term72 x n).
Proof. exact (MK_COMB (@lem2294173) (@lem2294172 x n)). Qed.
Lemma lem2294176 (x : real) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (EQ_MP (@lem2294089 x n) (@lem2294088 x n)). Qed.
Lemma lem2294177 (x : int) (n : nat) : (term46 x n) = (term67 x n).
Proof. exact (@lem2294176 (real_of_int x) n). Qed.
Lemma lem2294178 (x : int) (n : nat) : ((term45 x n) = (term46 x n)) = ((term70 x n) = (term67 x n)).
Proof. exact (MK_COMB (@lem2294174 x n) (@lem2294177 x n)). Qed.
Lemma lem2294181 (x : int) (n : nat) : ((term70 x n) = (term67 x n)) = ((term45 x n) = (term46 x n)).
Proof. exact (SYM (@lem2294178 x n)). Qed.
Lemma lem2294185 (n : nat) : (term9 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2294085 n) (@lem2294084 n)). Qed.
Lemma lem2294186 : term63 = term73.
Proof. exact (@lem2294185 term74). Qed.
Lemma lem2294187 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2294188 : term64 = term75.
Proof. exact (MK_COMB (@lem2294187) (@lem2294186)). Qed.
Lemma lem2294190 (n : nat) : (term15 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2294082 n) (@lem2294081 n)). Qed.
Lemma lem2294191 : term75 = term61.
Proof. exact (@lem2294190 term74). Qed.
Lemma lem2294192 : term64 = term61.
Proof. exact (TRANS (@lem2294188) (@lem2294191)). Qed.
Lemma lem2294193 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2294194 : term66 = term76.
Proof. exact (MK_COMB (@lem2294193) (@lem2294192)). Qed.
Lemma lem2294195 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem2294196 : (term64 = term61) = (term61 = term61).
Proof. exact (MK_COMB (@lem2294194) (@lem2294195)). Qed.
Lemma lem2294198 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294199 (x : real) : (x = x) = True.
Proof. exact (@lem2294198 real x). Qed.
Lemma lem2294200 : (term61 = term61) = True.
Proof. exact (@lem2294199 term61). Qed.
Lemma lem2294201 : (term64 = term61) = True.
Proof. exact (TRANS (@lem2294196) (@lem2294200)). Qed.
Lemma lem2294202 : True = (term64 = term61).
Proof. exact (SYM (@lem2294201)). Qed.
Lemma lem2294203 : term64 = term61.
Proof. exact (EQ_MP (@lem2294202) (@lem0)). Qed.
Lemma lem2294204 (x : int) (n : nat) (h1 : (term26 x n) = (term29 x n)) : (term29 x n) = (term26 x n).
Proof. exact (SYM (@lem2294145 x n h1)). Qed.
Lemma lem2294205 (x : int) : (term77 x) = (term77 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem2294206 (x : int) (n : nat) (h1 : (term26 x n) = (term29 x n)) : (term78 x n) = (term79 x n).
Proof. exact (MK_COMB (@lem2294205 x) (@lem2294204 x n h1)). Qed.
Lemma lem2294207 (x : int) (n : nat) : (term79 x n) = ((term80 x n) = (term81 x n)).
Proof. exact (eq_refl (term79 x n)). Qed.
Lemma lem2294208 (x : int) (n : nat) : (term82 x n) = (term82 x n).
Proof. exact (eq_refl (term82 x n)). Qed.
Lemma lem2294209 (x : int) (n : nat) : ((term78 x n) = (term79 x n)) = ((term78 x n) = ((term80 x n) = (term81 x n))).
Proof. exact (MK_COMB (@lem2294208 x n) (@lem2294207 x n)). Qed.
Lemma lem2294210 (x : int) (n : nat) : (term78 x n) = ((term70 x n) = (term67 x n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2294211 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2294212 (x : int) (n : nat) : (term82 x n) = (term83 x n).
Proof. exact (MK_COMB (@lem2294211) (@lem2294210 x n)). Qed.
Lemma lem2294213 (x : int) (n : nat) : ((term80 x n) = (term81 x n)) = ((term80 x n) = (term81 x n)).
Proof. exact (eq_refl ((term80 x n) = (term81 x n))). Qed.
Lemma lem2294214 (x : int) (n : nat) : ((term78 x n) = ((term80 x n) = (term81 x n))) = (((term70 x n) = (term67 x n)) = ((term80 x n) = (term81 x n))).
Proof. exact (MK_COMB (@lem2294212 x n) (@lem2294213 x n)). Qed.
Lemma lem2294215 (x : int) (n : nat) : ((term78 x n) = (term79 x n)) = (((term70 x n) = (term67 x n)) = ((term80 x n) = (term81 x n))).
Proof. exact (TRANS (@lem2294209 x n) (@lem2294214 x n)). Qed.
Lemma lem2294216 (x : int) (n : nat) (h1 : (term26 x n) = (term29 x n)) : ((term70 x n) = (term67 x n)) = ((term80 x n) = (term81 x n)).
Proof. exact (EQ_MP (@lem2294215 x n) (@lem2294206 x n h1)). Qed.
Lemma lem2294217 (x : int) (n : nat) (h1 : (term26 x n) = (term29 x n)) : ((term80 x n) = (term81 x n)) = ((term70 x n) = (term67 x n)).
Proof. exact (SYM (@lem2294216 x n h1)). Qed.
Lemma lem2294218 (x : int) : term84 x.
Proof. exact (@lem2287415 x). Qed.
Lemma lem2294219 (x : int) : (term84 x) = (term85 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem2294220 (x : int) : term85 x.
Proof. exact (EQ_MP (@lem2294219 x) (@lem2294218 x)). Qed.
Lemma lem2294221 (x : int) (y : int) : term86 x y.
Proof. exact (@lem2294220 x y). Qed.
Lemma lem2294222 (x : int) (y : int) : (term86 x y) = ((term87 x y) = (term88 x y)).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem2294224 (x : int) : term89 x.
Proof. exact (@lem2294070 x). Qed.
Lemma lem2294225 (x : int) : (term89 x) = (term4 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem2294226 (x : int) : term4 x.
Proof. exact (EQ_MP (@lem2294225 x) (@lem2294224 x)). Qed.
Lemma lem2294227 (x : int) (y : int) : term90 x y.
Proof. exact (@lem2294226 x y). Qed.
Lemma lem2294228 (x : int) (y : int) : (term90 x y) = ((term0 x y) = (int_mul x y)).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem2294233 (x : int) (y : int) : (term0 x y) = (int_mul x y).
Proof. exact (EQ_MP (@lem2294228 x y) (@lem2294227 x y)). Qed.
Lemma lem2294234 (x : int) (n : nat) : (term91 x n) = (term92 x n).
Proof. exact (@lem2294233 x (term24 x n)). Qed.
Lemma lem2294235 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2294236 (x : int) (n : nat) : (term80 x n) = (term93 x n).
Proof. exact (MK_COMB (@lem2294235) (@lem2294234 x n)). Qed.
Lemma lem2294238 (x : int) (y : int) : (term87 x y) = (term88 x y).
Proof. exact (EQ_MP (@lem2294222 x y) (@lem2294221 x y)). Qed.
Lemma lem2294239 (x : int) (n : nat) : (term93 x n) = (term81 x n).
Proof. exact (@lem2294238 x (term24 x n)). Qed.
Lemma lem2294240 (x : int) (n : nat) : (term80 x n) = (term81 x n).
Proof. exact (TRANS (@lem2294236 x n) (@lem2294239 x n)). Qed.
Lemma lem2294241 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2294242 (x : int) (n : nat) : (term94 x n) = (term95 x n).
Proof. exact (MK_COMB (@lem2294241) (@lem2294240 x n)). Qed.
Lemma lem2294243 (x : int) (n : nat) : (term81 x n) = (term81 x n).
Proof. exact (eq_refl (term81 x n)). Qed.
Lemma lem2294244 (x : int) (n : nat) : ((term80 x n) = (term81 x n)) = ((term81 x n) = (term81 x n)).
Proof. exact (MK_COMB (@lem2294242 x n) (@lem2294243 x n)). Qed.
Lemma lem2294246 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2294247 (x : real) : (x = x) = True.
Proof. exact (@lem2294246 real x). Qed.
Lemma lem2294248 (x : int) (n : nat) : ((term81 x n) = (term81 x n)) = True.
Proof. exact (@lem2294247 (term81 x n)). Qed.
Lemma lem2294249 (x : int) (n : nat) : ((term80 x n) = (term81 x n)) = True.
Proof. exact (TRANS (@lem2294244 x n) (@lem2294248 x n)). Qed.
Lemma lem2294250 (x : int) (n : nat) : True = ((term80 x n) = (term81 x n)).
Proof. exact (SYM (@lem2294249 x n)). Qed.
Lemma lem2294251 (x : int) (n : nat) : (term80 x n) = (term81 x n).
Proof. exact (EQ_MP (@lem2294250 x n) (@lem0)). Qed.
Lemma lem2294252 (x : int) (n : nat) (h1 : (term26 x n) = (term29 x n)) : (term70 x n) = (term67 x n).
Proof. exact (EQ_MP (@lem2294217 x n h1) (@lem2294251 x n)). Qed.
Lemma lem2294253 (x : int) (n : nat) (h1 : (term26 x n) = (term29 x n)) : (term45 x n) = (term46 x n).
Proof. exact (EQ_MP (@lem2294181 x n) (@lem2294252 x n h1)). Qed.
Lemma lem2294254 (x : int) : (term37 x) = (term38 x).
Proof. exact (EQ_MP (@lem2294163 x) (@lem2294203)). Qed.
Lemma lem2294255 (x : int) (n : nat) : term48 x n.
Proof. exact (fun h0 : (term26 x n) = (term29 x n) => @lem2294253 x n h0). Qed.
Lemma lem2294260 (x : int) : term52 x.
Proof. exact (fun n : nat => @lem2294255 x n). Qed.
Lemma lem2294261 (x : int) : term54 x.
Proof. exact (conj (@lem2294254 x) (@lem2294260 x)). Qed.
Lemma lem2294262 (x : int) : term33 x.
Proof. exact (@lem2294144 x (@lem2294261 x)). Qed.
Lemma lem2294263 (x : int) : term32 x.
Proof. exact (EQ_MP (@lem2294121 x) (@lem2294262 x)). Qed.
Lemma lem2294268 : term96.
Proof. exact (fun x : int => @lem2294263 x). Qed.
