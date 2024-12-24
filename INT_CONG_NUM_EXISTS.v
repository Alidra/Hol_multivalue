Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_CONG_NUM_EXISTS_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import INT_ABS_spec.
Require Import INT_ABS_MUL_spec.
Require Import INT_LE_LMUL_spec.
Require Import INT_OF_NUM_OF_INT_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032627_spec.
Require Import thm1032730_spec.
Require Import thm129_spec.
Require Import thm13473_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm137_spec.
Require Import thm1386578_spec.
Require Import thm1482678_spec.
Require Import thm1482679_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
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
Require Import thm1982713_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982731_spec.
Require Import thm1982733_spec.
Require Import thm1982735_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318514_spec.
Require Import thm2318515_spec.
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
Require Import thm2405481_spec.
Require Import thm2405758_spec.
Require Import thm2405764_spec.
Require Import thm2405813_spec.
Require Import thm2416511_spec.
Require Import thm2416515_spec.
Require Import thm2416517_spec.
Require Import thm2416521_spec.
Require Import thm2416523_spec.
Require Import thm2416525_spec.
Require Import thm2416531_spec.
Require Import thm2416533_spec.
Require Import thm2416535_spec.
Require Import thm2416537_spec.
Require Import thm2416547_spec.
Require Import thm2416549_spec.
Require Import thm2416551_spec.
Require Import thm2416555_spec.
Require Import thm2416557_spec.
Require Import thm2416563_spec.
Require Import thm2416587_spec.
Require Import thm2416594_spec.
Require Import thm2427003_spec.
Require Import thm2427014_spec.
Require Import thm2427015_spec.
Require Import thm2427026_spec.
Require Import thm2444030_spec.
Require Import thm2444031_spec.
Require Import thm2447297_spec.
Require Import thm2447298_spec.
Require Import thm2447306_spec.
Require Import thm2447307_spec.
Require Import thm2841542_spec.
Require Import thm2841544_spec.
Require Import thm2841561_spec.
Require Import thm2841562_spec.
Require Import thm2841579_spec.
Require Import thm2841580_spec.
Require Import thm2841585_spec.
Require Import thm2841586_spec.
Require Import thm2841591_spec.
Require Import thm2841592_spec.
Require Import thm2841615_spec.
Require Import thm2841616_spec.
Require Import thm2954598_spec.
Require Import thm32_spec.
Require Import thm62_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm93_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem3123785 (x : int) : term0 x.
Proof. exact (@lem2318180 x). Qed.
Lemma lem3123786 (x : int) : (term0 x) = ((int_abs x) = (term1 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3123793 (x : int) (y : int) (n : int) : (term2 x y n) = (term3 x y n).
Proof. exact (EQ_MP (@lem2447307 x y n) (@lem2447306 x y n)). Qed.
Lemma lem3123794 (a : int) (x : int) (n : int) : (term4 a x n) = (term5 a x n).
Proof. exact (@lem3123793 (int_add x a) x n). Qed.
Lemma lem3123801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3123802 (a : int) (x : int) (n : int) : (term6 a x n) = (term7 a x n).
Proof. exact (MK_COMB (@lem3123801) (@lem3123794 a x n)). Qed.
Lemma lem3123804 (b : int) (a : int) : (int_divides a b) = (term8 b a).
Proof. exact (EQ_MP (@lem2447298 b a) (@lem2447297 b a)). Qed.
Lemma lem3123805 (a : int) (n : int) : (int_divides n a) = (term8 a n).
Proof. exact (@lem3123804 a n). Qed.
Lemma lem3123812 (x : int) (a : int) (n : int) : ((term4 a x n) = (int_divides n a)) = ((term5 a x n) = (term8 a n)).
Proof. exact (MK_COMB (@lem3123802 a x n) (@lem3123805 a n)). Qed.
Lemma lem3123815 (x : int) (n : int) (a : int) : ((term5 a x n) = (term8 a n)) = ((term4 a x n) = (int_divides n a)).
Proof. exact (SYM (@lem3123812 x a n)). Qed.
Lemma lem3123816 (a : int) (x : int) (n : int) (h1 : term5 a x n) : term5 a x n.
Proof. exact (h1). Qed.
Lemma lem3123817 (a : int) (x : int) (n : int) (d : int) (h1 : (term9 a x) = (int_mul n d)) : (term9 a x) = (int_mul n d).
Proof. exact (h1). Qed.
Lemma lem3123818 (a : int) (n : int) (h1 : term8 a n) : term8 a n.
Proof. exact (h1). Qed.
Lemma lem3123819 (a : int) (n : int) (x' : int) (h1 : a = (int_mul n x')) : a = (int_mul n x').
Proof. exact (h1). Qed.
Lemma lem3124048 (a : int) (x : int) (n : int) (d : int) (h1 : (term9 a x) = (int_mul n d)) : (int_mul n d) = (term9 a x).
Proof. exact (SYM (@lem3123817 a x n d h1)). Qed.
Lemma lem3124049 (a : int) (n : int) (x' : int) (h1 : a = (int_mul n x')) : (int_mul n x') = a.
Proof. exact (SYM (@lem3123819 a n x' h1)). Qed.
Lemma lem3124051 (x : int) (y : int) : (x = y) = ((int_sub x y) = term10).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem3124052 (n : int) (d : int) (a : int) (x : int) : ((int_mul n d) = (term9 a x)) = ((term11 n d a x) = term10).
Proof. exact (@lem3124051 (int_mul n d) (term9 a x)). Qed.
Lemma lem3124053 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3124060 (a : int) (x : int) : (int_add x a) = (int_add a x).
Proof. exact (@lem2416563 a x). Qed.
Lemma lem3124061 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem3124062 (a : int) (x : int) : (term12 x a) = (term12 a x).
Proof. exact (MK_COMB (@lem3124061) (@lem3124060 a x)). Qed.
Lemma lem3124063 (a : int) (x : int) : (term9 a x) = (term13 a x).
Proof. exact (MK_COMB (@lem3124062 a x) (@lem3124053 x)). Qed.
Lemma lem3124064 (a : int) (x : int) : (term13 a x) = (term14 a x).
Proof. exact (@lem2416594 (int_add a x) x). Qed.
Lemma lem3124068 (a : int) (x : int) : (term14 a x) = (term15 a x).
Proof. exact (@lem2416557 a x (term16 x)). Qed.
Lemma lem3124069 (x : int) : (term17 x) = (term18 x).
Proof. exact (@lem2416517 term19 x). Qed.
Lemma lem3124071 (m : nat) : (term20 m) = term10.
Proof. exact (proj1 (@lem2405813 m)). Qed.
Lemma lem3124072 : term21 = term10.
Proof. exact (@lem3124071 term22). Qed.
Lemma lem3124073 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3124074 : term23 = term24.
Proof. exact (MK_COMB (@lem3124073) (@lem3124072)). Qed.
Lemma lem3124075 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3124076 (x : int) : (term18 x) = (term25 x).
Proof. exact (MK_COMB (@lem3124074) (@lem3124075 x)). Qed.
Lemma lem3124077 (x : int) : (term17 x) = (term25 x).
Proof. exact (TRANS (@lem3124069 x) (@lem3124076 x)). Qed.
Lemma lem3124078 (x : int) : (term25 x) = term10.
Proof. exact (@lem2416521 x). Qed.
Lemma lem3124079 (x : int) : (term17 x) = term10.
Proof. exact (TRANS (@lem3124077 x) (@lem3124078 x)). Qed.
Lemma lem3124080 (a : int) : (int_add a) = (int_add a).
Proof. exact (eq_refl (int_add a)). Qed.
Lemma lem3124081 (x : int) (a : int) : (term15 a x) = (term26 a).
Proof. exact (MK_COMB (@lem3124080 a) (@lem3124079 x)). Qed.
Lemma lem3124082 (x : int) (a : int) : (term14 a x) = (term26 a).
Proof. exact (TRANS (@lem3124068 a x) (@lem3124081 x a)). Qed.
Lemma lem3124083 (a : int) : (term26 a) = a.
Proof. exact (@lem2416525 a). Qed.
Lemma lem3124085 (x : int) (a : int) : (term14 a x) = a.
Proof. exact (TRANS (@lem3124082 x a) (@lem3124083 a)). Qed.
Lemma lem3124086 (x : int) (a : int) : (term13 a x) = a.
Proof. exact (TRANS (@lem3124064 a x) (@lem3124085 x a)). Qed.
Lemma lem3124087 (x : int) (a : int) : (term9 a x) = a.
Proof. exact (TRANS (@lem3124063 a x) (@lem3124086 x a)). Qed.
Lemma lem3124094 (d : int) (n : int) : (int_mul n d) = (int_mul d n).
Proof. exact (@lem2416549 d n). Qed.
Lemma lem3124095 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem3124096 (d : int) (n : int) : (term27 n d) = (term27 d n).
Proof. exact (MK_COMB (@lem3124095) (@lem3124094 d n)). Qed.
Lemma lem3124097 (x : int) (d : int) (n : int) (a : int) : (term11 n d a x) = (term28 d n a).
Proof. exact (MK_COMB (@lem3124096 d n) (@lem3124087 x a)). Qed.
Lemma lem3124104 (d : int) (n : int) (a : int) : (term28 d n a) = (term29 d n a).
Proof. exact (@lem2416594 (int_mul d n) a). Qed.
Lemma lem3124105 (x : int) (d : int) (n : int) (a : int) : (term11 n d a x) = (term29 d n a).
Proof. exact (TRANS (@lem3124097 x d n a) (@lem3124104 d n a)). Qed.
Lemma lem3124106 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3124107 (x : int) (d : int) (n : int) (a : int) : (term30 n d a x) = (term31 d n a).
Proof. exact (MK_COMB (@lem3124106) (@lem3124105 x d n a)). Qed.
Lemma lem3124108 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3124109 (x : int) (d : int) (n : int) (a : int) : ((term11 n d a x) = term10) = ((term29 d n a) = term10).
Proof. exact (MK_COMB (@lem3124107 x d n a) (@lem3124108)). Qed.
Lemma lem3124110 (x : int) (d : int) (n : int) (a : int) : ((int_mul n d) = (term9 a x)) = ((term29 d n a) = term10).
Proof. exact (TRANS (@lem3124052 n d a x) (@lem3124109 x d n a)). Qed.
Lemma lem3124111 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3124112 (x : int) (d : int) (n : int) (a : int) : (term32 n d a x) = (term33 d n a).
Proof. exact (MK_COMB (@lem3124111) (@lem3124110 x d n a)). Qed.
Lemma lem3124114 (x : int) (y : int) : (x = y) = ((int_sub x y) = term10).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem3124115 (a : int) (n : int) (x : int) : (a = (int_mul n x)) = ((term34 a n x) = term10).
Proof. exact (@lem3124114 a (int_mul n x)). Qed.
Lemma lem3124127 (a : int) (n : int) (x : int) : (term34 a n x) = (term35 a n x).
Proof. exact (@lem2416594 a (int_mul n x)). Qed.
Lemma lem3124132 (n : int) (x : int) (a : int) : (term35 a n x) = (term36 n x a).
Proof. exact (@lem2416563 (term37 n x) a). Qed.
Lemma lem3124134 (n : int) (x : int) (a : int) : (term34 a n x) = (term36 n x a).
Proof. exact (TRANS (@lem3124127 a n x) (@lem3124132 n x a)). Qed.
Lemma lem3124135 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3124136 (n : int) (x : int) (a : int) : (term38 a n x) = (term39 n x a).
Proof. exact (MK_COMB (@lem3124135) (@lem3124134 n x a)). Qed.
Lemma lem3124137 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3124138 (n : int) (x : int) (a : int) : ((term34 a n x) = term10) = ((term36 n x a) = term10).
Proof. exact (MK_COMB (@lem3124136 n x a) (@lem3124137)). Qed.
Lemma lem3124139 (n : int) (x : int) (a : int) : (a = (int_mul n x)) = ((term36 n x a) = term10).
Proof. exact (TRANS (@lem3124115 a n x) (@lem3124138 n x a)). Qed.
Lemma lem3124140 (n : int) (a : int) : (term40 a n) = (term41 n a).
Proof. exact (fun_ext (fun x : int => @lem3124139 n x a)). Qed.
Lemma lem3124141 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3124142 (n : int) (a : int) : (term8 a n) = (term42 n a).
Proof. exact (MK_COMB (@lem3124141) (@lem3124140 n a)). Qed.
Lemma lem3124143 (x : int) (d : int) (n : int) (a : int) : (term43 d x a n) = (term44 d n a).
Proof. exact (MK_COMB (@lem3124112 x d n a) (@lem3124142 n a)). Qed.
Lemma lem3124144 (d : int) (x : int) (a : int) (n : int) : (term44 d n a) = (term43 d x a n).
Proof. exact (SYM (@lem3124143 x d n a)). Qed.
Lemma lem3124146 (x : int) (y : int) : (x = y) = ((int_sub x y) = term10).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem3124147 (n : int) (x' : int) (a : int) : ((int_mul n x') = a) = ((term28 n x' a) = term10).
Proof. exact (@lem3124146 (int_mul n x') a). Qed.
Lemma lem3124166 (n : int) (x' : int) (a : int) : (term28 n x' a) = (term29 n x' a).
Proof. exact (@lem2416594 (int_mul n x') a). Qed.
Lemma lem3124167 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3124168 (n : int) (x' : int) (a : int) : (term45 n x' a) = (term31 n x' a).
Proof. exact (MK_COMB (@lem3124167) (@lem3124166 n x' a)). Qed.
Lemma lem3124169 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3124170 (n : int) (x' : int) (a : int) : ((term28 n x' a) = term10) = ((term29 n x' a) = term10).
Proof. exact (MK_COMB (@lem3124168 n x' a) (@lem3124169)). Qed.
Lemma lem3124171 (n : int) (x' : int) (a : int) : ((int_mul n x') = a) = ((term29 n x' a) = term10).
Proof. exact (TRANS (@lem3124147 n x' a) (@lem3124170 n x' a)). Qed.
Lemma lem3124172 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3124173 (n : int) (x' : int) (a : int) : (term46 n x' a) = (term33 n x' a).
Proof. exact (MK_COMB (@lem3124172) (@lem3124171 n x' a)). Qed.
Lemma lem3124175 (x : int) (y : int) : (x = y) = ((int_sub x y) = term10).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem3124176 (a : int) (x : int) (n : int) (d : int) : ((term9 a x) = (int_mul n d)) = ((term47 a x n d) = term10).
Proof. exact (@lem3124175 (term9 a x) (int_mul n d)). Qed.
Lemma lem3124183 (d : int) (n : int) : (int_mul n d) = (int_mul d n).
Proof. exact (@lem2416549 d n). Qed.
Lemma lem3124184 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3124191 (a : int) (x : int) : (int_add x a) = (int_add a x).
Proof. exact (@lem2416563 a x). Qed.
Lemma lem3124192 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem3124193 (a : int) (x : int) : (term12 x a) = (term12 a x).
Proof. exact (MK_COMB (@lem3124192) (@lem3124191 a x)). Qed.
Lemma lem3124194 (a : int) (x : int) : (term9 a x) = (term13 a x).
Proof. exact (MK_COMB (@lem3124193 a x) (@lem3124184 x)). Qed.
Lemma lem3124195 (a : int) (x : int) : (term13 a x) = (term14 a x).
Proof. exact (@lem2416594 (int_add a x) x). Qed.
Lemma lem3124199 (a : int) (x : int) : (term14 a x) = (term15 a x).
Proof. exact (@lem2416557 a x (term16 x)). Qed.
Lemma lem3124200 (x : int) : (term17 x) = (term18 x).
Proof. exact (@lem2416517 term19 x). Qed.
Lemma lem3124202 (m : nat) : (term20 m) = term10.
Proof. exact (proj1 (@lem2405813 m)). Qed.
Lemma lem3124203 : term21 = term10.
Proof. exact (@lem3124202 term22). Qed.
Lemma lem3124204 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3124205 : term23 = term24.
Proof. exact (MK_COMB (@lem3124204) (@lem3124203)). Qed.
Lemma lem3124206 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3124207 (x : int) : (term18 x) = (term25 x).
Proof. exact (MK_COMB (@lem3124205) (@lem3124206 x)). Qed.
Lemma lem3124208 (x : int) : (term17 x) = (term25 x).
Proof. exact (TRANS (@lem3124200 x) (@lem3124207 x)). Qed.
Lemma lem3124209 (x : int) : (term25 x) = term10.
Proof. exact (@lem2416521 x). Qed.
Lemma lem3124210 (x : int) : (term17 x) = term10.
Proof. exact (TRANS (@lem3124208 x) (@lem3124209 x)). Qed.
Lemma lem3124211 (a : int) : (int_add a) = (int_add a).
Proof. exact (eq_refl (int_add a)). Qed.
Lemma lem3124212 (x : int) (a : int) : (term15 a x) = (term26 a).
Proof. exact (MK_COMB (@lem3124211 a) (@lem3124210 x)). Qed.
Lemma lem3124213 (x : int) (a : int) : (term14 a x) = (term26 a).
Proof. exact (TRANS (@lem3124199 a x) (@lem3124212 x a)). Qed.
Lemma lem3124214 (a : int) : (term26 a) = a.
Proof. exact (@lem2416525 a). Qed.
Lemma lem3124216 (x : int) (a : int) : (term14 a x) = a.
Proof. exact (TRANS (@lem3124213 x a) (@lem3124214 a)). Qed.
Lemma lem3124217 (x : int) (a : int) : (term13 a x) = a.
Proof. exact (TRANS (@lem3124195 a x) (@lem3124216 x a)). Qed.
Lemma lem3124218 (x : int) (a : int) : (term9 a x) = a.
Proof. exact (TRANS (@lem3124194 a x) (@lem3124217 x a)). Qed.
Lemma lem3124219 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem3124220 (x : int) (a : int) : (term48 a x) = (int_sub a).
Proof. exact (MK_COMB (@lem3124219) (@lem3124218 x a)). Qed.
Lemma lem3124221 (x : int) (a : int) (d : int) (n : int) : (term47 a x n d) = (term34 a d n).
Proof. exact (MK_COMB (@lem3124220 x a) (@lem3124183 d n)). Qed.
Lemma lem3124222 (a : int) (d : int) (n : int) : (term34 a d n) = (term35 a d n).
Proof. exact (@lem2416594 a (int_mul d n)). Qed.
Lemma lem3124227 (d : int) (n : int) (a : int) : (term35 a d n) = (term36 d n a).
Proof. exact (@lem2416563 (term37 d n) a). Qed.
Lemma lem3124228 (d : int) (n : int) (a : int) : (term34 a d n) = (term36 d n a).
Proof. exact (TRANS (@lem3124222 a d n) (@lem3124227 d n a)). Qed.
Lemma lem3124229 (x : int) (d : int) (n : int) (a : int) : (term47 a x n d) = (term36 d n a).
Proof. exact (TRANS (@lem3124221 x a d n) (@lem3124228 d n a)). Qed.
Lemma lem3124230 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3124231 (x : int) (d : int) (n : int) (a : int) : (term49 a x n d) = (term39 d n a).
Proof. exact (MK_COMB (@lem3124230) (@lem3124229 x d n a)). Qed.
Lemma lem3124232 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3124233 (x : int) (d : int) (n : int) (a : int) : ((term47 a x n d) = term10) = ((term36 d n a) = term10).
Proof. exact (MK_COMB (@lem3124231 x d n a) (@lem3124232)). Qed.
Lemma lem3124234 (x : int) (d : int) (n : int) (a : int) : ((term9 a x) = (int_mul n d)) = ((term36 d n a) = term10).
Proof. exact (TRANS (@lem3124176 a x n d) (@lem3124233 x d n a)). Qed.
Lemma lem3124235 (x : int) (n : int) (a : int) : (term50 a x n) = (term51 n a).
Proof. exact (fun_ext (fun d : int => @lem3124234 x d n a)). Qed.
Lemma lem3124236 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3124237 (x : int) (n : int) (a : int) : (term5 a x n) = (term52 n a).
Proof. exact (MK_COMB (@lem3124236) (@lem3124235 x n a)). Qed.
Lemma lem3124238 (x : int) (x' : int) (n : int) (a : int) : (term53 x' a x n) = (term54 x' n a).
Proof. exact (MK_COMB (@lem3124173 n x' a) (@lem3124237 x n a)). Qed.
Lemma lem3124239 (x' : int) (a : int) (x : int) (n : int) : (term54 x' n a) = (term53 x' a x n).
Proof. exact (SYM (@lem3124238 x x' n a)). Qed.
Lemma lem3124268 (d : int) (n : int) (a : int) (h1 : (term29 d n a) = term10) : (term29 d n a) = term10.
Proof. exact (h1). Qed.
Lemma lem3124269 (n : int) (x' : int) (a : int) (h1 : (term29 n x' a) = term10) : (term29 n x' a) = term10.
Proof. exact (h1). Qed.
Lemma lem3124273 (n : int) (_32420 : int) (a : int) : ((term36 n _32420 a) = term10) = ((term36 n _32420 a) = term10).
Proof. exact (eq_refl ((term36 n _32420 a) = term10)). Qed.
Lemma lem3124274 (n : int) (a : int) : (term41 n a) = (term41 n a).
Proof. exact (fun_ext (fun _32420 : int => @lem3124273 n _32420 a)). Qed.
Lemma lem3124275 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3124277 (n : int) (a : int) : (term42 n a) = (term42 n a).
Proof. exact (MK_COMB (@lem3124275) (@lem3124274 n a)). Qed.
Lemma lem3124278 (n : int) (a : int) : (term42 n a) = (term42 n a).
Proof. exact (SYM (@lem3124277 n a)). Qed.
Lemma lem3124282 (_32421 : int) (n : int) (a : int) : ((term36 _32421 n a) = term10) = ((term36 _32421 n a) = term10).
Proof. exact (eq_refl ((term36 _32421 n a) = term10)). Qed.
Lemma lem3124283 (n : int) (a : int) : (term51 n a) = (term51 n a).
Proof. exact (fun_ext (fun _32421 : int => @lem3124282 _32421 n a)). Qed.
Lemma lem3124284 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3124286 (n : int) (a : int) : (term52 n a) = (term52 n a).
Proof. exact (MK_COMB (@lem3124284) (@lem3124283 n a)). Qed.
Lemma lem3124287 (n : int) (a : int) : (term52 n a) = (term52 n a).
Proof. exact (SYM (@lem3124286 n a)). Qed.
Lemma lem3124289 (x : int) (y : int) : (x = y) = ((int_sub x y) = term10).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem3124290 (n : int) (_32420 : int) (a : int) : ((term36 n _32420 a) = term10) = ((term55 n _32420 a) = term10).
Proof. exact (@lem3124289 (term36 n _32420 a) term10). Qed.
Lemma lem3124291 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3124292 (a : int) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3124299 (_32420 : int) (n : int) : (int_mul n _32420) = (int_mul _32420 n).
Proof. exact (@lem2416549 _32420 n). Qed.
Lemma lem3124302 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem3124305 (_32420 : int) (n : int) : (term37 n _32420) = (term37 _32420 n).
Proof. exact (MK_COMB (@lem3124302) (@lem3124299 _32420 n)). Qed.
Lemma lem3124306 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3124307 (_32420 : int) (n : int) : (term57 n _32420) = (term57 _32420 n).
Proof. exact (MK_COMB (@lem3124306) (@lem3124305 _32420 n)). Qed.
Lemma lem3124310 (_32420 : int) (n : int) (a : int) : (term36 n _32420 a) = (term36 _32420 n a).
Proof. exact (MK_COMB (@lem3124307 _32420 n) (@lem3124292 a)). Qed.
Lemma lem3124311 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem3124312 (_32420 : int) (n : int) (a : int) : (term58 n _32420 a) = (term58 _32420 n a).
Proof. exact (MK_COMB (@lem3124311) (@lem3124310 _32420 n a)). Qed.
Lemma lem3124313 (_32420 : int) (n : int) (a : int) : (term55 n _32420 a) = (term55 _32420 n a).
Proof. exact (MK_COMB (@lem3124312 _32420 n a) (@lem3124291)). Qed.
Lemma lem3124314 (_32420 : int) (n : int) (a : int) : (term55 _32420 n a) = (term59 _32420 n a).
Proof. exact (@lem2416594 (term36 _32420 n a) term10). Qed.
Lemma lem3124316 (x : nat) : (term60 x) = term10.
Proof. exact (proj2 (@lem2405764 x)). Qed.
Lemma lem3124317 : term61 = term10.
Proof. exact (@lem3124316 term22). Qed.
Lemma lem3124318 (_32420 : int) (n : int) (a : int) : (term62 _32420 n a) = (term62 _32420 n a).
Proof. exact (eq_refl (term62 _32420 n a)). Qed.
Lemma lem3124319 (_32420 : int) (n : int) (a : int) : (term59 _32420 n a) = (term63 _32420 n a).
Proof. exact (MK_COMB (@lem3124318 _32420 n a) (@lem3124317)). Qed.
Lemma lem3124320 (_32420 : int) (n : int) (a : int) : (term63 _32420 n a) = (term36 _32420 n a).
Proof. exact (@lem2416525 (term36 _32420 n a)). Qed.
Lemma lem3124321 (_32420 : int) (n : int) (a : int) : (term59 _32420 n a) = (term36 _32420 n a).
Proof. exact (TRANS (@lem3124319 _32420 n a) (@lem3124320 _32420 n a)). Qed.
Lemma lem3124322 (_32420 : int) (n : int) (a : int) : (term55 _32420 n a) = (term36 _32420 n a).
Proof. exact (TRANS (@lem3124314 _32420 n a) (@lem3124321 _32420 n a)). Qed.
Lemma lem3124323 (_32420 : int) (n : int) (a : int) : (term55 n _32420 a) = (term36 _32420 n a).
Proof. exact (TRANS (@lem3124313 _32420 n a) (@lem3124322 _32420 n a)). Qed.
Lemma lem3124324 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3124325 (_32420 : int) (n : int) (a : int) : (term64 n _32420 a) = (term39 _32420 n a).
Proof. exact (MK_COMB (@lem3124324) (@lem3124323 _32420 n a)). Qed.
Lemma lem3124326 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3124327 (_32420 : int) (n : int) (a : int) : ((term55 n _32420 a) = term10) = ((term36 _32420 n a) = term10).
Proof. exact (MK_COMB (@lem3124325 _32420 n a) (@lem3124326)). Qed.
Lemma lem3124328 (_32420 : int) (n : int) (a : int) : ((term36 n _32420 a) = term10) = ((term36 _32420 n a) = term10).
Proof. exact (TRANS (@lem3124290 n _32420 a) (@lem3124327 _32420 n a)). Qed.
Lemma lem3124329 (n : int) (a : int) : (term41 n a) = (term51 n a).
Proof. exact (fun_ext (fun _32420 : int => @lem3124328 _32420 n a)). Qed.
Lemma lem3124330 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3124331 (n : int) (a : int) : (term42 n a) = (term52 n a).
Proof. exact (MK_COMB (@lem3124330) (@lem3124329 n a)). Qed.
Lemma lem3124332 (n : int) (a : int) : (term52 n a) = (term42 n a).
Proof. exact (SYM (@lem3124331 n a)). Qed.
Lemma lem3124334 (x : int) (y : int) : (x = y) = ((int_sub x y) = term10).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem3124335 (_32421 : int) (n : int) (a : int) : ((term36 _32421 n a) = term10) = ((term55 _32421 n a) = term10).
Proof. exact (@lem3124334 (term36 _32421 n a) term10). Qed.
Lemma lem3124359 (_32421 : int) (n : int) (a : int) : (term55 _32421 n a) = (term59 _32421 n a).
Proof. exact (@lem2416594 (term36 _32421 n a) term10). Qed.
Lemma lem3124361 (x : nat) : (term60 x) = term10.
Proof. exact (proj2 (@lem2405764 x)). Qed.
Lemma lem3124362 : term61 = term10.
Proof. exact (@lem3124361 term22). Qed.
Lemma lem3124363 (_32421 : int) (n : int) (a : int) : (term62 _32421 n a) = (term62 _32421 n a).
Proof. exact (eq_refl (term62 _32421 n a)). Qed.
Lemma lem3124364 (_32421 : int) (n : int) (a : int) : (term59 _32421 n a) = (term63 _32421 n a).
Proof. exact (MK_COMB (@lem3124363 _32421 n a) (@lem3124362)). Qed.
Lemma lem3124365 (_32421 : int) (n : int) (a : int) : (term63 _32421 n a) = (term36 _32421 n a).
Proof. exact (@lem2416525 (term36 _32421 n a)). Qed.
Lemma lem3124366 (_32421 : int) (n : int) (a : int) : (term59 _32421 n a) = (term36 _32421 n a).
Proof. exact (TRANS (@lem3124364 _32421 n a) (@lem3124365 _32421 n a)). Qed.
Lemma lem3124368 (_32421 : int) (n : int) (a : int) : (term55 _32421 n a) = (term36 _32421 n a).
Proof. exact (TRANS (@lem3124359 _32421 n a) (@lem3124366 _32421 n a)). Qed.
Lemma lem3124369 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3124370 (_32421 : int) (n : int) (a : int) : (term64 _32421 n a) = (term39 _32421 n a).
Proof. exact (MK_COMB (@lem3124369) (@lem3124368 _32421 n a)). Qed.
Lemma lem3124371 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3124372 (_32421 : int) (n : int) (a : int) : ((term55 _32421 n a) = term10) = ((term36 _32421 n a) = term10).
Proof. exact (MK_COMB (@lem3124370 _32421 n a) (@lem3124371)). Qed.
Lemma lem3124373 (_32421 : int) (n : int) (a : int) : ((term36 _32421 n a) = term10) = ((term36 _32421 n a) = term10).
Proof. exact (TRANS (@lem3124335 _32421 n a) (@lem3124372 _32421 n a)). Qed.
Lemma lem3124374 (n : int) (a : int) : (term51 n a) = (term51 n a).
Proof. exact (fun_ext (fun _32421 : int => @lem3124373 _32421 n a)). Qed.
Lemma lem3124375 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3124376 (n : int) (a : int) : (term52 n a) = (term52 n a).
Proof. exact (MK_COMB (@lem3124375) (@lem3124374 n a)). Qed.
Lemma lem3124377 (n : int) (a : int) : (term52 n a) = (term52 n a).
Proof. exact (SYM (@lem3124376 n a)). Qed.
Lemma lem3124399 (d : int) (n : int) (a : int) : (term65 d n a) = (term65 d n a).
Proof. exact (eq_refl (term65 d n a)). Qed.
Lemma lem3124400 (d : int) (n : int) : (term66 d n) = (term66 d n).
Proof. exact (fun_ext (fun a : int => @lem3124399 d n a)). Qed.
Lemma lem3124401 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3124402 (d : int) (n : int) : (term67 d n) = (term67 d n).
Proof. exact (MK_COMB (@lem3124401) (@lem3124400 d n)). Qed.
Lemma lem3124403 (d : int) : (term68 d) = (term68 d).
Proof. exact (fun_ext (fun n : int => @lem3124402 d n)). Qed.
Lemma lem3124404 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3124405 (d : int) : (term69 d) = (term69 d).
Proof. exact (MK_COMB (@lem3124404) (@lem3124403 d)). Qed.
Lemma lem3124406 : term70 = term70.
Proof. exact (fun_ext (fun d : int => @lem3124405 d)). Qed.
Lemma lem3124407 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3124408 : term71 = term71.
Proof. exact (MK_COMB (@lem3124407) (@lem3124406)). Qed.
Lemma lem3124409 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3124411 : term72 = term72.
Proof. exact (MK_COMB (@lem3124409) (@lem3124408)). Qed.
Lemma lem3124418 (d : int) (n : int) (a : int) : (term73 d n a) = (term74 d n a).
Proof. exact (@lem17362 ((term29 d n a) = term10) ((term75 d n a) = term10)). Qed.
Lemma lem3124419 (P : int -> Prop) : (term76 P) = (term77 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3124420 (d : int) (n : int) : (term78 d n) = (term79 d n).
Proof. exact (@lem3124419 (term66 d n)). Qed.
Lemma lem3124421 (d : int) (n : int) (a : int) : (term80 d n a) = (term65 d n a).
Proof. exact (eq_refl (term80 d n a)). Qed.
Lemma lem3124422 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3124423 (d : int) (n : int) (a : int) : (term81 d n a) = (term73 d n a).
Proof. exact (MK_COMB (@lem3124422) (@lem3124421 d n a)). Qed.
Lemma lem3124424 (d : int) (n : int) (a : int) : (term81 d n a) = (term74 d n a).
Proof. exact (TRANS (@lem3124423 d n a) (@lem3124418 d n a)). Qed.
Lemma lem3124425 (d : int) (n : int) : (term82 d n) = (term83 d n).
Proof. exact (fun_ext (fun a : int => @lem3124424 d n a)). Qed.
Lemma lem3124426 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3124427 (d : int) (n : int) : (term79 d n) = (term84 d n).
Proof. exact (MK_COMB (@lem3124426) (@lem3124425 d n)). Qed.
Lemma lem3124428 (d : int) (n : int) : (term78 d n) = (term84 d n).
Proof. exact (TRANS (@lem3124420 d n) (@lem3124427 d n)). Qed.
Lemma lem3124429 (P : int -> Prop) : (term76 P) = (term77 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3124430 (d : int) : (term85 d) = (term86 d).
Proof. exact (@lem3124429 (term68 d)). Qed.
Lemma lem3124431 (d : int) (n : int) : (term87 d n) = (term67 d n).
Proof. exact (eq_refl (term87 d n)). Qed.
Lemma lem3124432 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3124433 (d : int) (n : int) : (term88 d n) = (term78 d n).
Proof. exact (MK_COMB (@lem3124432) (@lem3124431 d n)). Qed.
Lemma lem3124434 (d : int) (n : int) : (term88 d n) = (term84 d n).
Proof. exact (TRANS (@lem3124433 d n) (@lem3124428 d n)). Qed.
Lemma lem3124435 (d : int) : (term89 d) = (term90 d).
Proof. exact (fun_ext (fun n : int => @lem3124434 d n)). Qed.
Lemma lem3124436 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3124437 (d : int) : (term86 d) = (term91 d).
Proof. exact (MK_COMB (@lem3124436) (@lem3124435 d)). Qed.
Lemma lem3124438 (d : int) : (term85 d) = (term91 d).
Proof. exact (TRANS (@lem3124430 d) (@lem3124437 d)). Qed.
Lemma lem3124439 (P : int -> Prop) : (term76 P) = (term77 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3124440 : term72 = term92.
Proof. exact (@lem3124439 term70). Qed.
Lemma lem3124441 (d : int) : (term93 d) = (term69 d).
Proof. exact (eq_refl (term93 d)). Qed.
Lemma lem3124442 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3124443 (d : int) : (term94 d) = (term85 d).
Proof. exact (MK_COMB (@lem3124442) (@lem3124441 d)). Qed.
Lemma lem3124444 (d : int) : (term94 d) = (term91 d).
Proof. exact (TRANS (@lem3124443 d) (@lem3124438 d)). Qed.
Lemma lem3124445 : term95 = term96.
Proof. exact (fun_ext (fun d : int => @lem3124444 d)). Qed.
Lemma lem3124446 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3124447 : term92 = term97.
Proof. exact (MK_COMB (@lem3124446) (@lem3124445)). Qed.
Lemma lem3124448 : term72 = term97.
Proof. exact (TRANS (@lem3124440) (@lem3124447)). Qed.
Lemma lem3124453 : term72 = term97.
Proof. exact (TRANS (@lem3124411) (@lem3124448)). Qed.
Lemma lem3124461 (d : int) (n : int) (a : int) (h1 : term74 d n a) : term74 d n a.
Proof. exact (h1). Qed.
Lemma lem3124462 (d : int) (n : int) (a : int) (h1 : term74 d n a) : term98 d n a.
Proof. exact (proj2 (@lem3124461 d n a h1)). Qed.
Lemma lem3124463 (d : int) (n : int) (a : int) (h1 : term74 d n a) : (term29 d n a) = term10.
Proof. exact (proj1 (@lem3124461 d n a h1)). Qed.
Lemma lem3124464 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3124465 (a : int) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3124466 (n : int) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3124473 (d : int) : (term99 d) = d.
Proof. exact (@lem2416535 d). Qed.
Lemma lem3124474 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3124475 (d : int) : (term100 d) = (int_mul d).
Proof. exact (MK_COMB (@lem3124474) (@lem3124473 d)). Qed.
Lemma lem3124478 (d : int) (n : int) : (term101 d n) = (int_mul d n).
Proof. exact (MK_COMB (@lem3124475 d) (@lem3124466 n)). Qed.
Lemma lem3124481 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem3124484 (d : int) (n : int) : (term102 d n) = (term37 d n).
Proof. exact (MK_COMB (@lem3124481) (@lem3124478 d n)). Qed.
Lemma lem3124485 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3124486 (d : int) (n : int) : (term103 d n) = (term57 d n).
Proof. exact (MK_COMB (@lem3124485) (@lem3124484 d n)). Qed.
Lemma lem3124489 (d : int) (n : int) (a : int) : (term75 d n a) = (term36 d n a).
Proof. exact (MK_COMB (@lem3124486 d n) (@lem3124465 a)). Qed.
Lemma lem3124490 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3124491 (d : int) (n : int) (a : int) : (term104 d n a) = (term39 d n a).
Proof. exact (MK_COMB (@lem3124490) (@lem3124489 d n a)). Qed.
Lemma lem3124492 (d : int) (n : int) (a : int) : ((term75 d n a) = term10) = ((term36 d n a) = term10).
Proof. exact (MK_COMB (@lem3124491 d n a) (@lem3124464)). Qed.
Lemma lem3124493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3124494 (d : int) (n : int) (a : int) : (term98 d n a) = (term105 d n a).
Proof. exact (MK_COMB (@lem3124493) (@lem3124492 d n a)). Qed.
Lemma lem3124495 (d : int) (n : int) (a : int) (h1 : term74 d n a) : term105 d n a.
Proof. exact (EQ_MP (@lem3124494 d n a) (@lem3124462 d n a h1)). Qed.
Lemma lem3124496 (d : int) (n : int) (a : int) (h1 : term74 d n a) : term106 d n a.
Proof. exact (conj (@lem3124495 d n a h1) (@lem2427026)). Qed.
Lemma lem3124498 (a : int) (d : int) (b : int) (c : int) : (term107 a b c d) = (term108 a d b c).
Proof. exact (EQ_MP (@lem2427015 a d b c) (@lem2427014 a b c d)). Qed.
Lemma lem3124499 (d : int) (n : int) (a : int) : (term106 d n a) = (term109 d n a).
Proof. exact (@lem3124498 (term36 d n a) term10 term10 term110). Qed.
Lemma lem3124500 (d : int) (n : int) (a : int) (h1 : term74 d n a) : term109 d n a.
Proof. exact (EQ_MP (@lem3124499 d n a) (@lem3124496 d n a h1)). Qed.
Lemma lem3124501 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem3124502 (d : int) (n : int) (a : int) (h1 : term74 d n a) : (term111 d n a) = term112.
Proof. exact (MK_COMB (@lem3124501) (@lem3124463 d n a h1)). Qed.
Lemma lem3124503 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem3124504 (d : int) (n : int) (a : int) (h1 : term74 d n a) : (term114 d n a) = term115.
Proof. exact (MK_COMB (@lem3124503) (@lem3124463 d n a h1)). Qed.
Lemma lem3124505 (d : int) (n : int) (a : int) (h1 : term74 d n a) : term112 = (term111 d n a).
Proof. exact (SYM (@lem3124502 d n a h1)). Qed.
Lemma lem3124506 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3124507 (d : int) (n : int) (a : int) (h1 : term74 d n a) : term116 = (term117 d n a).
Proof. exact (MK_COMB (@lem3124506) (@lem3124505 d n a h1)). Qed.
Lemma lem3124508 (d : int) (n : int) (a : int) (h1 : term74 d n a) : (term118 d n a) = (term119 d n a).
Proof. exact (MK_COMB (@lem3124507 d n a h1) (@lem3124504 d n a h1)). Qed.
Lemma lem3124509 (d : int) (n : int) (a : int) (h1 : term74 d n a) : term120 d n a.
Proof. exact (conj (@lem3124508 d n a h1) (@lem3124500 d n a h1)). Qed.
Lemma lem3124511 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem3124512 : (term110 = term10) = (term22 = (NUMERAL 0)).
Proof. exact (@lem3124511 term22 (NUMERAL 0)). Qed.
Lemma lem3124513 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3124514 (h1 : term121 = (BIT1 0)) : (term22 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3124515 : (term121 = (BIT1 0)) = ((term22 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3124514 h1) (fun h1 : (term22 = (NUMERAL 0)) = False => @lem3124513)). Qed.
Lemma lem3124516 : (term22 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3124515) (@lem3124513)). Qed.
Lemma lem3124517 : (term110 = term10) = False.
Proof. exact (TRANS (@lem3124512) (@lem3124516)). Qed.
Lemma lem3124518 : term122.
Proof. exact (@lem93 (term110 = term10)). Qed.
Lemma lem3124519 : term123.
Proof. exact (@lem3124518 (@lem3124517)). Qed.
Lemma lem3124520 (h1 : term124) : term124.
Proof. exact (h1). Qed.
Lemma lem3124521 (n : int) (h1 : term124) : term125 n.
Proof. exact (@lem3124520 h1 n). Qed.
Lemma lem3124522 (n : int) : (term125 n) = (term126 n).
Proof. exact (eq_refl (term125 n)). Qed.
Lemma lem3124523 (n : int) (h1 : term124) : term126 n.
Proof. exact (EQ_MP (@lem3124522 n) (@lem3124521 n h1)). Qed.
Lemma lem3124524 (n : int) (a : int) (h1 : term124) : term127 n a.
Proof. exact (@lem3124523 n h1 a). Qed.
Lemma lem3124525 (a : int) (n : int) : (term127 n a) = (term128 a n).
Proof. exact (eq_refl (term127 n a)). Qed.
Lemma lem3124526 (a : int) (n : int) (h1 : term124) : term128 a n.
Proof. exact (EQ_MP (@lem3124525 a n) (@lem3124524 n a h1)). Qed.
Lemma lem3124527 (a : int) (n : int) (b : int) (h1 : term124) : term129 a n b.
Proof. exact (@lem3124526 a n h1 b). Qed.
Lemma lem3124528 (a : int) (b : int) (n : int) : (term129 a n b) = (term130 a b n).
Proof. exact (eq_refl (term129 a n b)). Qed.
Lemma lem3124529 (a : int) (b : int) (n : int) (h1 : term124) : term130 a b n.
Proof. exact (EQ_MP (@lem3124528 a b n) (@lem3124527 a n b h1)). Qed.
Lemma lem3124530 (a : int) (b : int) (n : int) (c : int) (h1 : term124) : term131 a b n c.
Proof. exact (@lem3124529 a b n h1 c). Qed.
Lemma lem3124531 (a : int) (c : int) (b : int) (n : int) : (term131 a b n c) = (term132 a c b n).
Proof. exact (eq_refl (term131 a b n c)). Qed.
Lemma lem3124532 (a : int) (c : int) (b : int) (n : int) (h1 : term124) : term132 a c b n.
Proof. exact (EQ_MP (@lem3124531 a c b n) (@lem3124530 a b n c h1)). Qed.
Lemma lem3124533 (a : int) (c : int) (b : int) (n : int) (d : int) (h1 : term124) : term133 a c b n d.
Proof. exact (@lem3124532 a c b n h1 d). Qed.
Lemma lem3124534 (a : int) (c : int) (b : int) (n : int) (d : int) : (term133 a c b n d) = (term134 a c b n d).
Proof. exact (eq_refl (term133 a c b n d)). Qed.
Lemma lem3124535 (a : int) (c : int) (b : int) (n : int) (d : int) (h1 : term124) : term134 a c b n d.
Proof. exact (EQ_MP (@lem3124534 a c b n d) (@lem3124533 a c b n d h1)). Qed.
Lemma lem3124536 (n : int) (h1 : term135 n) : term135 n.
Proof. exact (h1). Qed.
Lemma lem3124537 (a : int) (c : int) (b : int) (d : int) (n : int) (h1 : term124) (h2 : term135 n) : term136 a c b n d.
Proof. exact (@lem3124535 a c b n d h1 (@lem3124536 n h2)). Qed.
Lemma lem3124538 (a : int) (c : int) (b : int) (n : int) (h1 : term124) (h2 : term135 n) : term137 a c b n.
Proof. exact (fun d : int => @lem3124537 a c b d n h1 h2). Qed.
Lemma lem3124539 (a : int) (b : int) (n : int) (h1 : term124) (h2 : term135 n) : term138 a b n.
Proof. exact (fun c : int => @lem3124538 a c b n h1 h2). Qed.
Lemma lem3124540 (a : int) (n : int) (h1 : term124) (h2 : term135 n) : term139 a n.
Proof. exact (fun b : int => @lem3124539 a b n h1 h2). Qed.
Lemma lem3124541 (n : int) (h1 : term124) (h2 : term135 n) : term140 n.
Proof. exact (fun a : int => @lem3124540 a n h1 h2). Qed.
Lemma lem3124542 (n : int) (h1 : term124) : term141 n.
Proof. exact (fun h0 : term135 n => @lem3124541 n h1 h0). Qed.
Lemma lem3124543 (h1 : term124) : term142.
Proof. exact (fun n : int => @lem3124542 n h1). Qed.
Lemma lem3124544 : term143.
Proof. exact (fun h0 : term124 => @lem3124543 h0). Qed.
Lemma lem3124545 : term142.
Proof. exact (@lem3124544 (@lem2427003)). Qed.
Lemma lem3124546 (n : int) : term144 n.
Proof. exact (@lem3124545 n). Qed.
Lemma lem3124547 (n : int) : (term144 n) = (term141 n).
Proof. exact (eq_refl (term144 n)). Qed.
Lemma lem3124550 (n : int) : term141 n.
Proof. exact (EQ_MP (@lem3124547 n) (@lem3124546 n)). Qed.
Lemma lem3124551 : term145.
Proof. exact (@lem3124550 term110). Qed.
Lemma lem3124552 : term146.
Proof. exact (@lem3124551 (@lem3124519)). Qed.
Lemma lem3124553 (a : int) : term147 a.
Proof. exact (@lem3124552 a). Qed.
Lemma lem3124554 (a : int) : (term147 a) = (term148 a).
Proof. exact (eq_refl (term147 a)). Qed.
Lemma lem3124555 (a : int) : term148 a.
Proof. exact (EQ_MP (@lem3124554 a) (@lem3124553 a)). Qed.
Lemma lem3124556 (a : int) (b : int) : term149 a b.
Proof. exact (@lem3124555 a b). Qed.
Lemma lem3124557 (a : int) (b : int) : (term149 a b) = (term150 a b).
Proof. exact (eq_refl (term149 a b)). Qed.
Lemma lem3124558 (a : int) (b : int) : term150 a b.
Proof. exact (EQ_MP (@lem3124557 a b) (@lem3124556 a b)). Qed.
Lemma lem3124559 (a : int) (b : int) (c : int) : term151 a b c.
Proof. exact (@lem3124558 a b c). Qed.
Lemma lem3124560 (a : int) (c : int) (b : int) : (term151 a b c) = (term152 a c b).
Proof. exact (eq_refl (term151 a b c)). Qed.
Lemma lem3124561 (a : int) (c : int) (b : int) : term152 a c b.
Proof. exact (EQ_MP (@lem3124560 a c b) (@lem3124559 a b c)). Qed.
Lemma lem3124562 (a : int) (c : int) (b : int) (d : int) : term153 a c b d.
Proof. exact (@lem3124561 a c b d). Qed.
Lemma lem3124563 (a : int) (c : int) (b : int) (d : int) : (term153 a c b d) = (term154 a c b d).
Proof. exact (eq_refl (term153 a c b d)). Qed.
Lemma lem3124566 (a : int) (c : int) (b : int) (d : int) : term154 a c b d.
Proof. exact (EQ_MP (@lem3124563 a c b d) (@lem3124562 a c b d)). Qed.
Lemma lem3124567 (d : int) (n : int) (a : int) : term155 d n a.
Proof. exact (@lem3124566 (term118 d n a) (term156 d n a) (term119 d n a) (term157 d n a)). Qed.
Lemma lem3124568 (d : int) (n : int) (a : int) (h1 : term74 d n a) : term158 d n a.
Proof. exact (@lem3124567 d n a (@lem3124509 d n a h1)). Qed.
Lemma lem3124575 : term159 = term10.
Proof. exact (@lem2416531 term110). Qed.
Lemma lem3124600 (d : int) (n : int) (a : int) : (term160 d n a) = term10.
Proof. exact (@lem2416533 (term36 d n a)). Qed.
Lemma lem3124601 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3124602 (d : int) (n : int) (a : int) : (term161 d n a) = term162.
Proof. exact (MK_COMB (@lem3124601) (@lem3124600 d n a)). Qed.
Lemma lem3124603 (d : int) (n : int) (a : int) : (term157 d n a) = term163.
Proof. exact (MK_COMB (@lem3124602 d n a) (@lem3124575)). Qed.
Lemma lem3124604 : term163 = term10.
Proof. exact (@lem2416523 term10). Qed.
Lemma lem3124605 (d : int) (n : int) (a : int) : (term157 d n a) = term10.
Proof. exact (TRANS (@lem3124603 d n a) (@lem3124604)). Qed.
Lemma lem3124608 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem3124609 (d : int) (n : int) (a : int) : (term164 d n a) = term115.
Proof. exact (MK_COMB (@lem3124608) (@lem3124605 d n a)). Qed.
Lemma lem3124610 : term115 = term10.
Proof. exact (@lem2416533 term110). Qed.
Lemma lem3124611 (d : int) (n : int) (a : int) : (term164 d n a) = term10.
Proof. exact (TRANS (@lem3124609 d n a) (@lem3124610)). Qed.
Lemma lem3124618 : term115 = term10.
Proof. exact (@lem2416533 term110). Qed.
Lemma lem3124643 (d : int) (n : int) (a : int) : (term111 d n a) = term10.
Proof. exact (@lem2416531 (term29 d n a)). Qed.
Lemma lem3124644 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3124645 (d : int) (n : int) (a : int) : (term117 d n a) = term162.
Proof. exact (MK_COMB (@lem3124644) (@lem3124643 d n a)). Qed.
Lemma lem3124646 (d : int) (n : int) (a : int) : (term119 d n a) = term163.
Proof. exact (MK_COMB (@lem3124645 d n a) (@lem3124618)). Qed.
Lemma lem3124647 : term163 = term10.
Proof. exact (@lem2416523 term10). Qed.
Lemma lem3124648 (d : int) (n : int) (a : int) : (term119 d n a) = term10.
Proof. exact (TRANS (@lem3124646 d n a) (@lem3124647)). Qed.
Lemma lem3124649 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3124650 (d : int) (n : int) (a : int) : (term165 d n a) = term162.
Proof. exact (MK_COMB (@lem3124649) (@lem3124648 d n a)). Qed.
Lemma lem3124651 (d : int) (n : int) (a : int) : (term166 d n a) = term163.
Proof. exact (MK_COMB (@lem3124650 d n a) (@lem3124611 d n a)). Qed.
Lemma lem3124652 : term163 = term10.
Proof. exact (@lem2416523 term10). Qed.
Lemma lem3124653 (d : int) (n : int) (a : int) : (term166 d n a) = term10.
Proof. exact (TRANS (@lem3124651 d n a) (@lem3124652)). Qed.
Lemma lem3124660 : term112 = term10.
Proof. exact (@lem2416531 term10). Qed.
Lemma lem3124685 (d : int) (n : int) (a : int) : (term167 d n a) = (term36 d n a).
Proof. exact (@lem2416537 (term36 d n a)). Qed.
Lemma lem3124686 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3124687 (d : int) (n : int) (a : int) : (term168 d n a) = (term62 d n a).
Proof. exact (MK_COMB (@lem3124686) (@lem3124685 d n a)). Qed.
Lemma lem3124688 (d : int) (n : int) (a : int) : (term156 d n a) = (term63 d n a).
Proof. exact (MK_COMB (@lem3124687 d n a) (@lem3124660)). Qed.
Lemma lem3124689 (d : int) (n : int) (a : int) : (term63 d n a) = (term36 d n a).
Proof. exact (@lem2416525 (term36 d n a)). Qed.
Lemma lem3124690 (d : int) (n : int) (a : int) : (term156 d n a) = (term36 d n a).
Proof. exact (TRANS (@lem3124688 d n a) (@lem3124689 d n a)). Qed.
Lemma lem3124693 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem3124694 (d : int) (n : int) (a : int) : (term169 d n a) = (term170 d n a).
Proof. exact (MK_COMB (@lem3124693) (@lem3124690 d n a)). Qed.
Lemma lem3124695 (d : int) (n : int) (a : int) : (term170 d n a) = (term36 d n a).
Proof. exact (@lem2416535 (term36 d n a)). Qed.
Lemma lem3124696 (d : int) (n : int) (a : int) : (term169 d n a) = (term36 d n a).
Proof. exact (TRANS (@lem3124694 d n a) (@lem3124695 d n a)). Qed.
Lemma lem3124721 (d : int) (n : int) (a : int) : (term114 d n a) = (term29 d n a).
Proof. exact (@lem2416535 (term29 d n a)). Qed.
Lemma lem3124728 : term112 = term10.
Proof. exact (@lem2416531 term10). Qed.
Lemma lem3124729 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3124730 : term116 = term162.
Proof. exact (MK_COMB (@lem3124729) (@lem3124728)). Qed.
Lemma lem3124731 (d : int) (n : int) (a : int) : (term118 d n a) = (term171 d n a).
Proof. exact (MK_COMB (@lem3124730) (@lem3124721 d n a)). Qed.
Lemma lem3124732 (d : int) (n : int) (a : int) : (term171 d n a) = (term29 d n a).
Proof. exact (@lem2416523 (term29 d n a)). Qed.
Lemma lem3124733 (d : int) (n : int) (a : int) : (term118 d n a) = (term29 d n a).
Proof. exact (TRANS (@lem3124731 d n a) (@lem3124732 d n a)). Qed.
Lemma lem3124734 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3124735 (d : int) (n : int) (a : int) : (term172 d n a) = (term173 d n a).
Proof. exact (MK_COMB (@lem3124734) (@lem3124733 d n a)). Qed.
Lemma lem3124736 (d : int) (n : int) (a : int) : (term174 d n a) = (term175 d n a).
Proof. exact (MK_COMB (@lem3124735 d n a) (@lem3124696 d n a)). Qed.
Lemma lem3124737 (d : int) (n : int) (a : int) : (term175 d n a) = (term176 d n a).
Proof. exact (@lem2416555 (int_mul d n) (term37 d n) (term16 a) a). Qed.
Lemma lem3124738 (d : int) (n : int) : (term177 d n) = (term178 d n).
Proof. exact (@lem2416517 term19 (int_mul d n)). Qed.
Lemma lem3124740 (m : nat) : (term20 m) = term10.
Proof. exact (proj1 (@lem2405813 m)). Qed.
Lemma lem3124741 : term21 = term10.
Proof. exact (@lem3124740 term22). Qed.
Lemma lem3124742 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3124743 : term23 = term24.
Proof. exact (MK_COMB (@lem3124742) (@lem3124741)). Qed.
Lemma lem3124744 (d : int) (n : int) : (int_mul d n) = (int_mul d n).
Proof. exact (eq_refl (int_mul d n)). Qed.
Lemma lem3124745 (d : int) (n : int) : (term178 d n) = (term179 d n).
Proof. exact (MK_COMB (@lem3124743) (@lem3124744 d n)). Qed.
Lemma lem3124746 (d : int) (n : int) : (term177 d n) = (term179 d n).
Proof. exact (TRANS (@lem3124738 d n) (@lem3124745 d n)). Qed.
Lemma lem3124747 (d : int) (n : int) : (term179 d n) = term10.
Proof. exact (@lem2416521 (int_mul d n)). Qed.
Lemma lem3124748 (d : int) (n : int) : (term177 d n) = term10.
Proof. exact (TRANS (@lem3124746 d n) (@lem3124747 d n)). Qed.
Lemma lem3124749 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3124750 (d : int) (n : int) : (term180 d n) = term162.
Proof. exact (MK_COMB (@lem3124749) (@lem3124748 d n)). Qed.
Lemma lem3124751 (a : int) : (term181 a) = (term18 a).
Proof. exact (@lem2416515 term19 a). Qed.
Lemma lem3124753 (m : nat) : (term20 m) = term10.
Proof. exact (proj1 (@lem2405813 m)). Qed.
Lemma lem3124754 : term21 = term10.
Proof. exact (@lem3124753 term22). Qed.
Lemma lem3124755 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3124756 : term23 = term24.
Proof. exact (MK_COMB (@lem3124755) (@lem3124754)). Qed.
Lemma lem3124757 (a : int) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3124758 (a : int) : (term18 a) = (term25 a).
Proof. exact (MK_COMB (@lem3124756) (@lem3124757 a)). Qed.
Lemma lem3124759 (a : int) : (term181 a) = (term25 a).
Proof. exact (TRANS (@lem3124751 a) (@lem3124758 a)). Qed.
Lemma lem3124760 (a : int) : (term25 a) = term10.
Proof. exact (@lem2416521 a). Qed.
Lemma lem3124761 (a : int) : (term181 a) = term10.
Proof. exact (TRANS (@lem3124759 a) (@lem3124760 a)). Qed.
Lemma lem3124762 (d : int) (n : int) (a : int) : (term176 d n a) = term163.
Proof. exact (MK_COMB (@lem3124750 d n) (@lem3124761 a)). Qed.
Lemma lem3124763 (d : int) (n : int) (a : int) : (term175 d n a) = term163.
Proof. exact (TRANS (@lem3124737 d n a) (@lem3124762 d n a)). Qed.
Lemma lem3124764 : term163 = term10.
Proof. exact (@lem2416523 term10). Qed.
Lemma lem3124765 (d : int) (n : int) (a : int) : (term175 d n a) = term10.
Proof. exact (TRANS (@lem3124763 d n a) (@lem3124764)). Qed.
Lemma lem3124766 (d : int) (n : int) (a : int) : (term174 d n a) = term10.
Proof. exact (TRANS (@lem3124736 d n a) (@lem3124765 d n a)). Qed.
Lemma lem3124767 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3124768 (d : int) (n : int) (a : int) : (term182 d n a) = term183.
Proof. exact (MK_COMB (@lem3124767) (@lem3124766 d n a)). Qed.
Lemma lem3124769 (d : int) (n : int) (a : int) : ((term174 d n a) = (term166 d n a)) = (term10 = term10).
Proof. exact (MK_COMB (@lem3124768 d n a) (@lem3124653 d n a)). Qed.
Lemma lem3124770 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3124771 (d : int) (n : int) (a : int) : (term158 d n a) = term184.
Proof. exact (MK_COMB (@lem3124770) (@lem3124769 d n a)). Qed.
Lemma lem3124772 (d : int) (n : int) (a : int) (h1 : term74 d n a) : term184.
Proof. exact (EQ_MP (@lem3124771 d n a) (@lem3124568 d n a h1)). Qed.
Lemma lem3124773 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3124774 : term185.
Proof. exact (@lem82 (term10 = term10)). Qed.
Lemma lem3124775 (d : int) (n : int) (a : int) (h1 : term74 d n a) : (term10 = term10) = False.
Proof. exact (@lem3124774 (@lem3124772 d n a h1)). Qed.
Lemma lem3124776 (d : int) (n : int) (a : int) (h1 : term74 d n a) : False.
Proof. exact (EQ_MP (@lem3124775 d n a h1) (@lem3124773)). Qed.
Lemma lem3124777 (d : int) (n : int) (a : int) : term186 d n a.
Proof. exact (fun h0 : term74 d n a => @lem3124776 d n a h0). Qed.
Lemma lem3124778 (d : int) (n : int) (a : int) : (term186 d n a) = (term187 d n a).
Proof. exact (@lem69 (term74 d n a)). Qed.
Lemma lem3124779 (d : int) (n : int) (a : int) : term187 d n a.
Proof. exact (EQ_MP (@lem3124778 d n a) (@lem3124777 d n a)). Qed.
Lemma lem3124780 (d : int) (n : int) (a : int) : term188 d n a.
Proof. exact (@lem82 (term74 d n a)). Qed.
Lemma lem3124782 (d : int) (n : int) (a : int) : (term74 d n a) = False.
Proof. exact (@lem3124780 d n a (@lem3124779 d n a)). Qed.
Lemma lem3124783 (d : int) (n : int) (a : int) : term189 d n a.
Proof. exact (@lem93 (term74 d n a)). Qed.
Lemma lem3124784 (d : int) (n : int) (a : int) : term187 d n a.
Proof. exact (@lem3124783 d n a (@lem3124782 d n a)). Qed.
Lemma lem3124785 (d : int) (n : int) (a : int) : (term187 d n a) = (term186 d n a).
Proof. exact (@lem62 (term74 d n a)). Qed.
Lemma lem3124786 (d : int) (n : int) (a : int) : term186 d n a.
Proof. exact (EQ_MP (@lem3124785 d n a) (@lem3124784 d n a)). Qed.
Lemma lem3124787 (d : int) (n : int) (a : int) (h1 : term74 d n a) : term74 d n a.
Proof. exact (h1). Qed.
Lemma lem3124788 (d : int) (n : int) (a : int) (h1 : term74 d n a) : False.
Proof. exact (@lem3124786 d n a (@lem3124787 d n a h1)). Qed.
Lemma lem3124789 (d : int) (n : int) (h1 : term84 d n) : term84 d n.
Proof. exact (h1). Qed.
Lemma lem3124790 (d : int) (n : int) (h1 : term84 d n) : False.
Proof. exact (ex_elim (@lem3124789 d n h1) (fun a : int => fun h0 : term83 d n a => @lem3124788 d n a h0)). Qed.
Lemma lem3124791 (d : int) (h1 : term91 d) : term91 d.
Proof. exact (h1). Qed.
Lemma lem3124792 (d : int) (h1 : term91 d) : False.
Proof. exact (ex_elim (@lem3124791 d h1) (fun n : int => fun h0 : term90 d n => @lem3124790 d n h0)). Qed.
Lemma lem3124793 (h1 : term97) : term97.
Proof. exact (h1). Qed.
Lemma lem3124794 (h1 : term97) : False.
Proof. exact (ex_elim (@lem3124793 h1) (fun d : int => fun h0 : term96 d => @lem3124792 d h0)). Qed.
Lemma lem3124795 : term190.
Proof. exact (fun h0 : term97 => @lem3124794 h0). Qed.
Lemma lem3124797 (p : Prop) (q : Prop) : term191 p q.
Proof. exact (EQ_MP (@lem1032627 p q) (@lem1032730 p q)). Qed.
Lemma lem3124798 (q : Prop) : term192 q.
Proof. exact (@lem3124797 term97 q). Qed.
Lemma lem3124801 (q : Prop) : term193 q.
Proof. exact (@lem3124798 q (@lem3124795)). Qed.
Lemma lem3124802 : term194.
Proof. exact (@lem3124801 term71). Qed.
Lemma lem3124803 : term71.
Proof. exact (@lem3124802 (@lem3124453)). Qed.
Lemma lem3124804 (d : int) : term93 d.
Proof. exact (@lem3124803 d). Qed.
Lemma lem3124805 (d : int) : (term93 d) = (term69 d).
Proof. exact (eq_refl (term93 d)). Qed.
Lemma lem3124806 (d : int) : term69 d.
Proof. exact (EQ_MP (@lem3124805 d) (@lem3124804 d)). Qed.
Lemma lem3124807 (d : int) (n : int) : term87 d n.
Proof. exact (@lem3124806 d n). Qed.
Lemma lem3124808 (d : int) (n : int) : (term87 d n) = (term67 d n).
Proof. exact (eq_refl (term87 d n)). Qed.
Lemma lem3124809 (d : int) (n : int) : term67 d n.
Proof. exact (EQ_MP (@lem3124808 d n) (@lem3124807 d n)). Qed.
Lemma lem3124810 (d : int) (n : int) (a : int) : term80 d n a.
Proof. exact (@lem3124809 d n a). Qed.
Lemma lem3124811 (d : int) (n : int) (a : int) : (term80 d n a) = (term65 d n a).
Proof. exact (eq_refl (term80 d n a)). Qed.
Lemma lem3124812 (d : int) (n : int) (a : int) : term65 d n a.
Proof. exact (EQ_MP (@lem3124811 d n a) (@lem3124810 d n a)). Qed.
Lemma lem3124813 (d : int) (n : int) (a : int) (h1 : (term29 d n a) = term10) : (term75 d n a) = term10.
Proof. exact (@lem3124812 d n a (@lem3124268 d n a h1)). Qed.
Lemma lem3124814 (d : int) (n : int) (a : int) (h1 : (term29 d n a) = term10) : term52 n a.
Proof. exact (ex_intro (term51 n a) (term99 d) (@lem3124813 d n a h1)). Qed.
Lemma lem3124836 (x' : int) (n : int) (a : int) : (term195 x' n a) = (term195 x' n a).
Proof. exact (eq_refl (term195 x' n a)). Qed.
Lemma lem3124837 (x' : int) (n : int) : (term196 x' n) = (term196 x' n).
Proof. exact (fun_ext (fun a : int => @lem3124836 x' n a)). Qed.
Lemma lem3124838 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3124839 (x' : int) (n : int) : (term197 x' n) = (term197 x' n).
Proof. exact (MK_COMB (@lem3124838) (@lem3124837 x' n)). Qed.
Lemma lem3124840 (x' : int) : (term198 x') = (term198 x').
Proof. exact (fun_ext (fun n : int => @lem3124839 x' n)). Qed.
Lemma lem3124841 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3124842 (x' : int) : (term199 x') = (term199 x').
Proof. exact (MK_COMB (@lem3124841) (@lem3124840 x')). Qed.
Lemma lem3124843 : term200 = term200.
Proof. exact (fun_ext (fun x' : int => @lem3124842 x')). Qed.
Lemma lem3124844 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3124845 : term201 = term201.
Proof. exact (MK_COMB (@lem3124844) (@lem3124843)). Qed.
Lemma lem3124846 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3124848 : term202 = term202.
Proof. exact (MK_COMB (@lem3124846) (@lem3124845)). Qed.
Lemma lem3124855 (x' : int) (n : int) (a : int) : (term203 x' n a) = (term204 x' n a).
Proof. exact (@lem17362 ((term29 n x' a) = term10) ((term75 x' n a) = term10)). Qed.
Lemma lem3124856 (P : int -> Prop) : (term76 P) = (term77 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3124857 (x' : int) (n : int) : (term205 x' n) = (term206 x' n).
Proof. exact (@lem3124856 (term196 x' n)). Qed.
Lemma lem3124858 (x' : int) (n : int) (a : int) : (term207 x' n a) = (term195 x' n a).
Proof. exact (eq_refl (term207 x' n a)). Qed.
Lemma lem3124859 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3124860 (x' : int) (n : int) (a : int) : (term208 x' n a) = (term203 x' n a).
Proof. exact (MK_COMB (@lem3124859) (@lem3124858 x' n a)). Qed.
Lemma lem3124861 (x' : int) (n : int) (a : int) : (term208 x' n a) = (term204 x' n a).
Proof. exact (TRANS (@lem3124860 x' n a) (@lem3124855 x' n a)). Qed.
Lemma lem3124862 (x' : int) (n : int) : (term209 x' n) = (term210 x' n).
Proof. exact (fun_ext (fun a : int => @lem3124861 x' n a)). Qed.
Lemma lem3124863 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3124864 (x' : int) (n : int) : (term206 x' n) = (term211 x' n).
Proof. exact (MK_COMB (@lem3124863) (@lem3124862 x' n)). Qed.
Lemma lem3124865 (x' : int) (n : int) : (term205 x' n) = (term211 x' n).
Proof. exact (TRANS (@lem3124857 x' n) (@lem3124864 x' n)). Qed.
Lemma lem3124866 (P : int -> Prop) : (term76 P) = (term77 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3124867 (x' : int) : (term212 x') = (term213 x').
Proof. exact (@lem3124866 (term198 x')). Qed.
Lemma lem3124868 (x' : int) (n : int) : (term214 x' n) = (term197 x' n).
Proof. exact (eq_refl (term214 x' n)). Qed.
Lemma lem3124869 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3124870 (x' : int) (n : int) : (term215 x' n) = (term205 x' n).
Proof. exact (MK_COMB (@lem3124869) (@lem3124868 x' n)). Qed.
Lemma lem3124871 (x' : int) (n : int) : (term215 x' n) = (term211 x' n).
Proof. exact (TRANS (@lem3124870 x' n) (@lem3124865 x' n)). Qed.
Lemma lem3124872 (x' : int) : (term216 x') = (term217 x').
Proof. exact (fun_ext (fun n : int => @lem3124871 x' n)). Qed.
Lemma lem3124873 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3124874 (x' : int) : (term213 x') = (term218 x').
Proof. exact (MK_COMB (@lem3124873) (@lem3124872 x')). Qed.
Lemma lem3124875 (x' : int) : (term212 x') = (term218 x').
Proof. exact (TRANS (@lem3124867 x') (@lem3124874 x')). Qed.
Lemma lem3124876 (P : int -> Prop) : (term76 P) = (term77 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3124877 : term202 = term219.
Proof. exact (@lem3124876 term200). Qed.
Lemma lem3124878 (x' : int) : (term220 x') = (term199 x').
Proof. exact (eq_refl (term220 x')). Qed.
Lemma lem3124879 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3124880 (x' : int) : (term221 x') = (term212 x').
Proof. exact (MK_COMB (@lem3124879) (@lem3124878 x')). Qed.
Lemma lem3124881 (x' : int) : (term221 x') = (term218 x').
Proof. exact (TRANS (@lem3124880 x') (@lem3124875 x')). Qed.
Lemma lem3124882 : term222 = term223.
Proof. exact (fun_ext (fun x' : int => @lem3124881 x')). Qed.
Lemma lem3124883 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3124884 : term219 = term224.
Proof. exact (MK_COMB (@lem3124883) (@lem3124882)). Qed.
Lemma lem3124885 : term202 = term224.
Proof. exact (TRANS (@lem3124877) (@lem3124884)). Qed.
Lemma lem3124890 : term202 = term224.
Proof. exact (TRANS (@lem3124848) (@lem3124885)). Qed.
Lemma lem3124898 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : term204 x' n a.
Proof. exact (h1). Qed.
Lemma lem3124899 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : term98 x' n a.
Proof. exact (proj2 (@lem3124898 x' n a h1)). Qed.
Lemma lem3124900 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : (term29 n x' a) = term10.
Proof. exact (proj1 (@lem3124898 x' n a h1)). Qed.
Lemma lem3124901 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3124902 (a : int) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3124903 (n : int) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem3124910 (x' : int) : (term99 x') = x'.
Proof. exact (@lem2416535 x'). Qed.
Lemma lem3124911 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3124912 (x' : int) : (term100 x') = (int_mul x').
Proof. exact (MK_COMB (@lem3124911) (@lem3124910 x')). Qed.
Lemma lem3124913 (x' : int) (n : int) : (term101 x' n) = (int_mul x' n).
Proof. exact (MK_COMB (@lem3124912 x') (@lem3124903 n)). Qed.
Lemma lem3124914 (n : int) (x' : int) : (int_mul x' n) = (int_mul n x').
Proof. exact (@lem2416549 n x'). Qed.
Lemma lem3124915 (n : int) (x' : int) : (term101 x' n) = (int_mul n x').
Proof. exact (TRANS (@lem3124913 x' n) (@lem3124914 n x')). Qed.
Lemma lem3124918 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem3124921 (n : int) (x' : int) : (term102 x' n) = (term37 n x').
Proof. exact (MK_COMB (@lem3124918) (@lem3124915 n x')). Qed.
Lemma lem3124922 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3124923 (n : int) (x' : int) : (term103 x' n) = (term57 n x').
Proof. exact (MK_COMB (@lem3124922) (@lem3124921 n x')). Qed.
Lemma lem3124926 (n : int) (x' : int) (a : int) : (term75 x' n a) = (term36 n x' a).
Proof. exact (MK_COMB (@lem3124923 n x') (@lem3124902 a)). Qed.
Lemma lem3124927 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3124928 (n : int) (x' : int) (a : int) : (term104 x' n a) = (term39 n x' a).
Proof. exact (MK_COMB (@lem3124927) (@lem3124926 n x' a)). Qed.
Lemma lem3124929 (n : int) (x' : int) (a : int) : ((term75 x' n a) = term10) = ((term36 n x' a) = term10).
Proof. exact (MK_COMB (@lem3124928 n x' a) (@lem3124901)). Qed.
Lemma lem3124930 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3124931 (n : int) (x' : int) (a : int) : (term98 x' n a) = (term105 n x' a).
Proof. exact (MK_COMB (@lem3124930) (@lem3124929 n x' a)). Qed.
Lemma lem3124932 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : term105 n x' a.
Proof. exact (EQ_MP (@lem3124931 n x' a) (@lem3124899 x' n a h1)). Qed.
Lemma lem3124933 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : term106 n x' a.
Proof. exact (conj (@lem3124932 x' n a h1) (@lem2427026)). Qed.
Lemma lem3124935 (a : int) (d : int) (b : int) (c : int) : (term107 a b c d) = (term108 a d b c).
Proof. exact (EQ_MP (@lem2427015 a d b c) (@lem2427014 a b c d)). Qed.
Lemma lem3124936 (n : int) (x' : int) (a : int) : (term106 n x' a) = (term109 n x' a).
Proof. exact (@lem3124935 (term36 n x' a) term10 term10 term110). Qed.
Lemma lem3124937 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : term109 n x' a.
Proof. exact (EQ_MP (@lem3124936 n x' a) (@lem3124933 x' n a h1)). Qed.
Lemma lem3124938 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem3124939 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : (term111 n x' a) = term112.
Proof. exact (MK_COMB (@lem3124938) (@lem3124900 x' n a h1)). Qed.
Lemma lem3124940 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem3124941 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : (term114 n x' a) = term115.
Proof. exact (MK_COMB (@lem3124940) (@lem3124900 x' n a h1)). Qed.
Lemma lem3124942 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : term112 = (term111 n x' a).
Proof. exact (SYM (@lem3124939 x' n a h1)). Qed.
Lemma lem3124943 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3124944 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : term116 = (term117 n x' a).
Proof. exact (MK_COMB (@lem3124943) (@lem3124942 x' n a h1)). Qed.
Lemma lem3124945 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : (term118 n x' a) = (term119 n x' a).
Proof. exact (MK_COMB (@lem3124944 x' n a h1) (@lem3124941 x' n a h1)). Qed.
Lemma lem3124946 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : term120 n x' a.
Proof. exact (conj (@lem3124945 x' n a h1) (@lem3124937 x' n a h1)). Qed.
Lemma lem3124948 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem3124949 : (term110 = term10) = (term22 = (NUMERAL 0)).
Proof. exact (@lem3124948 term22 (NUMERAL 0)). Qed.
Lemma lem3124950 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3124951 (h1 : term121 = (BIT1 0)) : (term22 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3124952 : (term121 = (BIT1 0)) = ((term22 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3124951 h1) (fun h1 : (term22 = (NUMERAL 0)) = False => @lem3124950)). Qed.
Lemma lem3124953 : (term22 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3124952) (@lem3124950)). Qed.
Lemma lem3124954 : (term110 = term10) = False.
Proof. exact (TRANS (@lem3124949) (@lem3124953)). Qed.
Lemma lem3124955 : term122.
Proof. exact (@lem93 (term110 = term10)). Qed.
Lemma lem3124956 : term123.
Proof. exact (@lem3124955 (@lem3124954)). Qed.
Lemma lem3124957 (h1 : term124) : term124.
Proof. exact (h1). Qed.
Lemma lem3124958 (n : int) (h1 : term124) : term125 n.
Proof. exact (@lem3124957 h1 n). Qed.
Lemma lem3124959 (n : int) : (term125 n) = (term126 n).
Proof. exact (eq_refl (term125 n)). Qed.
Lemma lem3124960 (n : int) (h1 : term124) : term126 n.
Proof. exact (EQ_MP (@lem3124959 n) (@lem3124958 n h1)). Qed.
Lemma lem3124961 (n : int) (a : int) (h1 : term124) : term127 n a.
Proof. exact (@lem3124960 n h1 a). Qed.
Lemma lem3124962 (a : int) (n : int) : (term127 n a) = (term128 a n).
Proof. exact (eq_refl (term127 n a)). Qed.
Lemma lem3124963 (a : int) (n : int) (h1 : term124) : term128 a n.
Proof. exact (EQ_MP (@lem3124962 a n) (@lem3124961 n a h1)). Qed.
Lemma lem3124964 (a : int) (n : int) (b : int) (h1 : term124) : term129 a n b.
Proof. exact (@lem3124963 a n h1 b). Qed.
Lemma lem3124965 (a : int) (b : int) (n : int) : (term129 a n b) = (term130 a b n).
Proof. exact (eq_refl (term129 a n b)). Qed.
Lemma lem3124966 (a : int) (b : int) (n : int) (h1 : term124) : term130 a b n.
Proof. exact (EQ_MP (@lem3124965 a b n) (@lem3124964 a n b h1)). Qed.
Lemma lem3124967 (a : int) (b : int) (n : int) (c : int) (h1 : term124) : term131 a b n c.
Proof. exact (@lem3124966 a b n h1 c). Qed.
Lemma lem3124968 (a : int) (c : int) (b : int) (n : int) : (term131 a b n c) = (term132 a c b n).
Proof. exact (eq_refl (term131 a b n c)). Qed.
Lemma lem3124969 (a : int) (c : int) (b : int) (n : int) (h1 : term124) : term132 a c b n.
Proof. exact (EQ_MP (@lem3124968 a c b n) (@lem3124967 a b n c h1)). Qed.
Lemma lem3124970 (a : int) (c : int) (b : int) (n : int) (d : int) (h1 : term124) : term133 a c b n d.
Proof. exact (@lem3124969 a c b n h1 d). Qed.
Lemma lem3124971 (a : int) (c : int) (b : int) (n : int) (d : int) : (term133 a c b n d) = (term134 a c b n d).
Proof. exact (eq_refl (term133 a c b n d)). Qed.
Lemma lem3124972 (a : int) (c : int) (b : int) (n : int) (d : int) (h1 : term124) : term134 a c b n d.
Proof. exact (EQ_MP (@lem3124971 a c b n d) (@lem3124970 a c b n d h1)). Qed.
Lemma lem3124973 (n : int) (h1 : term135 n) : term135 n.
Proof. exact (h1). Qed.
Lemma lem3124974 (a : int) (c : int) (b : int) (d : int) (n : int) (h1 : term124) (h2 : term135 n) : term136 a c b n d.
Proof. exact (@lem3124972 a c b n d h1 (@lem3124973 n h2)). Qed.
Lemma lem3124975 (a : int) (c : int) (b : int) (n : int) (h1 : term124) (h2 : term135 n) : term137 a c b n.
Proof. exact (fun d : int => @lem3124974 a c b d n h1 h2). Qed.
Lemma lem3124976 (a : int) (b : int) (n : int) (h1 : term124) (h2 : term135 n) : term138 a b n.
Proof. exact (fun c : int => @lem3124975 a c b n h1 h2). Qed.
Lemma lem3124977 (a : int) (n : int) (h1 : term124) (h2 : term135 n) : term139 a n.
Proof. exact (fun b : int => @lem3124976 a b n h1 h2). Qed.
Lemma lem3124978 (n : int) (h1 : term124) (h2 : term135 n) : term140 n.
Proof. exact (fun a : int => @lem3124977 a n h1 h2). Qed.
Lemma lem3124979 (n : int) (h1 : term124) : term141 n.
Proof. exact (fun h0 : term135 n => @lem3124978 n h1 h0). Qed.
Lemma lem3124980 (h1 : term124) : term142.
Proof. exact (fun n : int => @lem3124979 n h1). Qed.
Lemma lem3124981 : term143.
Proof. exact (fun h0 : term124 => @lem3124980 h0). Qed.
Lemma lem3124982 : term142.
Proof. exact (@lem3124981 (@lem2427003)). Qed.
Lemma lem3124983 (n : int) : term144 n.
Proof. exact (@lem3124982 n). Qed.
Lemma lem3124984 (n : int) : (term144 n) = (term141 n).
Proof. exact (eq_refl (term144 n)). Qed.
Lemma lem3124987 (n : int) : term141 n.
Proof. exact (EQ_MP (@lem3124984 n) (@lem3124983 n)). Qed.
Lemma lem3124988 : term145.
Proof. exact (@lem3124987 term110). Qed.
Lemma lem3124989 : term146.
Proof. exact (@lem3124988 (@lem3124956)). Qed.
Lemma lem3124990 (a : int) : term147 a.
Proof. exact (@lem3124989 a). Qed.
Lemma lem3124991 (a : int) : (term147 a) = (term148 a).
Proof. exact (eq_refl (term147 a)). Qed.
Lemma lem3124992 (a : int) : term148 a.
Proof. exact (EQ_MP (@lem3124991 a) (@lem3124990 a)). Qed.
Lemma lem3124993 (a : int) (b : int) : term149 a b.
Proof. exact (@lem3124992 a b). Qed.
Lemma lem3124994 (a : int) (b : int) : (term149 a b) = (term150 a b).
Proof. exact (eq_refl (term149 a b)). Qed.
Lemma lem3124995 (a : int) (b : int) : term150 a b.
Proof. exact (EQ_MP (@lem3124994 a b) (@lem3124993 a b)). Qed.
Lemma lem3124996 (a : int) (b : int) (c : int) : term151 a b c.
Proof. exact (@lem3124995 a b c). Qed.
Lemma lem3124997 (a : int) (c : int) (b : int) : (term151 a b c) = (term152 a c b).
Proof. exact (eq_refl (term151 a b c)). Qed.
Lemma lem3124998 (a : int) (c : int) (b : int) : term152 a c b.
Proof. exact (EQ_MP (@lem3124997 a c b) (@lem3124996 a b c)). Qed.
Lemma lem3124999 (a : int) (c : int) (b : int) (d : int) : term153 a c b d.
Proof. exact (@lem3124998 a c b d). Qed.
Lemma lem3125000 (a : int) (c : int) (b : int) (d : int) : (term153 a c b d) = (term154 a c b d).
Proof. exact (eq_refl (term153 a c b d)). Qed.
Lemma lem3125003 (a : int) (c : int) (b : int) (d : int) : term154 a c b d.
Proof. exact (EQ_MP (@lem3125000 a c b d) (@lem3124999 a c b d)). Qed.
Lemma lem3125004 (n : int) (x' : int) (a : int) : term155 n x' a.
Proof. exact (@lem3125003 (term118 n x' a) (term156 n x' a) (term119 n x' a) (term157 n x' a)). Qed.
Lemma lem3125005 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : term158 n x' a.
Proof. exact (@lem3125004 n x' a (@lem3124946 x' n a h1)). Qed.
Lemma lem3125012 : term159 = term10.
Proof. exact (@lem2416531 term110). Qed.
Lemma lem3125037 (n : int) (x' : int) (a : int) : (term160 n x' a) = term10.
Proof. exact (@lem2416533 (term36 n x' a)). Qed.
Lemma lem3125038 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3125039 (n : int) (x' : int) (a : int) : (term161 n x' a) = term162.
Proof. exact (MK_COMB (@lem3125038) (@lem3125037 n x' a)). Qed.
Lemma lem3125040 (n : int) (x' : int) (a : int) : (term157 n x' a) = term163.
Proof. exact (MK_COMB (@lem3125039 n x' a) (@lem3125012)). Qed.
Lemma lem3125041 : term163 = term10.
Proof. exact (@lem2416523 term10). Qed.
Lemma lem3125042 (n : int) (x' : int) (a : int) : (term157 n x' a) = term10.
Proof. exact (TRANS (@lem3125040 n x' a) (@lem3125041)). Qed.
Lemma lem3125045 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem3125046 (n : int) (x' : int) (a : int) : (term164 n x' a) = term115.
Proof. exact (MK_COMB (@lem3125045) (@lem3125042 n x' a)). Qed.
Lemma lem3125047 : term115 = term10.
Proof. exact (@lem2416533 term110). Qed.
Lemma lem3125048 (n : int) (x' : int) (a : int) : (term164 n x' a) = term10.
Proof. exact (TRANS (@lem3125046 n x' a) (@lem3125047)). Qed.
Lemma lem3125055 : term115 = term10.
Proof. exact (@lem2416533 term110). Qed.
Lemma lem3125080 (n : int) (x' : int) (a : int) : (term111 n x' a) = term10.
Proof. exact (@lem2416531 (term29 n x' a)). Qed.
Lemma lem3125081 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3125082 (n : int) (x' : int) (a : int) : (term117 n x' a) = term162.
Proof. exact (MK_COMB (@lem3125081) (@lem3125080 n x' a)). Qed.
Lemma lem3125083 (n : int) (x' : int) (a : int) : (term119 n x' a) = term163.
Proof. exact (MK_COMB (@lem3125082 n x' a) (@lem3125055)). Qed.
Lemma lem3125084 : term163 = term10.
Proof. exact (@lem2416523 term10). Qed.
Lemma lem3125085 (n : int) (x' : int) (a : int) : (term119 n x' a) = term10.
Proof. exact (TRANS (@lem3125083 n x' a) (@lem3125084)). Qed.
Lemma lem3125086 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3125087 (n : int) (x' : int) (a : int) : (term165 n x' a) = term162.
Proof. exact (MK_COMB (@lem3125086) (@lem3125085 n x' a)). Qed.
Lemma lem3125088 (n : int) (x' : int) (a : int) : (term166 n x' a) = term163.
Proof. exact (MK_COMB (@lem3125087 n x' a) (@lem3125048 n x' a)). Qed.
Lemma lem3125089 : term163 = term10.
Proof. exact (@lem2416523 term10). Qed.
Lemma lem3125090 (n : int) (x' : int) (a : int) : (term166 n x' a) = term10.
Proof. exact (TRANS (@lem3125088 n x' a) (@lem3125089)). Qed.
Lemma lem3125097 : term112 = term10.
Proof. exact (@lem2416531 term10). Qed.
Lemma lem3125122 (n : int) (x' : int) (a : int) : (term167 n x' a) = (term36 n x' a).
Proof. exact (@lem2416537 (term36 n x' a)). Qed.
Lemma lem3125123 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3125124 (n : int) (x' : int) (a : int) : (term168 n x' a) = (term62 n x' a).
Proof. exact (MK_COMB (@lem3125123) (@lem3125122 n x' a)). Qed.
Lemma lem3125125 (n : int) (x' : int) (a : int) : (term156 n x' a) = (term63 n x' a).
Proof. exact (MK_COMB (@lem3125124 n x' a) (@lem3125097)). Qed.
Lemma lem3125126 (n : int) (x' : int) (a : int) : (term63 n x' a) = (term36 n x' a).
Proof. exact (@lem2416525 (term36 n x' a)). Qed.
Lemma lem3125127 (n : int) (x' : int) (a : int) : (term156 n x' a) = (term36 n x' a).
Proof. exact (TRANS (@lem3125125 n x' a) (@lem3125126 n x' a)). Qed.
Lemma lem3125130 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem3125131 (n : int) (x' : int) (a : int) : (term169 n x' a) = (term170 n x' a).
Proof. exact (MK_COMB (@lem3125130) (@lem3125127 n x' a)). Qed.
Lemma lem3125132 (n : int) (x' : int) (a : int) : (term170 n x' a) = (term36 n x' a).
Proof. exact (@lem2416535 (term36 n x' a)). Qed.
Lemma lem3125133 (n : int) (x' : int) (a : int) : (term169 n x' a) = (term36 n x' a).
Proof. exact (TRANS (@lem3125131 n x' a) (@lem3125132 n x' a)). Qed.
Lemma lem3125158 (n : int) (x' : int) (a : int) : (term114 n x' a) = (term29 n x' a).
Proof. exact (@lem2416535 (term29 n x' a)). Qed.
Lemma lem3125165 : term112 = term10.
Proof. exact (@lem2416531 term10). Qed.
Lemma lem3125166 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3125167 : term116 = term162.
Proof. exact (MK_COMB (@lem3125166) (@lem3125165)). Qed.
Lemma lem3125168 (n : int) (x' : int) (a : int) : (term118 n x' a) = (term171 n x' a).
Proof. exact (MK_COMB (@lem3125167) (@lem3125158 n x' a)). Qed.
Lemma lem3125169 (n : int) (x' : int) (a : int) : (term171 n x' a) = (term29 n x' a).
Proof. exact (@lem2416523 (term29 n x' a)). Qed.
Lemma lem3125170 (n : int) (x' : int) (a : int) : (term118 n x' a) = (term29 n x' a).
Proof. exact (TRANS (@lem3125168 n x' a) (@lem3125169 n x' a)). Qed.
Lemma lem3125171 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3125172 (n : int) (x' : int) (a : int) : (term172 n x' a) = (term173 n x' a).
Proof. exact (MK_COMB (@lem3125171) (@lem3125170 n x' a)). Qed.
Lemma lem3125173 (n : int) (x' : int) (a : int) : (term174 n x' a) = (term175 n x' a).
Proof. exact (MK_COMB (@lem3125172 n x' a) (@lem3125133 n x' a)). Qed.
Lemma lem3125174 (n : int) (x' : int) (a : int) : (term175 n x' a) = (term176 n x' a).
Proof. exact (@lem2416555 (int_mul n x') (term37 n x') (term16 a) a). Qed.
Lemma lem3125175 (n : int) (x' : int) : (term177 n x') = (term178 n x').
Proof. exact (@lem2416517 term19 (int_mul n x')). Qed.
Lemma lem3125177 (m : nat) : (term20 m) = term10.
Proof. exact (proj1 (@lem2405813 m)). Qed.
Lemma lem3125178 : term21 = term10.
Proof. exact (@lem3125177 term22). Qed.
Lemma lem3125179 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3125180 : term23 = term24.
Proof. exact (MK_COMB (@lem3125179) (@lem3125178)). Qed.
Lemma lem3125181 (n : int) (x' : int) : (int_mul n x') = (int_mul n x').
Proof. exact (eq_refl (int_mul n x')). Qed.
Lemma lem3125182 (n : int) (x' : int) : (term178 n x') = (term179 n x').
Proof. exact (MK_COMB (@lem3125180) (@lem3125181 n x')). Qed.
Lemma lem3125183 (n : int) (x' : int) : (term177 n x') = (term179 n x').
Proof. exact (TRANS (@lem3125175 n x') (@lem3125182 n x')). Qed.
Lemma lem3125184 (n : int) (x' : int) : (term179 n x') = term10.
Proof. exact (@lem2416521 (int_mul n x')). Qed.
Lemma lem3125185 (n : int) (x' : int) : (term177 n x') = term10.
Proof. exact (TRANS (@lem3125183 n x') (@lem3125184 n x')). Qed.
Lemma lem3125186 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3125187 (n : int) (x' : int) : (term180 n x') = term162.
Proof. exact (MK_COMB (@lem3125186) (@lem3125185 n x')). Qed.
Lemma lem3125188 (a : int) : (term181 a) = (term18 a).
Proof. exact (@lem2416515 term19 a). Qed.
Lemma lem3125190 (m : nat) : (term20 m) = term10.
Proof. exact (proj1 (@lem2405813 m)). Qed.
Lemma lem3125191 : term21 = term10.
Proof. exact (@lem3125190 term22). Qed.
Lemma lem3125192 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3125193 : term23 = term24.
Proof. exact (MK_COMB (@lem3125192) (@lem3125191)). Qed.
Lemma lem3125194 (a : int) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3125195 (a : int) : (term18 a) = (term25 a).
Proof. exact (MK_COMB (@lem3125193) (@lem3125194 a)). Qed.
Lemma lem3125196 (a : int) : (term181 a) = (term25 a).
Proof. exact (TRANS (@lem3125188 a) (@lem3125195 a)). Qed.
Lemma lem3125197 (a : int) : (term25 a) = term10.
Proof. exact (@lem2416521 a). Qed.
Lemma lem3125198 (a : int) : (term181 a) = term10.
Proof. exact (TRANS (@lem3125196 a) (@lem3125197 a)). Qed.
Lemma lem3125199 (n : int) (x' : int) (a : int) : (term176 n x' a) = term163.
Proof. exact (MK_COMB (@lem3125187 n x') (@lem3125198 a)). Qed.
Lemma lem3125200 (n : int) (x' : int) (a : int) : (term175 n x' a) = term163.
Proof. exact (TRANS (@lem3125174 n x' a) (@lem3125199 n x' a)). Qed.
Lemma lem3125201 : term163 = term10.
Proof. exact (@lem2416523 term10). Qed.
Lemma lem3125202 (n : int) (x' : int) (a : int) : (term175 n x' a) = term10.
Proof. exact (TRANS (@lem3125200 n x' a) (@lem3125201)). Qed.
Lemma lem3125203 (n : int) (x' : int) (a : int) : (term174 n x' a) = term10.
Proof. exact (TRANS (@lem3125173 n x' a) (@lem3125202 n x' a)). Qed.
Lemma lem3125204 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3125205 (n : int) (x' : int) (a : int) : (term182 n x' a) = term183.
Proof. exact (MK_COMB (@lem3125204) (@lem3125203 n x' a)). Qed.
Lemma lem3125206 (n : int) (x' : int) (a : int) : ((term174 n x' a) = (term166 n x' a)) = (term10 = term10).
Proof. exact (MK_COMB (@lem3125205 n x' a) (@lem3125090 n x' a)). Qed.
Lemma lem3125207 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3125208 (n : int) (x' : int) (a : int) : (term158 n x' a) = term184.
Proof. exact (MK_COMB (@lem3125207) (@lem3125206 n x' a)). Qed.
Lemma lem3125209 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : term184.
Proof. exact (EQ_MP (@lem3125208 n x' a) (@lem3125005 x' n a h1)). Qed.
Lemma lem3125210 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3125211 : term185.
Proof. exact (@lem82 (term10 = term10)). Qed.
Lemma lem3125212 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : (term10 = term10) = False.
Proof. exact (@lem3125211 (@lem3125209 x' n a h1)). Qed.
Lemma lem3125213 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : False.
Proof. exact (EQ_MP (@lem3125212 x' n a h1) (@lem3125210)). Qed.
Lemma lem3125214 (x' : int) (n : int) (a : int) : term225 x' n a.
Proof. exact (fun h0 : term204 x' n a => @lem3125213 x' n a h0). Qed.
Lemma lem3125215 (x' : int) (n : int) (a : int) : (term225 x' n a) = (term226 x' n a).
Proof. exact (@lem69 (term204 x' n a)). Qed.
Lemma lem3125216 (x' : int) (n : int) (a : int) : term226 x' n a.
Proof. exact (EQ_MP (@lem3125215 x' n a) (@lem3125214 x' n a)). Qed.
Lemma lem3125217 (x' : int) (n : int) (a : int) : term227 x' n a.
Proof. exact (@lem82 (term204 x' n a)). Qed.
Lemma lem3125219 (x' : int) (n : int) (a : int) : (term204 x' n a) = False.
Proof. exact (@lem3125217 x' n a (@lem3125216 x' n a)). Qed.
Lemma lem3125220 (x' : int) (n : int) (a : int) : term228 x' n a.
Proof. exact (@lem93 (term204 x' n a)). Qed.
Lemma lem3125221 (x' : int) (n : int) (a : int) : term226 x' n a.
Proof. exact (@lem3125220 x' n a (@lem3125219 x' n a)). Qed.
Lemma lem3125222 (x' : int) (n : int) (a : int) : (term226 x' n a) = (term225 x' n a).
Proof. exact (@lem62 (term204 x' n a)). Qed.
Lemma lem3125223 (x' : int) (n : int) (a : int) : term225 x' n a.
Proof. exact (EQ_MP (@lem3125222 x' n a) (@lem3125221 x' n a)). Qed.
Lemma lem3125224 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : term204 x' n a.
Proof. exact (h1). Qed.
Lemma lem3125225 (x' : int) (n : int) (a : int) (h1 : term204 x' n a) : False.
Proof. exact (@lem3125223 x' n a (@lem3125224 x' n a h1)). Qed.
Lemma lem3125226 (x' : int) (n : int) (h1 : term211 x' n) : term211 x' n.
Proof. exact (h1). Qed.
Lemma lem3125227 (x' : int) (n : int) (h1 : term211 x' n) : False.
Proof. exact (ex_elim (@lem3125226 x' n h1) (fun a : int => fun h0 : term210 x' n a => @lem3125225 x' n a h0)). Qed.
Lemma lem3125228 (x' : int) (h1 : term218 x') : term218 x'.
Proof. exact (h1). Qed.
Lemma lem3125229 (x' : int) (h1 : term218 x') : False.
Proof. exact (ex_elim (@lem3125228 x' h1) (fun n : int => fun h0 : term217 x' n => @lem3125227 x' n h0)). Qed.
Lemma lem3125230 (h1 : term224) : term224.
Proof. exact (h1). Qed.
Lemma lem3125231 (h1 : term224) : False.
Proof. exact (ex_elim (@lem3125230 h1) (fun x' : int => fun h0 : term223 x' => @lem3125229 x' h0)). Qed.
Lemma lem3125232 : term229.
Proof. exact (fun h0 : term224 => @lem3125231 h0). Qed.
Lemma lem3125234 (p : Prop) (q : Prop) : term191 p q.
Proof. exact (EQ_MP (@lem1032627 p q) (@lem1032730 p q)). Qed.
Lemma lem3125235 (q : Prop) : term230 q.
Proof. exact (@lem3125234 term224 q). Qed.
Lemma lem3125238 (q : Prop) : term231 q.
Proof. exact (@lem3125235 q (@lem3125232)). Qed.
Lemma lem3125239 : term232.
Proof. exact (@lem3125238 term201). Qed.
Lemma lem3125240 : term201.
Proof. exact (@lem3125239 (@lem3124890)). Qed.
Lemma lem3125241 (x' : int) : term220 x'.
Proof. exact (@lem3125240 x'). Qed.
Lemma lem3125242 (x' : int) : (term220 x') = (term199 x').
Proof. exact (eq_refl (term220 x')). Qed.
Lemma lem3125243 (x' : int) : term199 x'.
Proof. exact (EQ_MP (@lem3125242 x') (@lem3125241 x')). Qed.
Lemma lem3125244 (x' : int) (n : int) : term214 x' n.
Proof. exact (@lem3125243 x' n). Qed.
Lemma lem3125245 (x' : int) (n : int) : (term214 x' n) = (term197 x' n).
Proof. exact (eq_refl (term214 x' n)). Qed.
Lemma lem3125246 (x' : int) (n : int) : term197 x' n.
Proof. exact (EQ_MP (@lem3125245 x' n) (@lem3125244 x' n)). Qed.
Lemma lem3125247 (x' : int) (n : int) (a : int) : term207 x' n a.
Proof. exact (@lem3125246 x' n a). Qed.
Lemma lem3125248 (x' : int) (n : int) (a : int) : (term207 x' n a) = (term195 x' n a).
Proof. exact (eq_refl (term207 x' n a)). Qed.
Lemma lem3125249 (x' : int) (n : int) (a : int) : term195 x' n a.
Proof. exact (EQ_MP (@lem3125248 x' n a) (@lem3125247 x' n a)). Qed.
Lemma lem3125250 (n : int) (x' : int) (a : int) (h1 : (term29 n x' a) = term10) : (term75 x' n a) = term10.
Proof. exact (@lem3125249 x' n a (@lem3124269 n x' a h1)). Qed.
Lemma lem3125251 (n : int) (x' : int) (a : int) (h1 : (term29 n x' a) = term10) : term52 n a.
Proof. exact (ex_intro (term51 n a) (term99 x') (@lem3125250 n x' a h1)). Qed.
Lemma lem3125252 (n : int) (x' : int) (a : int) (h1 : (term29 n x' a) = term10) : term52 n a.
Proof. exact (EQ_MP (@lem3124377 n a) (@lem3125251 n x' a h1)). Qed.
Lemma lem3125253 (d : int) (n : int) (a : int) (h1 : (term29 d n a) = term10) : term42 n a.
Proof. exact (EQ_MP (@lem3124332 n a) (@lem3124814 d n a h1)). Qed.
Lemma lem3125254 (n : int) (x' : int) (a : int) (h1 : (term29 n x' a) = term10) : term52 n a.
Proof. exact (EQ_MP (@lem3124287 n a) (@lem3125252 n x' a h1)). Qed.
Lemma lem3125255 (d : int) (n : int) (a : int) (h1 : (term29 d n a) = term10) : term42 n a.
Proof. exact (EQ_MP (@lem3124278 n a) (@lem3125253 d n a h1)). Qed.
Lemma lem3125258 (x' : int) (n : int) (a : int) : term54 x' n a.
Proof. exact (fun h0 : (term29 n x' a) = term10 => @lem3125254 n x' a h0). Qed.
Lemma lem3125259 (d : int) (n : int) (a : int) : term44 d n a.
Proof. exact (fun h0 : (term29 d n a) = term10 => @lem3125255 d n a h0). Qed.
Lemma lem3125260 (x' : int) (a : int) (x : int) (n : int) : term53 x' a x n.
Proof. exact (EQ_MP (@lem3124239 x' a x n) (@lem3125258 x' n a)). Qed.
Lemma lem3125261 (d : int) (x : int) (a : int) (n : int) : term43 d x a n.
Proof. exact (EQ_MP (@lem3124144 d x a n) (@lem3125259 d n a)). Qed.
Lemma lem3125268 (x : int) (a : int) (n : int) (x' : int) (h1 : a = (int_mul n x')) : term5 a x n.
Proof. exact (@lem3125260 x' a x n (@lem3124049 a n x' h1)). Qed.
Lemma lem3125269 (a : int) (x : int) (n : int) (d : int) (h1 : (term9 a x) = (int_mul n d)) : term8 a n.
Proof. exact (@lem3125261 d x a n (@lem3124048 a x n d h1)). Qed.
Lemma lem3125270 (x : int) (a : int) (n : int) (x' : int) (h1 : a = (int_mul n x')) : (a = (int_mul n x')) = (term5 a x n).
Proof. exact (prop_ext (fun h2 : a = (int_mul n x') => @lem3125268 x a n x' h1) (fun h2 : term5 a x n => @lem3123819 a n x' h1)). Qed.
Lemma lem3125271 (x : int) (a : int) (n : int) (x' : int) (h1 : a = (int_mul n x')) : term5 a x n.
Proof. exact (EQ_MP (@lem3125270 x a n x' h1) (@lem3123819 a n x' h1)). Qed.
Lemma lem3125272 (x : int) (a : int) (n : int) (h1 : term8 a n) : term5 a x n.
Proof. exact (ex_elim (@lem3123818 a n h1) (fun x' : int => fun h0 : term40 a n x' => @lem3125271 x a n x' h0)). Qed.
Lemma lem3125273 (a : int) (x : int) (n : int) : term233 a x n.
Proof. exact (fun h0 : term8 a n => @lem3125272 x a n h0). Qed.
Lemma lem3125274 (a : int) (x : int) (n : int) (d : int) (h1 : (term9 a x) = (int_mul n d)) : ((term9 a x) = (int_mul n d)) = (term8 a n).
Proof. exact (prop_ext (fun h2 : (term9 a x) = (int_mul n d) => @lem3125269 a x n d h1) (fun h2 : term8 a n => @lem3123817 a x n d h1)). Qed.
Lemma lem3125275 (a : int) (x : int) (n : int) (d : int) (h1 : (term9 a x) = (int_mul n d)) : term8 a n.
Proof. exact (EQ_MP (@lem3125274 a x n d h1) (@lem3123817 a x n d h1)). Qed.
Lemma lem3125276 (a : int) (x : int) (n : int) (h1 : term5 a x n) : term8 a n.
Proof. exact (ex_elim (@lem3123816 a x n h1) (fun d : int => fun h0 : term50 a x n d => @lem3125275 a x n d h0)). Qed.
Lemma lem3125277 (x : int) (a : int) (n : int) : term234 x a n.
Proof. exact (fun h0 : term5 a x n => @lem3125276 a x n h0). Qed.
Lemma lem3125278 (a : int) (x : int) (n : int) : term235 a x n.
Proof. exact (conj (@lem3125277 x a n) (@lem3125273 a x n)). Qed.
Lemma lem3125279 (x : int) (a : int) (n : int) : (term235 a x n) = ((term5 a x n) = (term8 a n)).
Proof. exact (@lem32 (term5 a x n) (term8 a n)). Qed.
Lemma lem3125280 (x : int) (a : int) (n : int) : (term5 a x n) = (term8 a n).
Proof. exact (EQ_MP (@lem3125279 x a n) (@lem3125278 a x n)). Qed.
Lemma lem3125283 (h1 : term236) : term236.
Proof. exact (h1). Qed.
Lemma lem3125284 (x : int) (h1 : term236) : term237 x.
Proof. exact (@lem3125283 h1 x). Qed.
Lemma lem3125285 (x : int) : (term237 x) = (term238 x).
Proof. exact (eq_refl (term237 x)). Qed.
Lemma lem3125286 (x : int) (h1 : term236) : term238 x.
Proof. exact (EQ_MP (@lem3125285 x) (@lem3125284 x h1)). Qed.
Lemma lem3125287 (x : int) (y : int) (h1 : term236) : term239 x y.
Proof. exact (@lem3125286 x h1 y). Qed.
Lemma lem3125288 (y : int) (x : int) : (term239 x y) = (term240 y x).
Proof. exact (eq_refl (term239 x y)). Qed.
Lemma lem3125289 (y : int) (x : int) (h1 : term236) : term240 y x.
Proof. exact (EQ_MP (@lem3125288 y x) (@lem3125287 x y h1)). Qed.
Lemma lem3125290 (y : int) (x : int) (z : int) (h1 : term236) : term241 y x z.
Proof. exact (@lem3125289 y x h1 z). Qed.
Lemma lem3125291 (y : int) (x : int) (z : int) : (term241 y x z) = (term242 y x z).
Proof. exact (eq_refl (term241 y x z)). Qed.
Lemma lem3125292 (y : int) (x : int) (z : int) (h1 : term236) : term242 y x z.
Proof. exact (EQ_MP (@lem3125291 y x z) (@lem3125290 y x z h1)). Qed.
Lemma lem3125293 (x : int) (y : int) (z : int) (h1 : term243 x y z) : term243 x y z.
Proof. exact (h1). Qed.
Lemma lem3125294 (x : int) (y : int) (z : int) (h1 : term236) (h2 : term243 x y z) : term244 y x z.
Proof. exact (@lem3125292 y x z h1 (@lem3125293 x y z h2)). Qed.
Lemma lem3125295 (x : int) (y : int) (z : int) (h1 : term243 x y z) : term245 y x z.
Proof. exact (fun h0 : term236 => @lem3125294 x y z h0 h1). Qed.
Lemma lem3125296 (h1 : term236) : term236.
Proof. exact (h1). Qed.
Lemma lem3125297 (x : int) (y : int) (z : int) (h1 : term236) (h2 : term243 x y z) : term244 y x z.
Proof. exact (@lem3125295 x y z h2 (@lem3125296 h1)). Qed.
Lemma lem3125298 (y : int) (x : int) (z : int) (h1 : term236) : term242 y x z.
Proof. exact (fun h0 : term243 x y z => @lem3125297 x y z h1 h0). Qed.
Lemma lem3125299 (y : int) (x : int) (h1 : term236) : term240 y x.
Proof. exact (fun z : int => @lem3125298 y x z h1). Qed.
Lemma lem3125300 (y : int) (h1 : term236) : term246 y.
Proof. exact (fun x : int => @lem3125299 y x h1). Qed.
Lemma lem3125301 (h1 : term236) : term247.
Proof. exact (fun y : int => @lem3125300 y h1). Qed.
Lemma lem3125302 : term248.
Proof. exact (fun h0 : term236 => @lem3125301 h0). Qed.
Lemma lem3125303 : term247.
Proof. exact (@lem3125302 (@lem2302531)). Qed.
Lemma lem3125304 (y : int) : term249 y.
Proof. exact (@lem3125303 y). Qed.
Lemma lem3125305 (y : int) : (term249 y) = (term246 y).
Proof. exact (eq_refl (term249 y)). Qed.
Lemma lem3125306 (y : int) : term246 y.
Proof. exact (EQ_MP (@lem3125305 y) (@lem3125304 y)). Qed.
Lemma lem3125307 (y : int) (x : int) : term250 y x.
Proof. exact (@lem3125306 y x). Qed.
Lemma lem3125308 (y : int) (x : int) : (term250 y x) = (term240 y x).
Proof. exact (eq_refl (term250 y x)). Qed.
Lemma lem3125309 (y : int) (x : int) : term240 y x.
Proof. exact (EQ_MP (@lem3125308 y x) (@lem3125307 y x)). Qed.
Lemma lem3125310 (y : int) (x : int) (z : int) : term241 y x z.
Proof. exact (@lem3125309 y x z). Qed.
Lemma lem3125311 (y : int) (x : int) (z : int) : (term241 y x z) = (term242 y x z).
Proof. exact (eq_refl (term241 y x z)). Qed.
Lemma lem3125313 (x : int) : term251 x.
Proof. exact (@lem2300430 x). Qed.
Lemma lem3125314 (x : int) : (term251 x) = (term252 x).
Proof. exact (eq_refl (term251 x)). Qed.
Lemma lem3125315 (x : int) : term252 x.
Proof. exact (EQ_MP (@lem3125314 x) (@lem3125313 x)). Qed.
Lemma lem3125316 (x : int) (y : int) : term253 x y.
Proof. exact (@lem3125315 x y). Qed.
Lemma lem3125317 (x : int) (y : int) : (term253 x y) = ((term254 x y) = (term255 x y)).
Proof. exact (eq_refl (term253 x y)). Qed.
Lemma lem3125319 (x : int) (y : int) : (term256 x y) = (term257 x y).
Proof. exact (@lem2954598 (term257 x y)). Qed.
Lemma lem3125348 (x : int) (y : int) : (term258 x y) = (term259 x y).
Proof. exact (@lem17362 (term260 x y) (term261 x y)). Qed.
Lemma lem3125351 (x : int) (y : int) : (int_le x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3125352 (x : int) (y : int) : (term260 x y) = (term263 x y).
Proof. exact (@lem3125351 (term264 x) y). Qed.
Lemma lem3125354 (x : int) (y : int) : (term265 x y) = (term266 x y).
Proof. exact (EQ_MP (@lem2841580 x y) (@lem2841579 x y)). Qed.
Lemma lem3125355 (x : int) : (term267 x) = (term268 x).
Proof. exact (@lem3125354 (int_abs x) term110). Qed.
Lemma lem3125357 (x : int) : (term269 x) = (term270 x).
Proof. exact (EQ_MP (@lem2841562 x) (@lem2841561 x)). Qed.
Lemma lem3125358 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3125359 (x : int) : (term271 x) = (term272 x).
Proof. exact (MK_COMB (@lem3125358) (@lem3125357 x)). Qed.
Lemma lem3125361 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3125362 : term274 = term275.
Proof. exact (@lem3125361 term22). Qed.
Lemma lem3125363 (x : int) : (term268 x) = (term276 x).
Proof. exact (MK_COMB (@lem3125359 x) (@lem3125362)). Qed.
Lemma lem3125364 (x : int) : (term267 x) = (term276 x).
Proof. exact (TRANS (@lem3125355 x) (@lem3125363 x)). Qed.
Lemma lem3125365 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3125366 (x : int) : (term277 x) = (term278 x).
Proof. exact (MK_COMB (@lem3125365) (@lem3125364 x)). Qed.
Lemma lem3125367 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3125368 (x : int) (y : int) : (term263 x y) = (term279 x y).
Proof. exact (MK_COMB (@lem3125366 x) (@lem3125367 y)). Qed.
Lemma lem3125370 (x : int) (y : int) : (term260 x y) = (term279 x y).
Proof. exact (TRANS (@lem3125352 x y) (@lem3125368 x y)). Qed.
Lemma lem3125372 (y : int) (x : int) : (term280 x y) = (term281 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem3125373 (x : int) (y : int) : (term282 x y) = (term283 x y).
Proof. exact (@lem3125372 (int_add x y) term10). Qed.
Lemma lem3125375 (x : int) (y : int) : (int_le x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3125376 (x : int) (y : int) : (term283 x y) = (term284 x y).
Proof. exact (@lem3125375 (term285 x y) term10). Qed.
Lemma lem3125378 (x : int) (y : int) : (term286 x y) = (term287 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3125379 (x : int) (y : int) : (term288 x y) = (term289 x y).
Proof. exact (@lem3125378 (int_add x y) term110). Qed.
Lemma lem3125381 (x : int) (y : int) : (term286 x y) = (term287 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3125382 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3125383 (x : int) (y : int) : (term290 x y) = (term291 x y).
Proof. exact (MK_COMB (@lem3125382) (@lem3125381 x y)). Qed.
Lemma lem3125385 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3125386 : term274 = term275.
Proof. exact (@lem3125385 term22). Qed.
Lemma lem3125387 (x : int) (y : int) : (term289 x y) = (term292 x y).
Proof. exact (MK_COMB (@lem3125383 x y) (@lem3125386)). Qed.
Lemma lem3125388 (x : int) (y : int) : (term288 x y) = (term292 x y).
Proof. exact (TRANS (@lem3125379 x y) (@lem3125387 x y)). Qed.
Lemma lem3125389 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3125390 (x : int) (y : int) : (term293 x y) = (term294 x y).
Proof. exact (MK_COMB (@lem3125389) (@lem3125388 x y)). Qed.
Lemma lem3125392 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3125393 : term295 = term296.
Proof. exact (@lem3125392 (NUMERAL 0)). Qed.
Lemma lem3125394 (x : int) (y : int) : (term284 x y) = (term297 x y).
Proof. exact (MK_COMB (@lem3125390 x y) (@lem3125393)). Qed.
Lemma lem3125395 (x : int) (y : int) : (term283 x y) = (term297 x y).
Proof. exact (TRANS (@lem3125376 x y) (@lem3125394 x y)). Qed.
Lemma lem3125396 (x : int) (y : int) : (term282 x y) = (term297 x y).
Proof. exact (TRANS (@lem3125373 x y) (@lem3125395 x y)). Qed.
Lemma lem3125397 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3125398 (x : int) (y : int) : (term298 x y) = (term299 x y).
Proof. exact (MK_COMB (@lem3125397) (@lem3125370 x y)). Qed.
Lemma lem3125399 (x : int) (y : int) : (term259 x y) = (term300 x y).
Proof. exact (MK_COMB (@lem3125398 x y) (@lem3125396 x y)). Qed.
Lemma lem3125400 (x : int) (y : int) : (term258 x y) = (term300 x y).
Proof. exact (TRANS (@lem3125348 x y) (@lem3125399 x y)). Qed.
Lemma lem3125404 (t : Prop) : (term301 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3125420 (x : int) (y : int) : (term302 x y) = (term300 x y).
Proof. exact (@lem3125404 (term300 x y)). Qed.
Lemma lem3125421 (y : int) (x : int) : (term279 x y) = (term303 y x).
Proof. exact (@lem1988287 (real_of_int y) (term276 x)). Qed.
Lemma lem3125430 (x : int) : (term276 x) = (term270 x).
Proof. exact (@lem1982735 (term270 x)). Qed.
Lemma lem3125433 (y : int) : (term304 y) = (term304 y).
Proof. exact (eq_refl (term304 y)). Qed.
Lemma lem3125434 (y : int) (x : int) : (term305 y x) = (term306 y x).
Proof. exact (MK_COMB (@lem3125433 y) (@lem3125430 x)). Qed.
Lemma lem3125435 (y : int) (x : int) : (term306 y x) = (term307 y x).
Proof. exact (@lem1982792 (real_of_int y) (term270 x)). Qed.
Lemma lem3125440 (x : int) (y : int) : (term307 y x) = (term308 x y).
Proof. exact (@lem1982761 (term309 x) (real_of_int y)). Qed.
Lemma lem3125441 (x : int) (y : int) : (term306 y x) = (term308 x y).
Proof. exact (TRANS (@lem3125435 y x) (@lem3125440 x y)). Qed.
Lemma lem3125442 (x : int) (y : int) : (term305 y x) = (term308 x y).
Proof. exact (TRANS (@lem3125434 y x) (@lem3125441 x y)). Qed.
Lemma lem3125443 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3125444 (x : int) (y : int) : (term310 y x) = (term311 x y).
Proof. exact (MK_COMB (@lem3125443) (@lem3125442 x y)). Qed.
Lemma lem3125445 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3125446 (x : int) (y : int) : (term303 y x) = (term312 x y).
Proof. exact (MK_COMB (@lem3125444 x y) (@lem3125445)). Qed.
Lemma lem3125447 (x : int) (y : int) : (term279 x y) = (term312 x y).
Proof. exact (TRANS (@lem3125421 y x) (@lem3125446 x y)). Qed.
Lemma lem3125448 (x : int) (y : int) : (term297 x y) = (term313 x y).
Proof. exact (@lem1988287 term296 (term292 x y)). Qed.
Lemma lem3125465 (x : int) (y : int) : (term292 x y) = (term314 x y).
Proof. exact (@lem1982755 (real_of_int x) (real_of_int y) term275). Qed.
Lemma lem3125468 : term315 = term315.
Proof. exact (eq_refl term315). Qed.
Lemma lem3125469 (x : int) (y : int) : (term316 x y) = (term317 x y).
Proof. exact (MK_COMB (@lem3125468) (@lem3125465 x y)). Qed.
Lemma lem3125470 (x : int) (y : int) : (term317 x y) = (term318 x y).
Proof. exact (@lem1982792 term296 (term314 x y)). Qed.
Lemma lem3125471 (x : int) (y : int) : (term319 x y) = (term320 x y).
Proof. exact (@lem1982781 (real_of_int x) term321 (term322 y)). Qed.
Lemma lem3125472 (y : int) : (term323 y) = (term324 y).
Proof. exact (@lem1982781 (real_of_int y) term321 term275). Qed.
Lemma lem3125474 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3125475 : term275 = term326.
Proof. exact (@lem3125474 term22). Qed.
Lemma lem3125477 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3125478 : term321 = term329.
Proof. exact (@lem3125477 term22). Qed.
Lemma lem3125479 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3125480 : term330 = term331.
Proof. exact (MK_COMB (@lem3125479) (@lem3125478)). Qed.
Lemma lem3125481 : term332 = term333.
Proof. exact (MK_COMB (@lem3125480) (@lem3125475)). Qed.
Lemma lem3125482 : term333 = term334.
Proof. exact (@lem1981613 term321 term275 term275 term275). Qed.
Lemma lem3125484 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3125485 : term337 = term338.
Proof. exact (@lem3125484 term22 term22). Qed.
Lemma lem3125486 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3125487 : term340 = term22.
Proof. exact (EQ_MP (@lem3125486) (@lem940073)). Qed.
Lemma lem3125488 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3125489 : term338 = term275.
Proof. exact (MK_COMB (@lem3125488) (@lem3125487)). Qed.
Lemma lem3125490 : term337 = term275.
Proof. exact (TRANS (@lem3125485) (@lem3125489)). Qed.
Lemma lem3125492 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3125493 : term332 = term343.
Proof. exact (@lem3125492 term22 term22). Qed.
Lemma lem3125494 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3125495 : term340 = term22.
Proof. exact (EQ_MP (@lem3125494) (@lem940073)). Qed.
Lemma lem3125496 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3125497 : term338 = term275.
Proof. exact (MK_COMB (@lem3125496) (@lem3125495)). Qed.
Lemma lem3125498 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3125499 : term343 = term321.
Proof. exact (MK_COMB (@lem3125498) (@lem3125497)). Qed.
Lemma lem3125500 : term332 = term321.
Proof. exact (TRANS (@lem3125493) (@lem3125499)). Qed.
Lemma lem3125501 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3125502 : term344 = term345.
Proof. exact (MK_COMB (@lem3125501) (@lem3125500)). Qed.
Lemma lem3125503 : term334 = term329.
Proof. exact (MK_COMB (@lem3125502) (@lem3125490)). Qed.
Lemma lem3125504 : term333 = term329.
Proof. exact (TRANS (@lem3125482) (@lem3125503)). Qed.
Lemma lem3125505 : term332 = term329.
Proof. exact (TRANS (@lem3125481) (@lem3125504)). Qed.
Lemma lem3125507 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3125508 : term329 = term321.
Proof. exact (@lem3125507 term321). Qed.
Lemma lem3125509 : term332 = term321.
Proof. exact (TRANS (@lem3125505) (@lem3125508)). Qed.
Lemma lem3125512 (y : int) : (term347 y) = (term347 y).
Proof. exact (eq_refl (term347 y)). Qed.
Lemma lem3125513 (y : int) : (term324 y) = (term348 y).
Proof. exact (MK_COMB (@lem3125512 y) (@lem3125509)). Qed.
Lemma lem3125514 (y : int) : (term323 y) = (term348 y).
Proof. exact (TRANS (@lem3125472 y) (@lem3125513 y)). Qed.
Lemma lem3125517 (x : int) : (term347 x) = (term347 x).
Proof. exact (eq_refl (term347 x)). Qed.
Lemma lem3125518 (x : int) (y : int) : (term320 x y) = (term349 x y).
Proof. exact (MK_COMB (@lem3125517 x) (@lem3125514 y)). Qed.
Lemma lem3125519 (x : int) (y : int) : (term319 x y) = (term349 x y).
Proof. exact (TRANS (@lem3125471 x y) (@lem3125518 x y)). Qed.
Lemma lem3125520 : term350 = term350.
Proof. exact (eq_refl term350). Qed.
Lemma lem3125521 (x : int) (y : int) : (term318 x y) = (term351 x y).
Proof. exact (MK_COMB (@lem3125520) (@lem3125519 x y)). Qed.
Lemma lem3125522 (x : int) (y : int) : (term351 x y) = (term349 x y).
Proof. exact (@lem1982721 (term349 x y)). Qed.
Lemma lem3125523 (x : int) (y : int) : (term318 x y) = (term349 x y).
Proof. exact (TRANS (@lem3125521 x y) (@lem3125522 x y)). Qed.
Lemma lem3125524 (x : int) (y : int) : (term317 x y) = (term349 x y).
Proof. exact (TRANS (@lem3125470 x y) (@lem3125523 x y)). Qed.
Lemma lem3125525 (x : int) (y : int) : (term316 x y) = (term349 x y).
Proof. exact (TRANS (@lem3125469 x y) (@lem3125524 x y)). Qed.
Lemma lem3125526 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3125527 (x : int) (y : int) : (term352 x y) = (term353 x y).
Proof. exact (MK_COMB (@lem3125526) (@lem3125525 x y)). Qed.
Lemma lem3125528 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3125529 (x : int) (y : int) : (term313 x y) = (term354 x y).
Proof. exact (MK_COMB (@lem3125527 x y) (@lem3125528)). Qed.
Lemma lem3125530 (x : int) (y : int) : (term297 x y) = (term354 x y).
Proof. exact (TRANS (@lem3125448 x y) (@lem3125529 x y)). Qed.
Lemma lem3125531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3125532 (x : int) (y : int) : (term299 x y) = (term355 x y).
Proof. exact (MK_COMB (@lem3125531) (@lem3125447 x y)). Qed.
Lemma lem3125533 (x : int) (y : int) : (term300 x y) = (term356 x y).
Proof. exact (MK_COMB (@lem3125532 x y) (@lem3125530 x y)). Qed.
Lemma lem3125548 (x : int) (y : int) : (term302 x y) = (term356 x y).
Proof. exact (TRANS (@lem3125420 x y) (@lem3125533 x y)). Qed.
Lemma lem3125550 (a : real) (x : real) (r : real) : (term357 x a r) = (term358 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem3125551 (y : int) (x : int) : (term312 x y) = (term359 y x).
Proof. exact (@lem3125550 (real_of_int y) (real_of_int x) term296). Qed.
Lemma lem3125558 (x : int) : (term360 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem3125561 (y : int) : (term361 y) = (term361 y).
Proof. exact (eq_refl (term361 y)). Qed.
Lemma lem3125562 (y : int) (x : int) : (term362 y x) = (term287 y x).
Proof. exact (MK_COMB (@lem3125561 y) (@lem3125558 x)). Qed.
Lemma lem3125563 (x : int) (y : int) : (term287 y x) = (term287 x y).
Proof. exact (@lem1982761 (real_of_int x) (real_of_int y)). Qed.
Lemma lem3125564 (x : int) (y : int) : (term362 y x) = (term287 x y).
Proof. exact (TRANS (@lem3125562 y x) (@lem3125563 x y)). Qed.
Lemma lem3125565 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3125566 (x : int) (y : int) : (term363 y x) = (term364 x y).
Proof. exact (MK_COMB (@lem3125565) (@lem3125564 x y)). Qed.
Lemma lem3125567 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3125568 (x : int) (y : int) : (term365 y x) = (term366 x y).
Proof. exact (MK_COMB (@lem3125566 x y) (@lem3125567)). Qed.
Lemma lem3125581 (x : int) (y : int) : (term367 y x) = (term368 x y).
Proof. exact (@lem1982761 (term369 x) (real_of_int y)). Qed.
Lemma lem3125582 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3125583 (x : int) (y : int) : (term370 y x) = (term371 x y).
Proof. exact (MK_COMB (@lem3125582) (@lem3125581 x y)). Qed.
Lemma lem3125584 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3125585 (x : int) (y : int) : (term372 y x) = (term373 x y).
Proof. exact (MK_COMB (@lem3125583 x y) (@lem3125584)). Qed.
Lemma lem3125586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3125587 (x : int) (y : int) : (term374 y x) = (term375 x y).
Proof. exact (MK_COMB (@lem3125586) (@lem3125585 x y)). Qed.
Lemma lem3125588 (x : int) (y : int) : (term359 y x) = (term376 x y).
Proof. exact (MK_COMB (@lem3125587 x y) (@lem3125568 x y)). Qed.
Lemma lem3125589 (x : int) (y : int) : (term312 x y) = (term376 x y).
Proof. exact (TRANS (@lem3125551 y x) (@lem3125588 x y)). Qed.
Lemma lem3125590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3125591 (x : int) (y : int) : (term355 x y) = (term377 x y).
Proof. exact (MK_COMB (@lem3125590) (@lem3125589 x y)). Qed.
Lemma lem3125592 (x : int) (y : int) : (term354 x y) = (term354 x y).
Proof. exact (eq_refl (term354 x y)). Qed.
Lemma lem3125595 (x : int) (y : int) : (term356 x y) = (term378 x y).
Proof. exact (MK_COMB (@lem3125591 x y) (@lem3125592 x y)). Qed.
Lemma lem3125596 (x : int) (y : int) (h1 : term378 x y) : term378 x y.
Proof. exact (h1). Qed.
Lemma lem3125597 (x : int) (y : int) (h1 : term378 x y) : term354 x y.
Proof. exact (proj2 (@lem3125596 x y h1)). Qed.
Lemma lem3125598 (x : int) (y : int) (h1 : term378 x y) : term376 x y.
Proof. exact (proj1 (@lem3125596 x y h1)). Qed.
Lemma lem3125599 (x : int) (y : int) (h1 : term378 x y) : term366 x y.
Proof. exact (proj2 (@lem3125598 x y h1)). Qed.
Lemma lem3125602 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3125603 : term379 = term380.
Proof. exact (@lem3125602 term296 term275). Qed.
Lemma lem3125605 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3125606 : term275 = term326.
Proof. exact (@lem3125605 term22). Qed.
Lemma lem3125608 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3125609 : term296 = term381.
Proof. exact (@lem3125608 (NUMERAL 0)). Qed.
Lemma lem3125610 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3125611 : term382 = term383.
Proof. exact (MK_COMB (@lem3125610) (@lem3125609)). Qed.
Lemma lem3125612 : term380 = term384.
Proof. exact (MK_COMB (@lem3125611) (@lem3125606)). Qed.
Lemma lem3125613 : term385.
Proof. exact (@lem1980255 term296 term275 term275 term275). Qed.
Lemma lem3125615 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3125616 : term380 = term387.
Proof. exact (@lem3125615 (NUMERAL 0) term22). Qed.
Lemma lem3125617 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3125618 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3125619 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3125618 h1) (fun h1 : term387 = True => @lem3125617)). Qed.
Lemma lem3125620 : term387 = True.
Proof. exact (EQ_MP (@lem3125619) (@lem3125617)). Qed.
Lemma lem3125621 : term380 = True.
Proof. exact (TRANS (@lem3125616) (@lem3125620)). Qed.
Lemma lem3125622 : True = term380.
Proof. exact (SYM (@lem3125621)). Qed.
Lemma lem3125623 : term380.
Proof. exact (EQ_MP (@lem3125622) (@lem0)). Qed.
Lemma lem3125624 : term388.
Proof. exact (@lem3125613 (@lem3125623)). Qed.
Lemma lem3125626 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3125627 : term380 = term387.
Proof. exact (@lem3125626 (NUMERAL 0) term22). Qed.
Lemma lem3125628 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3125629 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3125630 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3125629 h1) (fun h1 : term387 = True => @lem3125628)). Qed.
Lemma lem3125631 : term387 = True.
Proof. exact (EQ_MP (@lem3125630) (@lem3125628)). Qed.
Lemma lem3125632 : term380 = True.
Proof. exact (TRANS (@lem3125627) (@lem3125631)). Qed.
Lemma lem3125633 : True = term380.
Proof. exact (SYM (@lem3125632)). Qed.
Lemma lem3125634 : term380.
Proof. exact (EQ_MP (@lem3125633) (@lem0)). Qed.
Lemma lem3125635 : term384 = term389.
Proof. exact (@lem3125624 (@lem3125634)). Qed.
Lemma lem3125637 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3125638 : term337 = term338.
Proof. exact (@lem3125637 term22 term22). Qed.
Lemma lem3125639 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3125640 : term340 = term22.
Proof. exact (EQ_MP (@lem3125639) (@lem940073)). Qed.
Lemma lem3125641 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3125642 : term338 = term275.
Proof. exact (MK_COMB (@lem3125641) (@lem3125640)). Qed.
Lemma lem3125643 : term337 = term275.
Proof. exact (TRANS (@lem3125638) (@lem3125642)). Qed.
Lemma lem3125645 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3125646 : term391 = term296.
Proof. exact (@lem3125645 term22). Qed.
Lemma lem3125647 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3125648 : term392 = term382.
Proof. exact (MK_COMB (@lem3125647) (@lem3125646)). Qed.
Lemma lem3125649 : term389 = term380.
Proof. exact (MK_COMB (@lem3125648) (@lem3125643)). Qed.
Lemma lem3125651 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3125652 : term380 = term387.
Proof. exact (@lem3125651 (NUMERAL 0) term22). Qed.
Lemma lem3125653 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3125654 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3125655 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3125654 h1) (fun h1 : term387 = True => @lem3125653)). Qed.
Lemma lem3125656 : term387 = True.
Proof. exact (EQ_MP (@lem3125655) (@lem3125653)). Qed.
Lemma lem3125657 : term380 = True.
Proof. exact (TRANS (@lem3125652) (@lem3125656)). Qed.
Lemma lem3125658 : term389 = True.
Proof. exact (TRANS (@lem3125649) (@lem3125657)). Qed.
Lemma lem3125659 : term384 = True.
Proof. exact (TRANS (@lem3125635) (@lem3125658)). Qed.
Lemma lem3125660 : term380 = True.
Proof. exact (TRANS (@lem3125612) (@lem3125659)). Qed.
Lemma lem3125661 : term379 = True.
Proof. exact (TRANS (@lem3125603) (@lem3125660)). Qed.
Lemma lem3125662 : True = term379.
Proof. exact (SYM (@lem3125661)). Qed.
Lemma lem3125663 : term379.
Proof. exact (EQ_MP (@lem3125662) (@lem0)). Qed.
Lemma lem3125664 (x : int) (y : int) (h1 : term378 x y) : term393 x y.
Proof. exact (conj (@lem3125663) (@lem3125599 x y h1)). Qed.
Lemma lem3125666 (x : real) (y : real) : term394 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3125667 (x : int) (y : int) : term395 x y.
Proof. exact (@lem3125666 term275 (term287 x y)). Qed.
Lemma lem3125668 (x : int) (y : int) (h1 : term378 x y) : term396 x y.
Proof. exact (@lem3125667 x y (@lem3125664 x y h1)). Qed.
Lemma lem3125669 (x : int) (y : int) : (term397 x y) = (term287 x y).
Proof. exact (@lem1982733 (term287 x y)). Qed.
Lemma lem3125670 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3125671 (x : int) (y : int) : (term398 x y) = (term364 x y).
Proof. exact (MK_COMB (@lem3125670) (@lem3125669 x y)). Qed.
Lemma lem3125672 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3125673 (x : int) (y : int) : (term396 x y) = (term366 x y).
Proof. exact (MK_COMB (@lem3125671 x y) (@lem3125672)). Qed.
Lemma lem3125674 (x : int) (y : int) (h1 : term378 x y) : term366 x y.
Proof. exact (EQ_MP (@lem3125673 x y) (@lem3125668 x y h1)). Qed.
Lemma lem3125676 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3125677 : term379 = term380.
Proof. exact (@lem3125676 term296 term275). Qed.
Lemma lem3125679 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3125680 : term275 = term326.
Proof. exact (@lem3125679 term22). Qed.
Lemma lem3125682 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3125683 : term296 = term381.
Proof. exact (@lem3125682 (NUMERAL 0)). Qed.
Lemma lem3125684 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3125685 : term382 = term383.
Proof. exact (MK_COMB (@lem3125684) (@lem3125683)). Qed.
Lemma lem3125686 : term380 = term384.
Proof. exact (MK_COMB (@lem3125685) (@lem3125680)). Qed.
Lemma lem3125687 : term385.
Proof. exact (@lem1980255 term296 term275 term275 term275). Qed.
Lemma lem3125689 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3125690 : term380 = term387.
Proof. exact (@lem3125689 (NUMERAL 0) term22). Qed.
Lemma lem3125691 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3125692 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3125693 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3125692 h1) (fun h1 : term387 = True => @lem3125691)). Qed.
Lemma lem3125694 : term387 = True.
Proof. exact (EQ_MP (@lem3125693) (@lem3125691)). Qed.
Lemma lem3125695 : term380 = True.
Proof. exact (TRANS (@lem3125690) (@lem3125694)). Qed.
Lemma lem3125696 : True = term380.
Proof. exact (SYM (@lem3125695)). Qed.
Lemma lem3125697 : term380.
Proof. exact (EQ_MP (@lem3125696) (@lem0)). Qed.
Lemma lem3125698 : term388.
Proof. exact (@lem3125687 (@lem3125697)). Qed.
Lemma lem3125700 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3125701 : term380 = term387.
Proof. exact (@lem3125700 (NUMERAL 0) term22). Qed.
Lemma lem3125702 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3125703 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3125704 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3125703 h1) (fun h1 : term387 = True => @lem3125702)). Qed.
Lemma lem3125705 : term387 = True.
Proof. exact (EQ_MP (@lem3125704) (@lem3125702)). Qed.
Lemma lem3125706 : term380 = True.
Proof. exact (TRANS (@lem3125701) (@lem3125705)). Qed.
Lemma lem3125707 : True = term380.
Proof. exact (SYM (@lem3125706)). Qed.
Lemma lem3125708 : term380.
Proof. exact (EQ_MP (@lem3125707) (@lem0)). Qed.
Lemma lem3125709 : term384 = term389.
Proof. exact (@lem3125698 (@lem3125708)). Qed.
Lemma lem3125711 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3125712 : term337 = term338.
Proof. exact (@lem3125711 term22 term22). Qed.
Lemma lem3125713 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3125714 : term340 = term22.
Proof. exact (EQ_MP (@lem3125713) (@lem940073)). Qed.
Lemma lem3125715 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3125716 : term338 = term275.
Proof. exact (MK_COMB (@lem3125715) (@lem3125714)). Qed.
Lemma lem3125717 : term337 = term275.
Proof. exact (TRANS (@lem3125712) (@lem3125716)). Qed.
Lemma lem3125719 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3125720 : term391 = term296.
Proof. exact (@lem3125719 term22). Qed.
Lemma lem3125721 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3125722 : term392 = term382.
Proof. exact (MK_COMB (@lem3125721) (@lem3125720)). Qed.
Lemma lem3125723 : term389 = term380.
Proof. exact (MK_COMB (@lem3125722) (@lem3125717)). Qed.
Lemma lem3125725 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3125726 : term380 = term387.
Proof. exact (@lem3125725 (NUMERAL 0) term22). Qed.
Lemma lem3125727 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3125728 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3125729 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3125728 h1) (fun h1 : term387 = True => @lem3125727)). Qed.
Lemma lem3125730 : term387 = True.
Proof. exact (EQ_MP (@lem3125729) (@lem3125727)). Qed.
Lemma lem3125731 : term380 = True.
Proof. exact (TRANS (@lem3125726) (@lem3125730)). Qed.
Lemma lem3125732 : term389 = True.
Proof. exact (TRANS (@lem3125723) (@lem3125731)). Qed.
Lemma lem3125733 : term384 = True.
Proof. exact (TRANS (@lem3125709) (@lem3125732)). Qed.
Lemma lem3125734 : term380 = True.
Proof. exact (TRANS (@lem3125686) (@lem3125733)). Qed.
Lemma lem3125735 : term379 = True.
Proof. exact (TRANS (@lem3125677) (@lem3125734)). Qed.
Lemma lem3125736 : True = term379.
Proof. exact (SYM (@lem3125735)). Qed.
Lemma lem3125737 : term379.
Proof. exact (EQ_MP (@lem3125736) (@lem0)). Qed.
Lemma lem3125738 (x : int) (y : int) (h1 : term378 x y) : term399 x y.
Proof. exact (conj (@lem3125737) (@lem3125597 x y h1)). Qed.
Lemma lem3125740 (x : real) (y : real) : term394 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3125741 (x : int) (y : int) : term400 x y.
Proof. exact (@lem3125740 term275 (term349 x y)). Qed.
Lemma lem3125742 (x : int) (y : int) (h1 : term378 x y) : term401 x y.
Proof. exact (@lem3125741 x y (@lem3125738 x y h1)). Qed.
Lemma lem3125743 (x : int) (y : int) : (term402 x y) = (term349 x y).
Proof. exact (@lem1982733 (term349 x y)). Qed.
Lemma lem3125744 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3125745 (x : int) (y : int) : (term403 x y) = (term353 x y).
Proof. exact (MK_COMB (@lem3125744) (@lem3125743 x y)). Qed.
Lemma lem3125746 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3125747 (x : int) (y : int) : (term401 x y) = (term354 x y).
Proof. exact (MK_COMB (@lem3125745 x y) (@lem3125746)). Qed.
Lemma lem3125748 (x : int) (y : int) (h1 : term378 x y) : term354 x y.
Proof. exact (EQ_MP (@lem3125747 x y) (@lem3125742 x y h1)). Qed.
Lemma lem3125749 (x : int) (y : int) (h1 : term378 x y) : term404 x y.
Proof. exact (conj (@lem3125748 x y h1) (@lem3125674 x y h1)). Qed.
Lemma lem3125751 (x : real) (y : real) : term405 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3125752 (x : int) (y : int) : term406 x y.
Proof. exact (@lem3125751 (term349 x y) (term287 x y)). Qed.
Lemma lem3125753 (x : int) (y : int) (h1 : term378 x y) : term407 x y.
Proof. exact (@lem3125752 x y (@lem3125749 x y h1)). Qed.
Lemma lem3125754 (x : int) (y : int) : (term408 x y) = (term409 x y).
Proof. exact (@lem1982753 (term369 x) (real_of_int x) (term348 y) (real_of_int y)). Qed.
Lemma lem3125755 (x : int) : (term410 x) = (term411 x).
Proof. exact (@lem1982713 term321 (real_of_int x)). Qed.
Lemma lem3125757 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3125758 : term275 = term326.
Proof. exact (@lem3125757 term22). Qed.
Lemma lem3125760 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3125761 : term321 = term329.
Proof. exact (@lem3125760 term22). Qed.
Lemma lem3125762 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3125763 : term412 = term413.
Proof. exact (MK_COMB (@lem3125762) (@lem3125761)). Qed.
Lemma lem3125764 : term414 = term415.
Proof. exact (MK_COMB (@lem3125763) (@lem3125758)). Qed.
Lemma lem3125765 : term416.
Proof. exact (@lem1981473 term321 term275 term275 term275 term296 term275). Qed.
Lemma lem3125767 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3125768 : term380 = term387.
Proof. exact (@lem3125767 (NUMERAL 0) term22). Qed.
Lemma lem3125769 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3125770 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3125771 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3125770 h1) (fun h1 : term387 = True => @lem3125769)). Qed.
Lemma lem3125772 : term387 = True.
Proof. exact (EQ_MP (@lem3125771) (@lem3125769)). Qed.
Lemma lem3125773 : term380 = True.
Proof. exact (TRANS (@lem3125768) (@lem3125772)). Qed.
Lemma lem3125774 : True = term380.
Proof. exact (SYM (@lem3125773)). Qed.
Lemma lem3125775 : term380.
Proof. exact (EQ_MP (@lem3125774) (@lem0)). Qed.
Lemma lem3125776 : term417.
Proof. exact (@lem3125765 (@lem3125775)). Qed.
Lemma lem3125778 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3125779 : term380 = term387.
Proof. exact (@lem3125778 (NUMERAL 0) term22). Qed.
Lemma lem3125780 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3125781 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3125782 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3125781 h1) (fun h1 : term387 = True => @lem3125780)). Qed.
Lemma lem3125783 : term387 = True.
Proof. exact (EQ_MP (@lem3125782) (@lem3125780)). Qed.
Lemma lem3125784 : term380 = True.
Proof. exact (TRANS (@lem3125779) (@lem3125783)). Qed.
Lemma lem3125785 : True = term380.
Proof. exact (SYM (@lem3125784)). Qed.
Lemma lem3125786 : term380.
Proof. exact (EQ_MP (@lem3125785) (@lem0)). Qed.
Lemma lem3125787 : term418.
Proof. exact (@lem3125776 (@lem3125786)). Qed.
Lemma lem3125789 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3125790 : term380 = term387.
Proof. exact (@lem3125789 (NUMERAL 0) term22). Qed.
Lemma lem3125791 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3125792 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3125793 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3125792 h1) (fun h1 : term387 = True => @lem3125791)). Qed.
Lemma lem3125794 : term387 = True.
Proof. exact (EQ_MP (@lem3125793) (@lem3125791)). Qed.
Lemma lem3125795 : term380 = True.
Proof. exact (TRANS (@lem3125790) (@lem3125794)). Qed.
Lemma lem3125796 : True = term380.
Proof. exact (SYM (@lem3125795)). Qed.
Lemma lem3125797 : term380.
Proof. exact (EQ_MP (@lem3125796) (@lem0)). Qed.
Lemma lem3125798 : term419.
Proof. exact (@lem3125787 (@lem3125797)). Qed.
Lemma lem3125800 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3125801 : term337 = term338.
Proof. exact (@lem3125800 term22 term22). Qed.
Lemma lem3125802 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3125803 : term340 = term22.
Proof. exact (EQ_MP (@lem3125802) (@lem940073)). Qed.
Lemma lem3125804 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3125805 : term338 = term275.
Proof. exact (MK_COMB (@lem3125804) (@lem3125803)). Qed.
Lemma lem3125806 : term337 = term275.
Proof. exact (TRANS (@lem3125801) (@lem3125805)). Qed.
Lemma lem3125808 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3125809 : term332 = term343.
Proof. exact (@lem3125808 term22 term22). Qed.
Lemma lem3125810 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3125811 : term340 = term22.
Proof. exact (EQ_MP (@lem3125810) (@lem940073)). Qed.
Lemma lem3125812 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3125813 : term338 = term275.
Proof. exact (MK_COMB (@lem3125812) (@lem3125811)). Qed.
Lemma lem3125814 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3125815 : term343 = term321.
Proof. exact (MK_COMB (@lem3125814) (@lem3125813)). Qed.
Lemma lem3125816 : term332 = term321.
Proof. exact (TRANS (@lem3125809) (@lem3125815)). Qed.
Lemma lem3125817 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3125818 : term420 = term412.
Proof. exact (MK_COMB (@lem3125817) (@lem3125816)). Qed.
Lemma lem3125819 : term421 = term414.
Proof. exact (MK_COMB (@lem3125818) (@lem3125806)). Qed.
Lemma lem3125821 (m : nat) : (term422 m) = term296.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3125822 : term414 = term296.
Proof. exact (@lem3125821 term22). Qed.
Lemma lem3125823 : term421 = term296.
Proof. exact (TRANS (@lem3125819) (@lem3125822)). Qed.
Lemma lem3125824 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3125825 : term423 = term424.
Proof. exact (MK_COMB (@lem3125824) (@lem3125823)). Qed.
Lemma lem3125826 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem3125827 : term425 = term391.
Proof. exact (MK_COMB (@lem3125825) (@lem3125826)). Qed.
Lemma lem3125829 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3125830 : term391 = term296.
Proof. exact (@lem3125829 term22). Qed.
Lemma lem3125831 : term425 = term296.
Proof. exact (TRANS (@lem3125827) (@lem3125830)). Qed.
Lemma lem3125833 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3125834 : term337 = term338.
Proof. exact (@lem3125833 term22 term22). Qed.
Lemma lem3125835 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3125836 : term340 = term22.
Proof. exact (EQ_MP (@lem3125835) (@lem940073)). Qed.
Lemma lem3125837 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3125838 : term338 = term275.
Proof. exact (MK_COMB (@lem3125837) (@lem3125836)). Qed.
Lemma lem3125839 : term337 = term275.
Proof. exact (TRANS (@lem3125834) (@lem3125838)). Qed.
Lemma lem3125840 : term424 = term424.
Proof. exact (eq_refl term424). Qed.
Lemma lem3125841 : term426 = term391.
Proof. exact (MK_COMB (@lem3125840) (@lem3125839)). Qed.
Lemma lem3125843 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3125844 : term391 = term296.
Proof. exact (@lem3125843 term22). Qed.
Lemma lem3125845 : term426 = term296.
Proof. exact (TRANS (@lem3125841) (@lem3125844)). Qed.
Lemma lem3125846 : term296 = term426.
Proof. exact (SYM (@lem3125845)). Qed.
Lemma lem3125847 : term425 = term426.
Proof. exact (TRANS (@lem3125831) (@lem3125846)). Qed.
Lemma lem3125848 : term415 = term381.
Proof. exact (@lem3125798 (@lem3125847)). Qed.
Lemma lem3125849 : term414 = term381.
Proof. exact (TRANS (@lem3125764) (@lem3125848)). Qed.
Lemma lem3125851 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3125852 : term381 = term296.
Proof. exact (@lem3125851 term296). Qed.
Lemma lem3125853 : term414 = term296.
Proof. exact (TRANS (@lem3125849) (@lem3125852)). Qed.
Lemma lem3125854 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3125855 : term427 = term424.
Proof. exact (MK_COMB (@lem3125854) (@lem3125853)). Qed.
Lemma lem3125856 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3125857 (x : int) : (term411 x) = (term428 x).
Proof. exact (MK_COMB (@lem3125855) (@lem3125856 x)). Qed.
Lemma lem3125858 (x : int) : (term410 x) = (term428 x).
Proof. exact (TRANS (@lem3125755 x) (@lem3125857 x)). Qed.
Lemma lem3125859 (x : int) : (term428 x) = term296.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem3125860 (x : int) : (term410 x) = term296.
Proof. exact (TRANS (@lem3125858 x) (@lem3125859 x)). Qed.
Lemma lem3125861 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3125862 (x : int) : (term429 x) = term350.
Proof. exact (MK_COMB (@lem3125861) (@lem3125860 x)). Qed.
Lemma lem3125863 (y : int) : (term430 y) = (term431 y).
Proof. exact (@lem1982759 (term369 y) (real_of_int y) term321). Qed.
Lemma lem3125864 (y : int) : (term410 y) = (term411 y).
Proof. exact (@lem1982713 term321 (real_of_int y)). Qed.
Lemma lem3125866 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3125867 : term275 = term326.
Proof. exact (@lem3125866 term22). Qed.
Lemma lem3125869 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3125870 : term321 = term329.
Proof. exact (@lem3125869 term22). Qed.
Lemma lem3125871 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3125872 : term412 = term413.
Proof. exact (MK_COMB (@lem3125871) (@lem3125870)). Qed.
Lemma lem3125873 : term414 = term415.
Proof. exact (MK_COMB (@lem3125872) (@lem3125867)). Qed.
Lemma lem3125874 : term416.
Proof. exact (@lem1981473 term321 term275 term275 term275 term296 term275). Qed.
Lemma lem3125876 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3125877 : term380 = term387.
Proof. exact (@lem3125876 (NUMERAL 0) term22). Qed.
Lemma lem3125878 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3125879 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3125880 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3125879 h1) (fun h1 : term387 = True => @lem3125878)). Qed.
Lemma lem3125881 : term387 = True.
Proof. exact (EQ_MP (@lem3125880) (@lem3125878)). Qed.
Lemma lem3125882 : term380 = True.
Proof. exact (TRANS (@lem3125877) (@lem3125881)). Qed.
Lemma lem3125883 : True = term380.
Proof. exact (SYM (@lem3125882)). Qed.
Lemma lem3125884 : term380.
Proof. exact (EQ_MP (@lem3125883) (@lem0)). Qed.
Lemma lem3125885 : term417.
Proof. exact (@lem3125874 (@lem3125884)). Qed.
Lemma lem3125887 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3125888 : term380 = term387.
Proof. exact (@lem3125887 (NUMERAL 0) term22). Qed.
Lemma lem3125889 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3125890 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3125891 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3125890 h1) (fun h1 : term387 = True => @lem3125889)). Qed.
Lemma lem3125892 : term387 = True.
Proof. exact (EQ_MP (@lem3125891) (@lem3125889)). Qed.
Lemma lem3125893 : term380 = True.
Proof. exact (TRANS (@lem3125888) (@lem3125892)). Qed.
Lemma lem3125894 : True = term380.
Proof. exact (SYM (@lem3125893)). Qed.
Lemma lem3125895 : term380.
Proof. exact (EQ_MP (@lem3125894) (@lem0)). Qed.
Lemma lem3125896 : term418.
Proof. exact (@lem3125885 (@lem3125895)). Qed.
Lemma lem3125898 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3125899 : term380 = term387.
Proof. exact (@lem3125898 (NUMERAL 0) term22). Qed.
Lemma lem3125900 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3125901 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3125902 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3125901 h1) (fun h1 : term387 = True => @lem3125900)). Qed.
Lemma lem3125903 : term387 = True.
Proof. exact (EQ_MP (@lem3125902) (@lem3125900)). Qed.
Lemma lem3125904 : term380 = True.
Proof. exact (TRANS (@lem3125899) (@lem3125903)). Qed.
Lemma lem3125905 : True = term380.
Proof. exact (SYM (@lem3125904)). Qed.
Lemma lem3125906 : term380.
Proof. exact (EQ_MP (@lem3125905) (@lem0)). Qed.
Lemma lem3125907 : term419.
Proof. exact (@lem3125896 (@lem3125906)). Qed.
Lemma lem3125909 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3125910 : term337 = term338.
Proof. exact (@lem3125909 term22 term22). Qed.
Lemma lem3125911 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3125912 : term340 = term22.
Proof. exact (EQ_MP (@lem3125911) (@lem940073)). Qed.
Lemma lem3125913 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3125914 : term338 = term275.
Proof. exact (MK_COMB (@lem3125913) (@lem3125912)). Qed.
Lemma lem3125915 : term337 = term275.
Proof. exact (TRANS (@lem3125910) (@lem3125914)). Qed.
Lemma lem3125917 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3125918 : term332 = term343.
Proof. exact (@lem3125917 term22 term22). Qed.
Lemma lem3125919 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3125920 : term340 = term22.
Proof. exact (EQ_MP (@lem3125919) (@lem940073)). Qed.
Lemma lem3125921 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3125922 : term338 = term275.
Proof. exact (MK_COMB (@lem3125921) (@lem3125920)). Qed.
Lemma lem3125923 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3125924 : term343 = term321.
Proof. exact (MK_COMB (@lem3125923) (@lem3125922)). Qed.
Lemma lem3125925 : term332 = term321.
Proof. exact (TRANS (@lem3125918) (@lem3125924)). Qed.
Lemma lem3125926 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3125927 : term420 = term412.
Proof. exact (MK_COMB (@lem3125926) (@lem3125925)). Qed.
Lemma lem3125928 : term421 = term414.
Proof. exact (MK_COMB (@lem3125927) (@lem3125915)). Qed.
Lemma lem3125930 (m : nat) : (term422 m) = term296.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3125931 : term414 = term296.
Proof. exact (@lem3125930 term22). Qed.
Lemma lem3125932 : term421 = term296.
Proof. exact (TRANS (@lem3125928) (@lem3125931)). Qed.
Lemma lem3125933 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3125934 : term423 = term424.
Proof. exact (MK_COMB (@lem3125933) (@lem3125932)). Qed.
Lemma lem3125935 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem3125936 : term425 = term391.
Proof. exact (MK_COMB (@lem3125934) (@lem3125935)). Qed.
Lemma lem3125938 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3125939 : term391 = term296.
Proof. exact (@lem3125938 term22). Qed.
Lemma lem3125940 : term425 = term296.
Proof. exact (TRANS (@lem3125936) (@lem3125939)). Qed.
Lemma lem3125942 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3125943 : term337 = term338.
Proof. exact (@lem3125942 term22 term22). Qed.
Lemma lem3125944 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3125945 : term340 = term22.
Proof. exact (EQ_MP (@lem3125944) (@lem940073)). Qed.
Lemma lem3125946 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3125947 : term338 = term275.
Proof. exact (MK_COMB (@lem3125946) (@lem3125945)). Qed.
Lemma lem3125948 : term337 = term275.
Proof. exact (TRANS (@lem3125943) (@lem3125947)). Qed.
Lemma lem3125949 : term424 = term424.
Proof. exact (eq_refl term424). Qed.
Lemma lem3125950 : term426 = term391.
Proof. exact (MK_COMB (@lem3125949) (@lem3125948)). Qed.
Lemma lem3125952 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3125953 : term391 = term296.
Proof. exact (@lem3125952 term22). Qed.
Lemma lem3125954 : term426 = term296.
Proof. exact (TRANS (@lem3125950) (@lem3125953)). Qed.
Lemma lem3125955 : term296 = term426.
Proof. exact (SYM (@lem3125954)). Qed.
Lemma lem3125956 : term425 = term426.
Proof. exact (TRANS (@lem3125940) (@lem3125955)). Qed.
Lemma lem3125957 : term415 = term381.
Proof. exact (@lem3125907 (@lem3125956)). Qed.
Lemma lem3125958 : term414 = term381.
Proof. exact (TRANS (@lem3125873) (@lem3125957)). Qed.
Lemma lem3125960 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3125961 : term381 = term296.
Proof. exact (@lem3125960 term296). Qed.
Lemma lem3125962 : term414 = term296.
Proof. exact (TRANS (@lem3125958) (@lem3125961)). Qed.
Lemma lem3125963 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3125964 : term427 = term424.
Proof. exact (MK_COMB (@lem3125963) (@lem3125962)). Qed.
Lemma lem3125965 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3125966 (y : int) : (term411 y) = (term428 y).
Proof. exact (MK_COMB (@lem3125964) (@lem3125965 y)). Qed.
Lemma lem3125967 (y : int) : (term410 y) = (term428 y).
Proof. exact (TRANS (@lem3125864 y) (@lem3125966 y)). Qed.
Lemma lem3125968 (y : int) : (term428 y) = term296.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem3125969 (y : int) : (term410 y) = term296.
Proof. exact (TRANS (@lem3125967 y) (@lem3125968 y)). Qed.
Lemma lem3125970 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3125971 (y : int) : (term429 y) = term350.
Proof. exact (MK_COMB (@lem3125970) (@lem3125969 y)). Qed.
Lemma lem3125972 : term321 = term321.
Proof. exact (eq_refl term321). Qed.
Lemma lem3125973 (y : int) : (term431 y) = term432.
Proof. exact (MK_COMB (@lem3125971 y) (@lem3125972)). Qed.
Lemma lem3125974 (y : int) : (term430 y) = term432.
Proof. exact (TRANS (@lem3125863 y) (@lem3125973 y)). Qed.
Lemma lem3125975 : term432 = term321.
Proof. exact (@lem1982721 term321). Qed.
Lemma lem3125976 (y : int) : (term430 y) = term321.
Proof. exact (TRANS (@lem3125974 y) (@lem3125975)). Qed.
Lemma lem3125977 (x : int) (y : int) : (term409 x y) = term432.
Proof. exact (MK_COMB (@lem3125862 x) (@lem3125976 y)). Qed.
Lemma lem3125978 (x : int) (y : int) : (term408 x y) = term432.
Proof. exact (TRANS (@lem3125754 x y) (@lem3125977 x y)). Qed.
Lemma lem3125979 : term432 = term321.
Proof. exact (@lem1982721 term321). Qed.
Lemma lem3125980 (x : int) (y : int) : (term408 x y) = term321.
Proof. exact (TRANS (@lem3125978 x y) (@lem3125979)). Qed.
Lemma lem3125981 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3125982 (x : int) (y : int) : (term433 x y) = term434.
Proof. exact (MK_COMB (@lem3125981) (@lem3125980 x y)). Qed.
Lemma lem3125983 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3125984 (x : int) (y : int) : (term407 x y) = term435.
Proof. exact (MK_COMB (@lem3125982 x y) (@lem3125983)). Qed.
Lemma lem3125985 (x : int) (y : int) (h1 : term378 x y) : term435.
Proof. exact (EQ_MP (@lem3125984 x y) (@lem3125753 x y h1)). Qed.
Lemma lem3125987 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3125988 : term435 = term436.
Proof. exact (@lem3125987 term296 term321). Qed.
Lemma lem3125990 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3125991 : term321 = term329.
Proof. exact (@lem3125990 term22). Qed.
Lemma lem3125993 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3125994 : term296 = term381.
Proof. exact (@lem3125993 (NUMERAL 0)). Qed.
Lemma lem3125995 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3125996 : term437 = term438.
Proof. exact (MK_COMB (@lem3125995) (@lem3125994)). Qed.
Lemma lem3125997 : term436 = term439.
Proof. exact (MK_COMB (@lem3125996) (@lem3125991)). Qed.
Lemma lem3125998 : term440.
Proof. exact (@lem1980026 term296 term275 term321 term275). Qed.
Lemma lem3126000 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126001 : term380 = term387.
Proof. exact (@lem3126000 (NUMERAL 0) term22). Qed.
Lemma lem3126002 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126003 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3126004 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126003 h1) (fun h1 : term387 = True => @lem3126002)). Qed.
Lemma lem3126005 : term387 = True.
Proof. exact (EQ_MP (@lem3126004) (@lem3126002)). Qed.
Lemma lem3126006 : term380 = True.
Proof. exact (TRANS (@lem3126001) (@lem3126005)). Qed.
Lemma lem3126007 : True = term380.
Proof. exact (SYM (@lem3126006)). Qed.
Lemma lem3126008 : term380.
Proof. exact (EQ_MP (@lem3126007) (@lem0)). Qed.
Lemma lem3126009 : term441.
Proof. exact (@lem3125998 (@lem3126008)). Qed.
Lemma lem3126011 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126012 : term380 = term387.
Proof. exact (@lem3126011 (NUMERAL 0) term22). Qed.
Lemma lem3126013 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126014 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3126015 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126014 h1) (fun h1 : term387 = True => @lem3126013)). Qed.
Lemma lem3126016 : term387 = True.
Proof. exact (EQ_MP (@lem3126015) (@lem3126013)). Qed.
Lemma lem3126017 : term380 = True.
Proof. exact (TRANS (@lem3126012) (@lem3126016)). Qed.
Lemma lem3126018 : True = term380.
Proof. exact (SYM (@lem3126017)). Qed.
Lemma lem3126019 : term380.
Proof. exact (EQ_MP (@lem3126018) (@lem0)). Qed.
Lemma lem3126020 : term439 = term442.
Proof. exact (@lem3126009 (@lem3126019)). Qed.
Lemma lem3126022 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3126023 : term332 = term343.
Proof. exact (@lem3126022 term22 term22). Qed.
Lemma lem3126024 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3126025 : term340 = term22.
Proof. exact (EQ_MP (@lem3126024) (@lem940073)). Qed.
Lemma lem3126026 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3126027 : term338 = term275.
Proof. exact (MK_COMB (@lem3126026) (@lem3126025)). Qed.
Lemma lem3126028 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3126029 : term343 = term321.
Proof. exact (MK_COMB (@lem3126028) (@lem3126027)). Qed.
Lemma lem3126030 : term332 = term321.
Proof. exact (TRANS (@lem3126023) (@lem3126029)). Qed.
Lemma lem3126032 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3126033 : term391 = term296.
Proof. exact (@lem3126032 term22). Qed.
Lemma lem3126034 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3126035 : term443 = term437.
Proof. exact (MK_COMB (@lem3126034) (@lem3126033)). Qed.
Lemma lem3126036 : term442 = term436.
Proof. exact (MK_COMB (@lem3126035) (@lem3126030)). Qed.
Lemma lem3126038 (m : nat) (n : nat) : (term444 m n) = (term445 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3126039 : term436 = term446.
Proof. exact (@lem3126038 (NUMERAL 0) term22). Qed.
Lemma lem3126040 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126041 (h1 : term121 = (BIT1 0)) : (term22 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3126042 : (term121 = (BIT1 0)) = ((term22 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126041 h1) (fun h1 : (term22 = (NUMERAL 0)) = False => @lem3126040)). Qed.
Lemma lem3126043 : (term22 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3126042) (@lem3126040)). Qed.
Lemma lem3126044 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3126045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3126046 : term447 = (and True).
Proof. exact (MK_COMB (@lem3126045) (@lem3126044)). Qed.
Lemma lem3126047 : term446 = (True /\ False).
Proof. exact (MK_COMB (@lem3126046) (@lem3126043)). Qed.
Lemma lem3126049 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3126050 : term446 = False.
Proof. exact (TRANS (@lem3126047) (@lem3126049)). Qed.
Lemma lem3126051 : term436 = False.
Proof. exact (TRANS (@lem3126039) (@lem3126050)). Qed.
Lemma lem3126052 : term442 = False.
Proof. exact (TRANS (@lem3126036) (@lem3126051)). Qed.
Lemma lem3126053 : term439 = False.
Proof. exact (TRANS (@lem3126020) (@lem3126052)). Qed.
Lemma lem3126054 : term436 = False.
Proof. exact (TRANS (@lem3125997) (@lem3126053)). Qed.
Lemma lem3126055 : term435 = False.
Proof. exact (TRANS (@lem3125988) (@lem3126054)). Qed.
Lemma lem3126056 (x : int) (y : int) (h1 : term378 x y) : False.
Proof. exact (EQ_MP (@lem3126055) (@lem3125985 x y h1)). Qed.
Lemma lem3126057 (x : int) (y : int) (h1 : term356 x y) : term356 x y.
Proof. exact (h1). Qed.
Lemma lem3126058 (x : int) (y : int) (h1 : term356 x y) : term378 x y.
Proof. exact (EQ_MP (@lem3125595 x y) (@lem3126057 x y h1)). Qed.
Lemma lem3126059 (x : int) (y : int) (h1 : term356 x y) : (term378 x y) = False.
Proof. exact (prop_ext (fun h2 : term378 x y => @lem3126056 x y h2) (fun h2 : False => @lem3126058 x y h1)). Qed.
Lemma lem3126060 (x : int) (y : int) (h1 : term356 x y) : False.
Proof. exact (EQ_MP (@lem3126059 x y h1) (@lem3126058 x y h1)). Qed.
Lemma lem3126061 (x : int) (y : int) (h1 : term302 x y) : term302 x y.
Proof. exact (h1). Qed.
Lemma lem3126062 (x : int) (y : int) (h1 : term302 x y) : term356 x y.
Proof. exact (EQ_MP (@lem3125548 x y) (@lem3126061 x y h1)). Qed.
Lemma lem3126063 (x : int) (y : int) (h1 : term302 x y) : (term356 x y) = False.
Proof. exact (prop_ext (fun h2 : term356 x y => @lem3126060 x y h2) (fun h2 : False => @lem3126062 x y h1)). Qed.
Lemma lem3126064 (x : int) (y : int) (h1 : term302 x y) : False.
Proof. exact (EQ_MP (@lem3126063 x y h1) (@lem3126062 x y h1)). Qed.
Lemma lem3126065 (x : int) (y : int) : term448 x y.
Proof. exact (fun h0 : term302 x y => @lem3126064 x y h0). Qed.
Lemma lem3126066 (x : int) (y : int) : term449 x y.
Proof. exact (@lem1386578 (term450 x y)). Qed.
Lemma lem3126069 (x : int) (y : int) : term450 x y.
Proof. exact (@lem3126066 x y (@lem3126065 x y)). Qed.
Lemma lem3126070 (x : int) (y : int) : (term300 x y) = (term258 x y).
Proof. exact (SYM (@lem3125400 x y)). Qed.
Lemma lem3126071 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3126072 (x : int) (y : int) : (term450 x y) = (term256 x y).
Proof. exact (MK_COMB (@lem3126071) (@lem3126070 x y)). Qed.
Lemma lem3126073 (x : int) (y : int) : term256 x y.
Proof. exact (EQ_MP (@lem3126072 x y) (@lem3126069 x y)). Qed.
Lemma lem3126074 (x : int) (y : int) : term257 x y.
Proof. exact (EQ_MP (@lem3125319 x y) (@lem3126073 x y)). Qed.
Lemma lem3126075 (x : int) (y : int) (h1 : term257 x y) : term257 x y.
Proof. exact (h1). Qed.
Lemma lem3126076 (x : int) (y : int) (h1 : term260 x y) : term260 x y.
Proof. exact (h1). Qed.
Lemma lem3126077 (x : int) (y : int) (h1 : term257 x y) (h2 : term260 x y) : term261 x y.
Proof. exact (@lem3126075 x y h1 (@lem3126076 x y h2)). Qed.
Lemma lem3126078 (x : int) (y : int) (h1 : term260 x y) : term451 x y.
Proof. exact (fun h0 : term257 x y => @lem3126077 x y h0 h1). Qed.
Lemma lem3126079 (x : int) (y : int) (h1 : term257 x y) : term257 x y.
Proof. exact (h1). Qed.
Lemma lem3126080 (x : int) (y : int) (h1 : term257 x y) (h2 : term260 x y) : term261 x y.
Proof. exact (@lem3126078 x y h2 (@lem3126079 x y h1)). Qed.
Lemma lem3126081 (x : int) (y : int) (h1 : term257 x y) : term257 x y.
Proof. exact (fun h0 : term260 x y => @lem3126080 x y h1 h0). Qed.
Lemma lem3126082 (x : int) (y : int) : term452 x y.
Proof. exact (fun h0 : term257 x y => @lem3126081 x y h0). Qed.
Lemma lem3126084 (y : int) : term453 y.
Proof. exact (@lem9784 (y = term10)). Qed.
Lemma lem3126085 (y : int) : (term453 y) = (term454 y).
Proof. exact (eq_refl (term453 y)). Qed.
Lemma lem3126086 (y : int) : term454 y.
Proof. exact (EQ_MP (@lem3126085 y) (@lem3126084 y)). Qed.
Lemma lem3126087 (y : int) (h1 : y = term10) : y = term10.
Proof. exact (h1). Qed.
Lemma lem3126088 (y : int) (h1 : term135 y) : term135 y.
Proof. exact (h1). Qed.
Lemma lem3126089 (x : int) : term455 x.
Proof. exact (@lem2834258 x). Qed.
Lemma lem3126090 (x : int) : (term455 x) = (term456 x).
Proof. exact (eq_refl (term455 x)). Qed.
Lemma lem3126092 (y : int) (x : int) (h1 : term457 y x) : term457 y x.
Proof. exact (h1). Qed.
Lemma lem3126094 (x : int) : term456 x.
Proof. exact (EQ_MP (@lem3126090 x) (@lem3126089 x)). Qed.
Lemma lem3126095 (x : int) (y : int) : term458 x y.
Proof. exact (@lem3126094 (term459 x y)). Qed.
Lemma lem3126097 (p : Prop) (q : Prop) (r : Prop) : term460 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem3126098 (x : int) (y : int) : term461 x y.
Proof. exact (@lem3126097 (term462 x y) ((term463 x y) = (term459 x y)) (term464 x y)). Qed.
Lemma lem3126108 (y : int) (h1 : y = term10) : y = term10.
Proof. exact (h1). Qed.
Lemma lem3126109 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3126110 (y : int) (h1 : y = term10) : (@eq int y) = term183.
Proof. exact (MK_COMB (@lem3126109) (@lem3126108 y h1)). Qed.
Lemma lem3126111 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3126112 (y : int) (h1 : y = term10) : (y = term10) = (term10 = term10).
Proof. exact (MK_COMB (@lem3126110 y h1) (@lem3126111)). Qed.
Lemma lem3126114 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3126115 (x : int) : (x = x) = True.
Proof. exact (@lem3126114 int x). Qed.
Lemma lem3126116 : (term10 = term10) = True.
Proof. exact (@lem3126115 term10). Qed.
Lemma lem3126117 (y : int) (h1 : y = term10) : (y = term10) = True.
Proof. exact (TRANS (@lem3126112 y h1) (@lem3126116)). Qed.
Lemma lem3126118 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3126119 (y : int) (h1 : y = term10) : (term465 y) = (imp True).
Proof. exact (MK_COMB (@lem3126118) (@lem3126117 y h1)). Qed.
Lemma lem3126120 (x : int) : (term466 x) = (term466 x).
Proof. exact (eq_refl (term466 x)). Qed.
Lemma lem3126121 (x : int) (y : int) (h1 : y = term10) : (term457 y x) = (term467 x).
Proof. exact (MK_COMB (@lem3126119 y h1) (@lem3126120 x)). Qed.
Lemma lem3126123 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3126124 (x : int) : (term467 x) = (term466 x).
Proof. exact (@lem3126123 (term466 x)). Qed.
Lemma lem3126125 (x : int) (y : int) (h1 : y = term10) : (term457 y x) = (term466 x).
Proof. exact (TRANS (@lem3126121 x y h1) (@lem3126124 x)). Qed.
Lemma lem3126126 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3126127 (x : int) (y : int) (h1 : y = term10) : (term468 y x) = (term469 x).
Proof. exact (MK_COMB (@lem3126126) (@lem3126125 x y h1)). Qed.
Lemma lem3126129 (y : int) (h1 : y = term10) : y = term10.
Proof. exact (h1). Qed.
Lemma lem3126130 (x : int) : (int_mul x) = (int_mul x).
Proof. exact (eq_refl (int_mul x)). Qed.
Lemma lem3126131 (x : int) (y : int) (h1 : y = term10) : (int_mul x y) = (term470 x).
Proof. exact (MK_COMB (@lem3126130 x) (@lem3126129 y h1)). Qed.
Lemma lem3126132 : int_abs = int_abs.
Proof. exact (eq_refl int_abs). Qed.
Lemma lem3126133 (x : int) (y : int) (h1 : y = term10) : (term254 x y) = (term471 x).
Proof. exact (MK_COMB (@lem3126132) (@lem3126131 x y h1)). Qed.
Lemma lem3126134 (x : int) : (int_add x) = (int_add x).
Proof. exact (eq_refl (int_add x)). Qed.
Lemma lem3126135 (x : int) (y : int) (h1 : y = term10) : (term459 x y) = (term472 x).
Proof. exact (MK_COMB (@lem3126134 x) (@lem3126133 x y h1)). Qed.
Lemma lem3126136 : term473 = term473.
Proof. exact (eq_refl term473). Qed.
Lemma lem3126137 (x : int) (y : int) (h1 : y = term10) : (term462 x y) = (term474 x).
Proof. exact (MK_COMB (@lem3126136) (@lem3126135 x y h1)). Qed.
Lemma lem3126138 (x : int) (y : int) (h1 : y = term10) : (term475 x y) = (term476 x).
Proof. exact (MK_COMB (@lem3126127 x y h1) (@lem3126137 x y h1)). Qed.
Lemma lem3126141 (x : int) (y : int) (h1 : y = term10) : (term476 x) = (term475 x y).
Proof. exact (SYM (@lem3126138 x y h1)). Qed.
Lemma lem3126142 (y : int) : term477 y.
Proof. exact (@lem82 (y = term10)). Qed.
Lemma lem3126162 (y : int) (h1 : term135 y) : (y = term10) = False.
Proof. exact (@lem3126142 y (@lem3126088 y h1)). Qed.
Lemma lem3126163 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3126164 (y : int) (h1 : term135 y) : (term465 y) = (imp False).
Proof. exact (MK_COMB (@lem3126163) (@lem3126162 y h1)). Qed.
Lemma lem3126165 (x : int) : (term466 x) = (term466 x).
Proof. exact (eq_refl (term466 x)). Qed.
Lemma lem3126166 (x : int) (y : int) (h1 : term135 y) : (term457 y x) = (term478 x).
Proof. exact (MK_COMB (@lem3126164 y h1) (@lem3126165 x)). Qed.
Lemma lem3126168 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3126169 (x : int) : (term478 x) = True.
Proof. exact (@lem3126168 (term466 x)). Qed.
Lemma lem3126170 (x : int) (y : int) (h1 : term135 y) : (term457 y x) = True.
Proof. exact (TRANS (@lem3126166 x y h1) (@lem3126169 x)). Qed.
Lemma lem3126171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3126172 (x : int) (y : int) (h1 : term135 y) : (term468 y x) = (imp True).
Proof. exact (MK_COMB (@lem3126171) (@lem3126170 x y h1)). Qed.
Lemma lem3126173 (x : int) (y : int) : (term462 x y) = (term462 x y).
Proof. exact (eq_refl (term462 x y)). Qed.
Lemma lem3126174 (x : int) (y : int) (h1 : term135 y) : (term475 x y) = (term479 x y).
Proof. exact (MK_COMB (@lem3126172 x y h1) (@lem3126173 x y)). Qed.
Lemma lem3126176 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3126177 (x : int) (y : int) : (term479 x y) = (term462 x y).
Proof. exact (@lem3126176 (term462 x y)). Qed.
Lemma lem3126178 (x : int) (y : int) (h1 : term135 y) : (term475 x y) = (term462 x y).
Proof. exact (TRANS (@lem3126174 x y h1) (@lem3126177 x y)). Qed.
Lemma lem3126179 (x : int) (y : int) (h1 : term135 y) : (term462 x y) = (term475 x y).
Proof. exact (SYM (@lem3126178 x y h1)). Qed.
Lemma lem3126206 (x : int) : (term476 x) = (term480 x).
Proof. exact (@lem17265 (term466 x) (term474 x)). Qed.
Lemma lem3126208 (y : int) : (term481 y) = (term481 y).
Proof. exact (eq_refl (term481 y)). Qed.
Lemma lem3126209 (y : int) (x : int) : (term482 y x) = (term483 y x).
Proof. exact (MK_COMB (@lem3126208 y) (@lem3126206 x)). Qed.
Lemma lem3126210 (y : int) (x : int) : (term484 y x) = (term482 y x).
Proof. exact (@lem17265 (y = term10) (term476 x)). Qed.
Lemma lem3126258 (y : int) (x : int) : (term484 y x) = (term483 y x).
Proof. exact (TRANS (@lem3126210 y x) (@lem3126209 y x)). Qed.
Lemma lem3126259 (y : int) (x : int) : (term485 y x) = (term483 y x).
Proof. exact (@lem2318604 (term483 y x)). Qed.
Lemma lem3126271 (y : int) : (term486 y) = (y = term10).
Proof. exact (@lem16933 (y = term10)). Qed.
Lemma lem3126274 (x : int) : (term487 x) = (term466 x).
Proof. exact (@lem16933 (term466 x)). Qed.
Lemma lem3126275 (x : int) : (term488 x) = (term488 x).
Proof. exact (eq_refl (term488 x)). Qed.
Lemma lem3126276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3126277 (x : int) : (term489 x) = (term490 x).
Proof. exact (MK_COMB (@lem3126276) (@lem3126274 x)). Qed.
Lemma lem3126278 (x : int) : (term491 x) = (term492 x).
Proof. exact (MK_COMB (@lem3126277 x) (@lem3126275 x)). Qed.
Lemma lem3126279 (x : int) : (term493 x) = (term491 x).
Proof. exact (@lem17160 (term494 x) (term474 x)). Qed.
Lemma lem3126280 (x : int) : (term493 x) = (term492 x).
Proof. exact (TRANS (@lem3126279 x) (@lem3126278 x)). Qed.
Lemma lem3126281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3126282 (y : int) : (term495 y) = (term496 y).
Proof. exact (MK_COMB (@lem3126281) (@lem3126271 y)). Qed.
Lemma lem3126283 (y : int) (x : int) : (term497 y x) = (term498 y x).
Proof. exact (MK_COMB (@lem3126282 y) (@lem3126280 x)). Qed.
Lemma lem3126284 (y : int) (x : int) : (term499 y x) = (term497 y x).
Proof. exact (@lem17160 (term135 y) (term480 x)). Qed.
Lemma lem3126298 (y : int) (x : int) : (term499 y x) = (term498 y x).
Proof. exact (TRANS (@lem3126284 y x) (@lem3126283 y x)). Qed.
Lemma lem3126301 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3126302 (y : int) : (y = term10) = ((real_of_int y) = term295).
Proof. exact (@lem3126301 y term10). Qed.
Lemma lem3126306 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3126307 : term295 = term296.
Proof. exact (@lem3126306 (NUMERAL 0)). Qed.
Lemma lem3126308 (y : int) : (term500 y) = (term500 y).
Proof. exact (eq_refl (term500 y)). Qed.
Lemma lem3126309 (y : int) : ((real_of_int y) = term295) = ((real_of_int y) = term296).
Proof. exact (MK_COMB (@lem3126308 y) (@lem3126307)). Qed.
Lemma lem3126311 (y : int) : (y = term10) = ((real_of_int y) = term296).
Proof. exact (TRANS (@lem3126302 y) (@lem3126309 y)). Qed.
Lemma lem3126314 (x : int) (y : int) : (int_le x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3126315 (x : int) : (term466 x) = (term501 x).
Proof. exact (@lem3126314 term10 x). Qed.
Lemma lem3126317 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3126318 : term295 = term296.
Proof. exact (@lem3126317 (NUMERAL 0)). Qed.
Lemma lem3126319 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3126320 : term502 = term437.
Proof. exact (MK_COMB (@lem3126319) (@lem3126318)). Qed.
Lemma lem3126321 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3126322 (x : int) : (term501 x) = (term503 x).
Proof. exact (MK_COMB (@lem3126320) (@lem3126321 x)). Qed.
Lemma lem3126324 (x : int) : (term466 x) = (term503 x).
Proof. exact (TRANS (@lem3126315 x) (@lem3126322 x)). Qed.
Lemma lem3126326 (y : int) (x : int) : (term280 x y) = (term281 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem3126327 (x : int) : (term488 x) = (term504 x).
Proof. exact (@lem3126326 (term472 x) term10). Qed.
Lemma lem3126329 (x : int) (y : int) : (int_le x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3126330 (x : int) : (term504 x) = (term505 x).
Proof. exact (@lem3126329 (term506 x) term10). Qed.
Lemma lem3126332 (x : int) (y : int) : (term286 x y) = (term287 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3126333 (x : int) : (term507 x) = (term508 x).
Proof. exact (@lem3126332 (term472 x) term110). Qed.
Lemma lem3126335 (x : int) (y : int) : (term286 x y) = (term287 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3126336 (x : int) : (term509 x) = (term510 x).
Proof. exact (@lem3126335 x (term471 x)). Qed.
Lemma lem3126338 (x : int) : (term269 x) = (term270 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem3126339 (x : int) : (term511 x) = (term512 x).
Proof. exact (@lem3126338 (term470 x)). Qed.
Lemma lem3126341 (x : int) (y : int) : (term265 x y) = (term266 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem3126342 (x : int) : (term513 x) = (term514 x).
Proof. exact (@lem3126341 x term10). Qed.
Lemma lem3126344 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3126345 : term295 = term296.
Proof. exact (@lem3126344 (NUMERAL 0)). Qed.
Lemma lem3126346 (x : int) : (term515 x) = (term515 x).
Proof. exact (eq_refl (term515 x)). Qed.
Lemma lem3126347 (x : int) : (term514 x) = (term516 x).
Proof. exact (MK_COMB (@lem3126346 x) (@lem3126345)). Qed.
Lemma lem3126348 (x : int) : (term513 x) = (term516 x).
Proof. exact (TRANS (@lem3126342 x) (@lem3126347 x)). Qed.
Lemma lem3126349 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem3126350 (x : int) : (term512 x) = (term517 x).
Proof. exact (MK_COMB (@lem3126349) (@lem3126348 x)). Qed.
Lemma lem3126351 (x : int) : (term511 x) = (term517 x).
Proof. exact (TRANS (@lem3126339 x) (@lem3126350 x)). Qed.
Lemma lem3126352 (x : int) : (term361 x) = (term361 x).
Proof. exact (eq_refl (term361 x)). Qed.
Lemma lem3126353 (x : int) : (term510 x) = (term518 x).
Proof. exact (MK_COMB (@lem3126352 x) (@lem3126351 x)). Qed.
Lemma lem3126354 (x : int) : (term509 x) = (term518 x).
Proof. exact (TRANS (@lem3126336 x) (@lem3126353 x)). Qed.
Lemma lem3126355 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3126356 (x : int) : (term519 x) = (term520 x).
Proof. exact (MK_COMB (@lem3126355) (@lem3126354 x)). Qed.
Lemma lem3126358 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3126359 : term274 = term275.
Proof. exact (@lem3126358 term22). Qed.
Lemma lem3126360 (x : int) : (term508 x) = (term521 x).
Proof. exact (MK_COMB (@lem3126356 x) (@lem3126359)). Qed.
Lemma lem3126361 (x : int) : (term507 x) = (term521 x).
Proof. exact (TRANS (@lem3126333 x) (@lem3126360 x)). Qed.
Lemma lem3126362 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3126363 (x : int) : (term522 x) = (term523 x).
Proof. exact (MK_COMB (@lem3126362) (@lem3126361 x)). Qed.
Lemma lem3126365 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3126366 : term295 = term296.
Proof. exact (@lem3126365 (NUMERAL 0)). Qed.
Lemma lem3126367 (x : int) : (term505 x) = (term524 x).
Proof. exact (MK_COMB (@lem3126363 x) (@lem3126366)). Qed.
Lemma lem3126368 (x : int) : (term504 x) = (term524 x).
Proof. exact (TRANS (@lem3126330 x) (@lem3126367 x)). Qed.
Lemma lem3126369 (x : int) : (term488 x) = (term524 x).
Proof. exact (TRANS (@lem3126327 x) (@lem3126368 x)). Qed.
Lemma lem3126370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3126371 (x : int) : (term490 x) = (term525 x).
Proof. exact (MK_COMB (@lem3126370) (@lem3126324 x)). Qed.
Lemma lem3126372 (x : int) : (term492 x) = (term526 x).
Proof. exact (MK_COMB (@lem3126371 x) (@lem3126369 x)). Qed.
Lemma lem3126373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3126374 (y : int) : (term496 y) = (term527 y).
Proof. exact (MK_COMB (@lem3126373) (@lem3126311 y)). Qed.
Lemma lem3126375 (y : int) (x : int) : (term498 y x) = (term528 y x).
Proof. exact (MK_COMB (@lem3126374 y) (@lem3126372 x)). Qed.
Lemma lem3126376 (y : int) (x : int) : (term499 y x) = (term528 y x).
Proof. exact (TRANS (@lem3126298 y x) (@lem3126375 y x)). Qed.
Lemma lem3126380 (t : Prop) : (term301 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3126406 (y : int) (x : int) : (term529 y x) = (term528 y x).
Proof. exact (@lem3126380 (term528 y x)). Qed.
Lemma lem3126407 (y : int) : ((real_of_int y) = term296) = ((term530 y) = term296).
Proof. exact (@lem1988293 (real_of_int y) term296). Qed.
Lemma lem3126413 (y : int) : (term530 y) = (term531 y).
Proof. exact (@lem1982792 (real_of_int y) term296). Qed.
Lemma lem3126415 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3126416 : term296 = term381.
Proof. exact (@lem3126415 (NUMERAL 0)). Qed.
Lemma lem3126418 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3126419 : term321 = term329.
Proof. exact (@lem3126418 term22). Qed.
Lemma lem3126420 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3126421 : term330 = term331.
Proof. exact (MK_COMB (@lem3126420) (@lem3126419)). Qed.
Lemma lem3126422 : term532 = term533.
Proof. exact (MK_COMB (@lem3126421) (@lem3126416)). Qed.
Lemma lem3126423 : term533 = term534.
Proof. exact (@lem1981613 term321 term296 term275 term275). Qed.
Lemma lem3126425 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3126426 : term337 = term338.
Proof. exact (@lem3126425 term22 term22). Qed.
Lemma lem3126427 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3126428 : term340 = term22.
Proof. exact (EQ_MP (@lem3126427) (@lem940073)). Qed.
Lemma lem3126429 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3126430 : term338 = term275.
Proof. exact (MK_COMB (@lem3126429) (@lem3126428)). Qed.
Lemma lem3126431 : term337 = term275.
Proof. exact (TRANS (@lem3126426) (@lem3126430)). Qed.
Lemma lem3126433 (x : nat) : (term535 x) = term296.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3126434 : term532 = term296.
Proof. exact (@lem3126433 term22). Qed.
Lemma lem3126435 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3126436 : term536 = term537.
Proof. exact (MK_COMB (@lem3126435) (@lem3126434)). Qed.
Lemma lem3126437 : term534 = term381.
Proof. exact (MK_COMB (@lem3126436) (@lem3126431)). Qed.
Lemma lem3126438 : term533 = term381.
Proof. exact (TRANS (@lem3126423) (@lem3126437)). Qed.
Lemma lem3126439 : term532 = term381.
Proof. exact (TRANS (@lem3126422) (@lem3126438)). Qed.
Lemma lem3126441 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3126442 : term381 = term296.
Proof. exact (@lem3126441 term296). Qed.
Lemma lem3126443 : term532 = term296.
Proof. exact (TRANS (@lem3126439) (@lem3126442)). Qed.
Lemma lem3126444 (y : int) : (term361 y) = (term361 y).
Proof. exact (eq_refl (term361 y)). Qed.
Lemma lem3126445 (y : int) : (term531 y) = (term538 y).
Proof. exact (MK_COMB (@lem3126444 y) (@lem3126443)). Qed.
Lemma lem3126446 (y : int) : (term538 y) = (real_of_int y).
Proof. exact (@lem1982723 (real_of_int y)). Qed.
Lemma lem3126447 (y : int) : (term531 y) = (real_of_int y).
Proof. exact (TRANS (@lem3126445 y) (@lem3126446 y)). Qed.
Lemma lem3126449 (y : int) : (term530 y) = (real_of_int y).
Proof. exact (TRANS (@lem3126413 y) (@lem3126447 y)). Qed.
Lemma lem3126450 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3126451 (y : int) : (term539 y) = (term500 y).
Proof. exact (MK_COMB (@lem3126450) (@lem3126449 y)). Qed.
Lemma lem3126452 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3126453 (y : int) : ((term530 y) = term296) = ((real_of_int y) = term296).
Proof. exact (MK_COMB (@lem3126451 y) (@lem3126452)). Qed.
Lemma lem3126454 (y : int) : ((real_of_int y) = term296) = ((real_of_int y) = term296).
Proof. exact (TRANS (@lem3126407 y) (@lem3126453 y)). Qed.
Lemma lem3126455 (x : int) : (term503 x) = (term540 x).
Proof. exact (@lem1988287 (real_of_int x) term296). Qed.
Lemma lem3126461 (x : int) : (term530 x) = (term531 x).
Proof. exact (@lem1982792 (real_of_int x) term296). Qed.
Lemma lem3126463 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3126464 : term296 = term381.
Proof. exact (@lem3126463 (NUMERAL 0)). Qed.
Lemma lem3126466 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3126467 : term321 = term329.
Proof. exact (@lem3126466 term22). Qed.
Lemma lem3126468 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3126469 : term330 = term331.
Proof. exact (MK_COMB (@lem3126468) (@lem3126467)). Qed.
Lemma lem3126470 : term532 = term533.
Proof. exact (MK_COMB (@lem3126469) (@lem3126464)). Qed.
Lemma lem3126471 : term533 = term534.
Proof. exact (@lem1981613 term321 term296 term275 term275). Qed.
Lemma lem3126473 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3126474 : term337 = term338.
Proof. exact (@lem3126473 term22 term22). Qed.
Lemma lem3126475 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3126476 : term340 = term22.
Proof. exact (EQ_MP (@lem3126475) (@lem940073)). Qed.
Lemma lem3126477 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3126478 : term338 = term275.
Proof. exact (MK_COMB (@lem3126477) (@lem3126476)). Qed.
Lemma lem3126479 : term337 = term275.
Proof. exact (TRANS (@lem3126474) (@lem3126478)). Qed.
Lemma lem3126481 (x : nat) : (term535 x) = term296.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3126482 : term532 = term296.
Proof. exact (@lem3126481 term22). Qed.
Lemma lem3126483 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3126484 : term536 = term537.
Proof. exact (MK_COMB (@lem3126483) (@lem3126482)). Qed.
Lemma lem3126485 : term534 = term381.
Proof. exact (MK_COMB (@lem3126484) (@lem3126479)). Qed.
Lemma lem3126486 : term533 = term381.
Proof. exact (TRANS (@lem3126471) (@lem3126485)). Qed.
Lemma lem3126487 : term532 = term381.
Proof. exact (TRANS (@lem3126470) (@lem3126486)). Qed.
Lemma lem3126489 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3126490 : term381 = term296.
Proof. exact (@lem3126489 term296). Qed.
Lemma lem3126491 : term532 = term296.
Proof. exact (TRANS (@lem3126487) (@lem3126490)). Qed.
Lemma lem3126492 (x : int) : (term361 x) = (term361 x).
Proof. exact (eq_refl (term361 x)). Qed.
Lemma lem3126493 (x : int) : (term531 x) = (term538 x).
Proof. exact (MK_COMB (@lem3126492 x) (@lem3126491)). Qed.
Lemma lem3126494 (x : int) : (term538 x) = (real_of_int x).
Proof. exact (@lem1982723 (real_of_int x)). Qed.
Lemma lem3126495 (x : int) : (term531 x) = (real_of_int x).
Proof. exact (TRANS (@lem3126493 x) (@lem3126494 x)). Qed.
Lemma lem3126497 (x : int) : (term530 x) = (real_of_int x).
Proof. exact (TRANS (@lem3126461 x) (@lem3126495 x)). Qed.
Lemma lem3126498 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3126499 (x : int) : (term541 x) = (term542 x).
Proof. exact (MK_COMB (@lem3126498) (@lem3126497 x)). Qed.
Lemma lem3126500 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3126501 (x : int) : (term540 x) = (term543 x).
Proof. exact (MK_COMB (@lem3126499 x) (@lem3126500)). Qed.
Lemma lem3126502 (x : int) : (term503 x) = (term543 x).
Proof. exact (TRANS (@lem3126455 x) (@lem3126501 x)). Qed.
Lemma lem3126503 (x : int) : (term524 x) = (term544 x).
Proof. exact (@lem1988287 term296 (term521 x)). Qed.
Lemma lem3126504 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem3126511 (x : int) : (term516 x) = term296.
Proof. exact (@lem1982731 (real_of_int x)). Qed.
Lemma lem3126512 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem3126513 (x : int) : (term517 x) = term545.
Proof. exact (MK_COMB (@lem3126512) (@lem3126511 x)). Qed.
Lemma lem3126516 (x : int) : (term361 x) = (term361 x).
Proof. exact (eq_refl (term361 x)). Qed.
Lemma lem3126517 (x : int) : (term518 x) = (term546 x).
Proof. exact (MK_COMB (@lem3126516 x) (@lem3126513 x)). Qed.
Lemma lem3126518 (x : int) : (term546 x) = (term547 x).
Proof. exact (@lem1982761 term545 (real_of_int x)). Qed.
Lemma lem3126519 (x : int) : (term518 x) = (term547 x).
Proof. exact (TRANS (@lem3126517 x) (@lem3126518 x)). Qed.
Lemma lem3126520 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3126521 (x : int) : (term520 x) = (term548 x).
Proof. exact (MK_COMB (@lem3126520) (@lem3126519 x)). Qed.
Lemma lem3126522 (x : int) : (term521 x) = (term549 x).
Proof. exact (MK_COMB (@lem3126521 x) (@lem3126504)). Qed.
Lemma lem3126527 (x : int) : (term549 x) = (term550 x).
Proof. exact (@lem1982755 term545 (real_of_int x) term275). Qed.
Lemma lem3126528 (x : int) : (term521 x) = (term550 x).
Proof. exact (TRANS (@lem3126522 x) (@lem3126527 x)). Qed.
Lemma lem3126531 : term315 = term315.
Proof. exact (eq_refl term315). Qed.
Lemma lem3126532 (x : int) : (term551 x) = (term552 x).
Proof. exact (MK_COMB (@lem3126531) (@lem3126528 x)). Qed.
Lemma lem3126533 (x : int) : (term552 x) = (term553 x).
Proof. exact (@lem1982792 term296 (term550 x)). Qed.
Lemma lem3126534 (x : int) : (term554 x) = (term555 x).
Proof. exact (@lem1982781 term545 term321 (term322 x)). Qed.
Lemma lem3126535 (x : int) : (term323 x) = (term324 x).
Proof. exact (@lem1982781 (real_of_int x) term321 term275). Qed.
Lemma lem3126537 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3126538 : term275 = term326.
Proof. exact (@lem3126537 term22). Qed.
Lemma lem3126540 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3126541 : term321 = term329.
Proof. exact (@lem3126540 term22). Qed.
Lemma lem3126542 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3126543 : term330 = term331.
Proof. exact (MK_COMB (@lem3126542) (@lem3126541)). Qed.
Lemma lem3126544 : term332 = term333.
Proof. exact (MK_COMB (@lem3126543) (@lem3126538)). Qed.
Lemma lem3126545 : term333 = term334.
Proof. exact (@lem1981613 term321 term275 term275 term275). Qed.
Lemma lem3126547 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3126548 : term337 = term338.
Proof. exact (@lem3126547 term22 term22). Qed.
Lemma lem3126549 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3126550 : term340 = term22.
Proof. exact (EQ_MP (@lem3126549) (@lem940073)). Qed.
Lemma lem3126551 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3126552 : term338 = term275.
Proof. exact (MK_COMB (@lem3126551) (@lem3126550)). Qed.
Lemma lem3126553 : term337 = term275.
Proof. exact (TRANS (@lem3126548) (@lem3126552)). Qed.
Lemma lem3126555 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3126556 : term332 = term343.
Proof. exact (@lem3126555 term22 term22). Qed.
Lemma lem3126557 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3126558 : term340 = term22.
Proof. exact (EQ_MP (@lem3126557) (@lem940073)). Qed.
Lemma lem3126559 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3126560 : term338 = term275.
Proof. exact (MK_COMB (@lem3126559) (@lem3126558)). Qed.
Lemma lem3126561 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3126562 : term343 = term321.
Proof. exact (MK_COMB (@lem3126561) (@lem3126560)). Qed.
Lemma lem3126563 : term332 = term321.
Proof. exact (TRANS (@lem3126556) (@lem3126562)). Qed.
Lemma lem3126564 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3126565 : term344 = term345.
Proof. exact (MK_COMB (@lem3126564) (@lem3126563)). Qed.
Lemma lem3126566 : term334 = term329.
Proof. exact (MK_COMB (@lem3126565) (@lem3126553)). Qed.
Lemma lem3126567 : term333 = term329.
Proof. exact (TRANS (@lem3126545) (@lem3126566)). Qed.
Lemma lem3126568 : term332 = term329.
Proof. exact (TRANS (@lem3126544) (@lem3126567)). Qed.
Lemma lem3126570 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3126571 : term329 = term321.
Proof. exact (@lem3126570 term321). Qed.
Lemma lem3126572 : term332 = term321.
Proof. exact (TRANS (@lem3126568) (@lem3126571)). Qed.
Lemma lem3126575 (x : int) : (term347 x) = (term347 x).
Proof. exact (eq_refl (term347 x)). Qed.
Lemma lem3126576 (x : int) : (term324 x) = (term348 x).
Proof. exact (MK_COMB (@lem3126575 x) (@lem3126572)). Qed.
Lemma lem3126577 (x : int) : (term323 x) = (term348 x).
Proof. exact (TRANS (@lem3126535 x) (@lem3126576 x)). Qed.
Lemma lem3126580 : term556 = term556.
Proof. exact (eq_refl term556). Qed.
Lemma lem3126581 (x : int) : (term555 x) = (term557 x).
Proof. exact (MK_COMB (@lem3126580) (@lem3126577 x)). Qed.
Lemma lem3126582 (x : int) : (term554 x) = (term557 x).
Proof. exact (TRANS (@lem3126534 x) (@lem3126581 x)). Qed.
Lemma lem3126583 : term350 = term350.
Proof. exact (eq_refl term350). Qed.
Lemma lem3126584 (x : int) : (term553 x) = (term558 x).
Proof. exact (MK_COMB (@lem3126583) (@lem3126582 x)). Qed.
Lemma lem3126585 (x : int) : (term558 x) = (term557 x).
Proof. exact (@lem1982721 (term557 x)). Qed.
Lemma lem3126586 (x : int) : (term553 x) = (term557 x).
Proof. exact (TRANS (@lem3126584 x) (@lem3126585 x)). Qed.
Lemma lem3126587 (x : int) : (term552 x) = (term557 x).
Proof. exact (TRANS (@lem3126533 x) (@lem3126586 x)). Qed.
Lemma lem3126588 (x : int) : (term551 x) = (term557 x).
Proof. exact (TRANS (@lem3126532 x) (@lem3126587 x)). Qed.
Lemma lem3126589 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3126590 (x : int) : (term559 x) = (term560 x).
Proof. exact (MK_COMB (@lem3126589) (@lem3126588 x)). Qed.
Lemma lem3126591 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3126592 (x : int) : (term544 x) = (term561 x).
Proof. exact (MK_COMB (@lem3126590 x) (@lem3126591)). Qed.
Lemma lem3126593 (x : int) : (term524 x) = (term561 x).
Proof. exact (TRANS (@lem3126503 x) (@lem3126592 x)). Qed.
Lemma lem3126594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3126595 (x : int) : (term525 x) = (term562 x).
Proof. exact (MK_COMB (@lem3126594) (@lem3126502 x)). Qed.
Lemma lem3126596 (x : int) : (term526 x) = (term563 x).
Proof. exact (MK_COMB (@lem3126595 x) (@lem3126593 x)). Qed.
Lemma lem3126597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3126598 (y : int) : (term527 y) = (term527 y).
Proof. exact (MK_COMB (@lem3126597) (@lem3126454 y)). Qed.
Lemma lem3126599 (y : int) (x : int) : (term528 y x) = (term564 y x).
Proof. exact (MK_COMB (@lem3126598 y) (@lem3126596 x)). Qed.
Lemma lem3126620 (y : int) (x : int) : (term529 y x) = (term564 y x).
Proof. exact (TRANS (@lem3126406 y x) (@lem3126599 y x)). Qed.
Lemma lem3126622 (a : real) (x : real) (r : real) : (term357 x a r) = (term358 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem3126623 (x : int) : (term561 x) = (term565 x).
Proof. exact (@lem3126622 (term348 x) term296 term296). Qed.
Lemma lem3126630 : term566 = term296.
Proof. exact (@lem1982731 term275). Qed.
Lemma lem3126645 (x : int) : (term567 x) = (term567 x).
Proof. exact (eq_refl (term567 x)). Qed.
Lemma lem3126646 (x : int) : (term568 x) = (term569 x).
Proof. exact (MK_COMB (@lem3126645 x) (@lem3126630)). Qed.
Lemma lem3126647 (x : int) : (term569 x) = (term348 x).
Proof. exact (@lem1982723 (term348 x)). Qed.
Lemma lem3126648 (x : int) : (term568 x) = (term348 x).
Proof. exact (TRANS (@lem3126646 x) (@lem3126647 x)). Qed.
Lemma lem3126649 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3126650 (x : int) : (term570 x) = (term571 x).
Proof. exact (MK_COMB (@lem3126649) (@lem3126648 x)). Qed.
Lemma lem3126651 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3126652 (x : int) : (term572 x) = (term573 x).
Proof. exact (MK_COMB (@lem3126650 x) (@lem3126651)). Qed.
Lemma lem3126659 : term532 = term296.
Proof. exact (@lem1982731 term321). Qed.
Lemma lem3126674 (x : int) : (term567 x) = (term567 x).
Proof. exact (eq_refl (term567 x)). Qed.
Lemma lem3126675 (x : int) : (term574 x) = (term569 x).
Proof. exact (MK_COMB (@lem3126674 x) (@lem3126659)). Qed.
Lemma lem3126676 (x : int) : (term569 x) = (term348 x).
Proof. exact (@lem1982723 (term348 x)). Qed.
Lemma lem3126677 (x : int) : (term574 x) = (term348 x).
Proof. exact (TRANS (@lem3126675 x) (@lem3126676 x)). Qed.
Lemma lem3126678 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3126679 (x : int) : (term575 x) = (term571 x).
Proof. exact (MK_COMB (@lem3126678) (@lem3126677 x)). Qed.
Lemma lem3126680 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3126681 (x : int) : (term576 x) = (term573 x).
Proof. exact (MK_COMB (@lem3126679 x) (@lem3126680)). Qed.
Lemma lem3126682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3126683 (x : int) : (term577 x) = (term578 x).
Proof. exact (MK_COMB (@lem3126682) (@lem3126681 x)). Qed.
Lemma lem3126684 (x : int) : (term565 x) = (term579 x).
Proof. exact (MK_COMB (@lem3126683 x) (@lem3126652 x)). Qed.
Lemma lem3126685 (x : int) : (term561 x) = (term579 x).
Proof. exact (TRANS (@lem3126623 x) (@lem3126684 x)). Qed.
Lemma lem3126686 (x : int) : (term562 x) = (term562 x).
Proof. exact (eq_refl (term562 x)). Qed.
Lemma lem3126687 (x : int) : (term563 x) = (term580 x).
Proof. exact (MK_COMB (@lem3126686 x) (@lem3126685 x)). Qed.
Lemma lem3126688 (y : int) : (term527 y) = (term527 y).
Proof. exact (eq_refl (term527 y)). Qed.
Lemma lem3126691 (y : int) (x : int) : (term564 y x) = (term581 y x).
Proof. exact (MK_COMB (@lem3126688 y) (@lem3126687 x)). Qed.
Lemma lem3126692 (y : int) (x : int) (h1 : term581 y x) : term581 y x.
Proof. exact (h1). Qed.
Lemma lem3126693 (y : int) (x : int) (h1 : term581 y x) : term580 x.
Proof. exact (proj2 (@lem3126692 y x h1)). Qed.
Lemma lem3126695 (y : int) (x : int) (h1 : term581 y x) : term579 x.
Proof. exact (proj2 (@lem3126693 y x h1)). Qed.
Lemma lem3126696 (y : int) (x : int) (h1 : term581 y x) : term543 x.
Proof. exact (proj1 (@lem3126693 y x h1)). Qed.
Lemma lem3126697 (y : int) (x : int) (h1 : term581 y x) : term573 x.
Proof. exact (proj2 (@lem3126695 y x h1)). Qed.
Lemma lem3126700 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3126701 : term379 = term380.
Proof. exact (@lem3126700 term296 term275). Qed.
Lemma lem3126703 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3126704 : term275 = term326.
Proof. exact (@lem3126703 term22). Qed.
Lemma lem3126706 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3126707 : term296 = term381.
Proof. exact (@lem3126706 (NUMERAL 0)). Qed.
Lemma lem3126708 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3126709 : term382 = term383.
Proof. exact (MK_COMB (@lem3126708) (@lem3126707)). Qed.
Lemma lem3126710 : term380 = term384.
Proof. exact (MK_COMB (@lem3126709) (@lem3126704)). Qed.
Lemma lem3126711 : term385.
Proof. exact (@lem1980255 term296 term275 term275 term275). Qed.
Lemma lem3126713 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126714 : term380 = term387.
Proof. exact (@lem3126713 (NUMERAL 0) term22). Qed.
Lemma lem3126715 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126716 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3126717 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126716 h1) (fun h1 : term387 = True => @lem3126715)). Qed.
Lemma lem3126718 : term387 = True.
Proof. exact (EQ_MP (@lem3126717) (@lem3126715)). Qed.
Lemma lem3126719 : term380 = True.
Proof. exact (TRANS (@lem3126714) (@lem3126718)). Qed.
Lemma lem3126720 : True = term380.
Proof. exact (SYM (@lem3126719)). Qed.
Lemma lem3126721 : term380.
Proof. exact (EQ_MP (@lem3126720) (@lem0)). Qed.
Lemma lem3126722 : term388.
Proof. exact (@lem3126711 (@lem3126721)). Qed.
Lemma lem3126724 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126725 : term380 = term387.
Proof. exact (@lem3126724 (NUMERAL 0) term22). Qed.
Lemma lem3126726 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126727 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3126728 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126727 h1) (fun h1 : term387 = True => @lem3126726)). Qed.
Lemma lem3126729 : term387 = True.
Proof. exact (EQ_MP (@lem3126728) (@lem3126726)). Qed.
Lemma lem3126730 : term380 = True.
Proof. exact (TRANS (@lem3126725) (@lem3126729)). Qed.
Lemma lem3126731 : True = term380.
Proof. exact (SYM (@lem3126730)). Qed.
Lemma lem3126732 : term380.
Proof. exact (EQ_MP (@lem3126731) (@lem0)). Qed.
Lemma lem3126733 : term384 = term389.
Proof. exact (@lem3126722 (@lem3126732)). Qed.
Lemma lem3126735 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3126736 : term337 = term338.
Proof. exact (@lem3126735 term22 term22). Qed.
Lemma lem3126737 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3126738 : term340 = term22.
Proof. exact (EQ_MP (@lem3126737) (@lem940073)). Qed.
Lemma lem3126739 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3126740 : term338 = term275.
Proof. exact (MK_COMB (@lem3126739) (@lem3126738)). Qed.
Lemma lem3126741 : term337 = term275.
Proof. exact (TRANS (@lem3126736) (@lem3126740)). Qed.
Lemma lem3126743 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3126744 : term391 = term296.
Proof. exact (@lem3126743 term22). Qed.
Lemma lem3126745 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3126746 : term392 = term382.
Proof. exact (MK_COMB (@lem3126745) (@lem3126744)). Qed.
Lemma lem3126747 : term389 = term380.
Proof. exact (MK_COMB (@lem3126746) (@lem3126741)). Qed.
Lemma lem3126749 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126750 : term380 = term387.
Proof. exact (@lem3126749 (NUMERAL 0) term22). Qed.
Lemma lem3126751 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126752 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3126753 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126752 h1) (fun h1 : term387 = True => @lem3126751)). Qed.
Lemma lem3126754 : term387 = True.
Proof. exact (EQ_MP (@lem3126753) (@lem3126751)). Qed.
Lemma lem3126755 : term380 = True.
Proof. exact (TRANS (@lem3126750) (@lem3126754)). Qed.
Lemma lem3126756 : term389 = True.
Proof. exact (TRANS (@lem3126747) (@lem3126755)). Qed.
Lemma lem3126757 : term384 = True.
Proof. exact (TRANS (@lem3126733) (@lem3126756)). Qed.
Lemma lem3126758 : term380 = True.
Proof. exact (TRANS (@lem3126710) (@lem3126757)). Qed.
Lemma lem3126759 : term379 = True.
Proof. exact (TRANS (@lem3126701) (@lem3126758)). Qed.
Lemma lem3126760 : True = term379.
Proof. exact (SYM (@lem3126759)). Qed.
Lemma lem3126761 : term379.
Proof. exact (EQ_MP (@lem3126760) (@lem0)). Qed.
Lemma lem3126762 (y : int) (x : int) (h1 : term581 y x) : term582 x.
Proof. exact (conj (@lem3126761) (@lem3126696 y x h1)). Qed.
Lemma lem3126764 (x : real) (y : real) : term394 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3126765 (x : int) : term583 x.
Proof. exact (@lem3126764 term275 (real_of_int x)). Qed.
Lemma lem3126766 (y : int) (x : int) (h1 : term581 y x) : term584 x.
Proof. exact (@lem3126765 x (@lem3126762 y x h1)). Qed.
Lemma lem3126767 (x : int) : (term360 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem3126768 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3126769 (x : int) : (term585 x) = (term542 x).
Proof. exact (MK_COMB (@lem3126768) (@lem3126767 x)). Qed.
Lemma lem3126770 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3126771 (x : int) : (term584 x) = (term543 x).
Proof. exact (MK_COMB (@lem3126769 x) (@lem3126770)). Qed.
Lemma lem3126772 (y : int) (x : int) (h1 : term581 y x) : term543 x.
Proof. exact (EQ_MP (@lem3126771 x) (@lem3126766 y x h1)). Qed.
Lemma lem3126774 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3126775 : term379 = term380.
Proof. exact (@lem3126774 term296 term275). Qed.
Lemma lem3126777 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3126778 : term275 = term326.
Proof. exact (@lem3126777 term22). Qed.
Lemma lem3126780 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3126781 : term296 = term381.
Proof. exact (@lem3126780 (NUMERAL 0)). Qed.
Lemma lem3126782 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3126783 : term382 = term383.
Proof. exact (MK_COMB (@lem3126782) (@lem3126781)). Qed.
Lemma lem3126784 : term380 = term384.
Proof. exact (MK_COMB (@lem3126783) (@lem3126778)). Qed.
Lemma lem3126785 : term385.
Proof. exact (@lem1980255 term296 term275 term275 term275). Qed.
Lemma lem3126787 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126788 : term380 = term387.
Proof. exact (@lem3126787 (NUMERAL 0) term22). Qed.
Lemma lem3126789 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126790 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3126791 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126790 h1) (fun h1 : term387 = True => @lem3126789)). Qed.
Lemma lem3126792 : term387 = True.
Proof. exact (EQ_MP (@lem3126791) (@lem3126789)). Qed.
Lemma lem3126793 : term380 = True.
Proof. exact (TRANS (@lem3126788) (@lem3126792)). Qed.
Lemma lem3126794 : True = term380.
Proof. exact (SYM (@lem3126793)). Qed.
Lemma lem3126795 : term380.
Proof. exact (EQ_MP (@lem3126794) (@lem0)). Qed.
Lemma lem3126796 : term388.
Proof. exact (@lem3126785 (@lem3126795)). Qed.
Lemma lem3126798 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126799 : term380 = term387.
Proof. exact (@lem3126798 (NUMERAL 0) term22). Qed.
Lemma lem3126800 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126801 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3126802 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126801 h1) (fun h1 : term387 = True => @lem3126800)). Qed.
Lemma lem3126803 : term387 = True.
Proof. exact (EQ_MP (@lem3126802) (@lem3126800)). Qed.
Lemma lem3126804 : term380 = True.
Proof. exact (TRANS (@lem3126799) (@lem3126803)). Qed.
Lemma lem3126805 : True = term380.
Proof. exact (SYM (@lem3126804)). Qed.
Lemma lem3126806 : term380.
Proof. exact (EQ_MP (@lem3126805) (@lem0)). Qed.
Lemma lem3126807 : term384 = term389.
Proof. exact (@lem3126796 (@lem3126806)). Qed.
Lemma lem3126809 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3126810 : term337 = term338.
Proof. exact (@lem3126809 term22 term22). Qed.
Lemma lem3126811 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3126812 : term340 = term22.
Proof. exact (EQ_MP (@lem3126811) (@lem940073)). Qed.
Lemma lem3126813 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3126814 : term338 = term275.
Proof. exact (MK_COMB (@lem3126813) (@lem3126812)). Qed.
Lemma lem3126815 : term337 = term275.
Proof. exact (TRANS (@lem3126810) (@lem3126814)). Qed.
Lemma lem3126817 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3126818 : term391 = term296.
Proof. exact (@lem3126817 term22). Qed.
Lemma lem3126819 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3126820 : term392 = term382.
Proof. exact (MK_COMB (@lem3126819) (@lem3126818)). Qed.
Lemma lem3126821 : term389 = term380.
Proof. exact (MK_COMB (@lem3126820) (@lem3126815)). Qed.
Lemma lem3126823 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126824 : term380 = term387.
Proof. exact (@lem3126823 (NUMERAL 0) term22). Qed.
Lemma lem3126825 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126826 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3126827 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126826 h1) (fun h1 : term387 = True => @lem3126825)). Qed.
Lemma lem3126828 : term387 = True.
Proof. exact (EQ_MP (@lem3126827) (@lem3126825)). Qed.
Lemma lem3126829 : term380 = True.
Proof. exact (TRANS (@lem3126824) (@lem3126828)). Qed.
Lemma lem3126830 : term389 = True.
Proof. exact (TRANS (@lem3126821) (@lem3126829)). Qed.
Lemma lem3126831 : term384 = True.
Proof. exact (TRANS (@lem3126807) (@lem3126830)). Qed.
Lemma lem3126832 : term380 = True.
Proof. exact (TRANS (@lem3126784) (@lem3126831)). Qed.
Lemma lem3126833 : term379 = True.
Proof. exact (TRANS (@lem3126775) (@lem3126832)). Qed.
Lemma lem3126834 : True = term379.
Proof. exact (SYM (@lem3126833)). Qed.
Lemma lem3126835 : term379.
Proof. exact (EQ_MP (@lem3126834) (@lem0)). Qed.
Lemma lem3126836 (y : int) (x : int) (h1 : term581 y x) : term586 x.
Proof. exact (conj (@lem3126835) (@lem3126697 y x h1)). Qed.
Lemma lem3126838 (x : real) (y : real) : term394 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3126839 (x : int) : term587 x.
Proof. exact (@lem3126838 term275 (term348 x)). Qed.
Lemma lem3126840 (y : int) (x : int) (h1 : term581 y x) : term588 x.
Proof. exact (@lem3126839 x (@lem3126836 y x h1)). Qed.
Lemma lem3126841 (x : int) : (term589 x) = (term348 x).
Proof. exact (@lem1982733 (term348 x)). Qed.
Lemma lem3126842 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3126843 (x : int) : (term590 x) = (term571 x).
Proof. exact (MK_COMB (@lem3126842) (@lem3126841 x)). Qed.
Lemma lem3126844 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3126845 (x : int) : (term588 x) = (term573 x).
Proof. exact (MK_COMB (@lem3126843 x) (@lem3126844)). Qed.
Lemma lem3126846 (y : int) (x : int) (h1 : term581 y x) : term573 x.
Proof. exact (EQ_MP (@lem3126845 x) (@lem3126840 y x h1)). Qed.
Lemma lem3126847 (y : int) (x : int) (h1 : term581 y x) : term591 x.
Proof. exact (conj (@lem3126846 y x h1) (@lem3126772 y x h1)). Qed.
Lemma lem3126849 (x : real) (y : real) : term405 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3126850 (x : int) : term592 x.
Proof. exact (@lem3126849 (term348 x) (real_of_int x)). Qed.
Lemma lem3126851 (y : int) (x : int) (h1 : term581 y x) : term593 x.
Proof. exact (@lem3126850 x (@lem3126847 y x h1)). Qed.
Lemma lem3126852 (x : int) : (term430 x) = (term431 x).
Proof. exact (@lem1982759 (term369 x) (real_of_int x) term321). Qed.
Lemma lem3126853 (x : int) : (term410 x) = (term411 x).
Proof. exact (@lem1982713 term321 (real_of_int x)). Qed.
Lemma lem3126855 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3126856 : term275 = term326.
Proof. exact (@lem3126855 term22). Qed.
Lemma lem3126858 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3126859 : term321 = term329.
Proof. exact (@lem3126858 term22). Qed.
Lemma lem3126860 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3126861 : term412 = term413.
Proof. exact (MK_COMB (@lem3126860) (@lem3126859)). Qed.
Lemma lem3126862 : term414 = term415.
Proof. exact (MK_COMB (@lem3126861) (@lem3126856)). Qed.
Lemma lem3126863 : term416.
Proof. exact (@lem1981473 term321 term275 term275 term275 term296 term275). Qed.
Lemma lem3126865 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126866 : term380 = term387.
Proof. exact (@lem3126865 (NUMERAL 0) term22). Qed.
Lemma lem3126867 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126868 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3126869 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126868 h1) (fun h1 : term387 = True => @lem3126867)). Qed.
Lemma lem3126870 : term387 = True.
Proof. exact (EQ_MP (@lem3126869) (@lem3126867)). Qed.
Lemma lem3126871 : term380 = True.
Proof. exact (TRANS (@lem3126866) (@lem3126870)). Qed.
Lemma lem3126872 : True = term380.
Proof. exact (SYM (@lem3126871)). Qed.
Lemma lem3126873 : term380.
Proof. exact (EQ_MP (@lem3126872) (@lem0)). Qed.
Lemma lem3126874 : term417.
Proof. exact (@lem3126863 (@lem3126873)). Qed.
Lemma lem3126876 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126877 : term380 = term387.
Proof. exact (@lem3126876 (NUMERAL 0) term22). Qed.
Lemma lem3126878 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126879 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3126880 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126879 h1) (fun h1 : term387 = True => @lem3126878)). Qed.
Lemma lem3126881 : term387 = True.
Proof. exact (EQ_MP (@lem3126880) (@lem3126878)). Qed.
Lemma lem3126882 : term380 = True.
Proof. exact (TRANS (@lem3126877) (@lem3126881)). Qed.
Lemma lem3126883 : True = term380.
Proof. exact (SYM (@lem3126882)). Qed.
Lemma lem3126884 : term380.
Proof. exact (EQ_MP (@lem3126883) (@lem0)). Qed.
Lemma lem3126885 : term418.
Proof. exact (@lem3126874 (@lem3126884)). Qed.
Lemma lem3126887 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126888 : term380 = term387.
Proof. exact (@lem3126887 (NUMERAL 0) term22). Qed.
Lemma lem3126889 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126890 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3126891 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126890 h1) (fun h1 : term387 = True => @lem3126889)). Qed.
Lemma lem3126892 : term387 = True.
Proof. exact (EQ_MP (@lem3126891) (@lem3126889)). Qed.
Lemma lem3126893 : term380 = True.
Proof. exact (TRANS (@lem3126888) (@lem3126892)). Qed.
Lemma lem3126894 : True = term380.
Proof. exact (SYM (@lem3126893)). Qed.
Lemma lem3126895 : term380.
Proof. exact (EQ_MP (@lem3126894) (@lem0)). Qed.
Lemma lem3126896 : term419.
Proof. exact (@lem3126885 (@lem3126895)). Qed.
Lemma lem3126898 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3126899 : term337 = term338.
Proof. exact (@lem3126898 term22 term22). Qed.
Lemma lem3126900 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3126901 : term340 = term22.
Proof. exact (EQ_MP (@lem3126900) (@lem940073)). Qed.
Lemma lem3126902 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3126903 : term338 = term275.
Proof. exact (MK_COMB (@lem3126902) (@lem3126901)). Qed.
Lemma lem3126904 : term337 = term275.
Proof. exact (TRANS (@lem3126899) (@lem3126903)). Qed.
Lemma lem3126906 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3126907 : term332 = term343.
Proof. exact (@lem3126906 term22 term22). Qed.
Lemma lem3126908 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3126909 : term340 = term22.
Proof. exact (EQ_MP (@lem3126908) (@lem940073)). Qed.
Lemma lem3126910 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3126911 : term338 = term275.
Proof. exact (MK_COMB (@lem3126910) (@lem3126909)). Qed.
Lemma lem3126912 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3126913 : term343 = term321.
Proof. exact (MK_COMB (@lem3126912) (@lem3126911)). Qed.
Lemma lem3126914 : term332 = term321.
Proof. exact (TRANS (@lem3126907) (@lem3126913)). Qed.
Lemma lem3126915 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3126916 : term420 = term412.
Proof. exact (MK_COMB (@lem3126915) (@lem3126914)). Qed.
Lemma lem3126917 : term421 = term414.
Proof. exact (MK_COMB (@lem3126916) (@lem3126904)). Qed.
Lemma lem3126919 (m : nat) : (term422 m) = term296.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3126920 : term414 = term296.
Proof. exact (@lem3126919 term22). Qed.
Lemma lem3126921 : term421 = term296.
Proof. exact (TRANS (@lem3126917) (@lem3126920)). Qed.
Lemma lem3126922 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3126923 : term423 = term424.
Proof. exact (MK_COMB (@lem3126922) (@lem3126921)). Qed.
Lemma lem3126924 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem3126925 : term425 = term391.
Proof. exact (MK_COMB (@lem3126923) (@lem3126924)). Qed.
Lemma lem3126927 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3126928 : term391 = term296.
Proof. exact (@lem3126927 term22). Qed.
Lemma lem3126929 : term425 = term296.
Proof. exact (TRANS (@lem3126925) (@lem3126928)). Qed.
Lemma lem3126931 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3126932 : term337 = term338.
Proof. exact (@lem3126931 term22 term22). Qed.
Lemma lem3126933 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3126934 : term340 = term22.
Proof. exact (EQ_MP (@lem3126933) (@lem940073)). Qed.
Lemma lem3126935 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3126936 : term338 = term275.
Proof. exact (MK_COMB (@lem3126935) (@lem3126934)). Qed.
Lemma lem3126937 : term337 = term275.
Proof. exact (TRANS (@lem3126932) (@lem3126936)). Qed.
Lemma lem3126938 : term424 = term424.
Proof. exact (eq_refl term424). Qed.
Lemma lem3126939 : term426 = term391.
Proof. exact (MK_COMB (@lem3126938) (@lem3126937)). Qed.
Lemma lem3126941 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3126942 : term391 = term296.
Proof. exact (@lem3126941 term22). Qed.
Lemma lem3126943 : term426 = term296.
Proof. exact (TRANS (@lem3126939) (@lem3126942)). Qed.
Lemma lem3126944 : term296 = term426.
Proof. exact (SYM (@lem3126943)). Qed.
Lemma lem3126945 : term425 = term426.
Proof. exact (TRANS (@lem3126929) (@lem3126944)). Qed.
Lemma lem3126946 : term415 = term381.
Proof. exact (@lem3126896 (@lem3126945)). Qed.
Lemma lem3126947 : term414 = term381.
Proof. exact (TRANS (@lem3126862) (@lem3126946)). Qed.
Lemma lem3126949 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3126950 : term381 = term296.
Proof. exact (@lem3126949 term296). Qed.
Lemma lem3126951 : term414 = term296.
Proof. exact (TRANS (@lem3126947) (@lem3126950)). Qed.
Lemma lem3126952 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3126953 : term427 = term424.
Proof. exact (MK_COMB (@lem3126952) (@lem3126951)). Qed.
Lemma lem3126954 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3126955 (x : int) : (term411 x) = (term428 x).
Proof. exact (MK_COMB (@lem3126953) (@lem3126954 x)). Qed.
Lemma lem3126956 (x : int) : (term410 x) = (term428 x).
Proof. exact (TRANS (@lem3126853 x) (@lem3126955 x)). Qed.
Lemma lem3126957 (x : int) : (term428 x) = term296.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem3126958 (x : int) : (term410 x) = term296.
Proof. exact (TRANS (@lem3126956 x) (@lem3126957 x)). Qed.
Lemma lem3126959 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3126960 (x : int) : (term429 x) = term350.
Proof. exact (MK_COMB (@lem3126959) (@lem3126958 x)). Qed.
Lemma lem3126961 : term321 = term321.
Proof. exact (eq_refl term321). Qed.
Lemma lem3126962 (x : int) : (term431 x) = term432.
Proof. exact (MK_COMB (@lem3126960 x) (@lem3126961)). Qed.
Lemma lem3126963 (x : int) : (term430 x) = term432.
Proof. exact (TRANS (@lem3126852 x) (@lem3126962 x)). Qed.
Lemma lem3126964 : term432 = term321.
Proof. exact (@lem1982721 term321). Qed.
Lemma lem3126965 (x : int) : (term430 x) = term321.
Proof. exact (TRANS (@lem3126963 x) (@lem3126964)). Qed.
Lemma lem3126966 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3126967 (x : int) : (term594 x) = term434.
Proof. exact (MK_COMB (@lem3126966) (@lem3126965 x)). Qed.
Lemma lem3126968 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3126969 (x : int) : (term593 x) = term435.
Proof. exact (MK_COMB (@lem3126967 x) (@lem3126968)). Qed.
Lemma lem3126970 (y : int) (x : int) (h1 : term581 y x) : term435.
Proof. exact (EQ_MP (@lem3126969 x) (@lem3126851 y x h1)). Qed.
Lemma lem3126972 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3126973 : term435 = term436.
Proof. exact (@lem3126972 term296 term321). Qed.
Lemma lem3126975 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3126976 : term321 = term329.
Proof. exact (@lem3126975 term22). Qed.
Lemma lem3126978 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3126979 : term296 = term381.
Proof. exact (@lem3126978 (NUMERAL 0)). Qed.
Lemma lem3126980 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3126981 : term437 = term438.
Proof. exact (MK_COMB (@lem3126980) (@lem3126979)). Qed.
Lemma lem3126982 : term436 = term439.
Proof. exact (MK_COMB (@lem3126981) (@lem3126976)). Qed.
Lemma lem3126983 : term440.
Proof. exact (@lem1980026 term296 term275 term321 term275). Qed.
Lemma lem3126985 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126986 : term380 = term387.
Proof. exact (@lem3126985 (NUMERAL 0) term22). Qed.
Lemma lem3126987 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126988 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3126989 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126988 h1) (fun h1 : term387 = True => @lem3126987)). Qed.
Lemma lem3126990 : term387 = True.
Proof. exact (EQ_MP (@lem3126989) (@lem3126987)). Qed.
Lemma lem3126991 : term380 = True.
Proof. exact (TRANS (@lem3126986) (@lem3126990)). Qed.
Lemma lem3126992 : True = term380.
Proof. exact (SYM (@lem3126991)). Qed.
Lemma lem3126993 : term380.
Proof. exact (EQ_MP (@lem3126992) (@lem0)). Qed.
Lemma lem3126994 : term441.
Proof. exact (@lem3126983 (@lem3126993)). Qed.
Lemma lem3126996 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3126997 : term380 = term387.
Proof. exact (@lem3126996 (NUMERAL 0) term22). Qed.
Lemma lem3126998 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3126999 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3127000 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3126999 h1) (fun h1 : term387 = True => @lem3126998)). Qed.
Lemma lem3127001 : term387 = True.
Proof. exact (EQ_MP (@lem3127000) (@lem3126998)). Qed.
Lemma lem3127002 : term380 = True.
Proof. exact (TRANS (@lem3126997) (@lem3127001)). Qed.
Lemma lem3127003 : True = term380.
Proof. exact (SYM (@lem3127002)). Qed.
Lemma lem3127004 : term380.
Proof. exact (EQ_MP (@lem3127003) (@lem0)). Qed.
Lemma lem3127005 : term439 = term442.
Proof. exact (@lem3126994 (@lem3127004)). Qed.
Lemma lem3127007 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3127008 : term332 = term343.
Proof. exact (@lem3127007 term22 term22). Qed.
Lemma lem3127009 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127010 : term340 = term22.
Proof. exact (EQ_MP (@lem3127009) (@lem940073)). Qed.
Lemma lem3127011 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127012 : term338 = term275.
Proof. exact (MK_COMB (@lem3127011) (@lem3127010)). Qed.
Lemma lem3127013 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3127014 : term343 = term321.
Proof. exact (MK_COMB (@lem3127013) (@lem3127012)). Qed.
Lemma lem3127015 : term332 = term321.
Proof. exact (TRANS (@lem3127008) (@lem3127014)). Qed.
Lemma lem3127017 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3127018 : term391 = term296.
Proof. exact (@lem3127017 term22). Qed.
Lemma lem3127019 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3127020 : term443 = term437.
Proof. exact (MK_COMB (@lem3127019) (@lem3127018)). Qed.
Lemma lem3127021 : term442 = term436.
Proof. exact (MK_COMB (@lem3127020) (@lem3127015)). Qed.
Lemma lem3127023 (m : nat) (n : nat) : (term444 m n) = (term445 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3127024 : term436 = term446.
Proof. exact (@lem3127023 (NUMERAL 0) term22). Qed.
Lemma lem3127025 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3127026 (h1 : term121 = (BIT1 0)) : (term22 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3127027 : (term121 = (BIT1 0)) = ((term22 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3127026 h1) (fun h1 : (term22 = (NUMERAL 0)) = False => @lem3127025)). Qed.
Lemma lem3127028 : (term22 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3127027) (@lem3127025)). Qed.
Lemma lem3127029 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3127030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3127031 : term447 = (and True).
Proof. exact (MK_COMB (@lem3127030) (@lem3127029)). Qed.
Lemma lem3127032 : term446 = (True /\ False).
Proof. exact (MK_COMB (@lem3127031) (@lem3127028)). Qed.
Lemma lem3127034 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3127035 : term446 = False.
Proof. exact (TRANS (@lem3127032) (@lem3127034)). Qed.
Lemma lem3127036 : term436 = False.
Proof. exact (TRANS (@lem3127024) (@lem3127035)). Qed.
Lemma lem3127037 : term442 = False.
Proof. exact (TRANS (@lem3127021) (@lem3127036)). Qed.
Lemma lem3127038 : term439 = False.
Proof. exact (TRANS (@lem3127005) (@lem3127037)). Qed.
Lemma lem3127039 : term436 = False.
Proof. exact (TRANS (@lem3126982) (@lem3127038)). Qed.
Lemma lem3127040 : term435 = False.
Proof. exact (TRANS (@lem3126973) (@lem3127039)). Qed.
Lemma lem3127041 (y : int) (x : int) (h1 : term581 y x) : False.
Proof. exact (EQ_MP (@lem3127040) (@lem3126970 y x h1)). Qed.
Lemma lem3127042 (y : int) (x : int) (h1 : term564 y x) : term564 y x.
Proof. exact (h1). Qed.
Lemma lem3127043 (y : int) (x : int) (h1 : term564 y x) : term581 y x.
Proof. exact (EQ_MP (@lem3126691 y x) (@lem3127042 y x h1)). Qed.
Lemma lem3127044 (y : int) (x : int) (h1 : term564 y x) : (term581 y x) = False.
Proof. exact (prop_ext (fun h2 : term581 y x => @lem3127041 y x h2) (fun h2 : False => @lem3127043 y x h1)). Qed.
Lemma lem3127045 (y : int) (x : int) (h1 : term564 y x) : False.
Proof. exact (EQ_MP (@lem3127044 y x h1) (@lem3127043 y x h1)). Qed.
Lemma lem3127046 (y : int) (x : int) (h1 : term529 y x) : term529 y x.
Proof. exact (h1). Qed.
Lemma lem3127047 (y : int) (x : int) (h1 : term529 y x) : term564 y x.
Proof. exact (EQ_MP (@lem3126620 y x) (@lem3127046 y x h1)). Qed.
Lemma lem3127048 (y : int) (x : int) (h1 : term529 y x) : (term564 y x) = False.
Proof. exact (prop_ext (fun h2 : term564 y x => @lem3127045 y x h2) (fun h2 : False => @lem3127047 y x h1)). Qed.
Lemma lem3127049 (y : int) (x : int) (h1 : term529 y x) : False.
Proof. exact (EQ_MP (@lem3127048 y x h1) (@lem3127047 y x h1)). Qed.
Lemma lem3127050 (y : int) (x : int) : term595 y x.
Proof. exact (fun h0 : term529 y x => @lem3127049 y x h0). Qed.
Lemma lem3127051 (y : int) (x : int) : term596 y x.
Proof. exact (@lem1386578 (term597 y x)). Qed.
Lemma lem3127054 (y : int) (x : int) : term597 y x.
Proof. exact (@lem3127051 y x (@lem3127050 y x)). Qed.
Lemma lem3127055 (y : int) (x : int) : (term528 y x) = (term499 y x).
Proof. exact (SYM (@lem3126376 y x)). Qed.
Lemma lem3127056 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3127057 (y : int) (x : int) : (term597 y x) = (term485 y x).
Proof. exact (MK_COMB (@lem3127056) (@lem3127055 y x)). Qed.
Lemma lem3127058 (y : int) (x : int) : term485 y x.
Proof. exact (EQ_MP (@lem3127057 y x) (@lem3127054 y x)). Qed.
Lemma lem3127059 (y : int) (x : int) : term483 y x.
Proof. exact (EQ_MP (@lem3126259 y x) (@lem3127058 y x)). Qed.
Lemma lem3127060 (y : int) (x : int) : (term483 y x) = (term484 y x).
Proof. exact (SYM (@lem3126258 y x)). Qed.
Lemma lem3127061 (y : int) (x : int) : term484 y x.
Proof. exact (EQ_MP (@lem3127060 y x) (@lem3127059 y x)). Qed.
Lemma lem3127062 (y : int) (x : int) : (term484 y x) = ((term484 y x) = True).
Proof. exact (@lem7 (term484 y x)). Qed.
Lemma lem3127063 (y : int) (x : int) : (term484 y x) = True.
Proof. exact (EQ_MP (@lem3127062 y x) (@lem3127061 y x)). Qed.
Lemma lem3127064 (y : int) (x : int) : True = (term484 y x).
Proof. exact (SYM (@lem3127063 y x)). Qed.
Lemma lem3127065 (y : int) (x : int) : term484 y x.
Proof. exact (EQ_MP (@lem3127064 y x) (@lem0)). Qed.
Lemma lem3127066 (x : int) (y : int) (h1 : y = term10) : term476 x.
Proof. exact (@lem3127065 y x (@lem3126087 y h1)). Qed.
Lemma lem3127068 (x : int) (y : int) : term257 x y.
Proof. exact (@lem3126082 x y (@lem3126074 x y)). Qed.
Lemma lem3127069 (x : int) (y : int) : term598 x y.
Proof. exact (@lem3127068 x (term254 x y)). Qed.
Lemma lem3127071 (x : int) (y : int) : (term254 x y) = (term255 x y).
Proof. exact (EQ_MP (@lem3125317 x y) (@lem3125316 x y)). Qed.
Lemma lem3127072 (x : int) : (term599 x) = (term599 x).
Proof. exact (eq_refl (term599 x)). Qed.
Lemma lem3127073 (x : int) (y : int) : (term600 x y) = (term601 x y).
Proof. exact (MK_COMB (@lem3127072 x) (@lem3127071 x y)). Qed.
Lemma lem3127074 (x : int) (y : int) : (term601 x y) = (term600 x y).
Proof. exact (SYM (@lem3127073 x y)). Qed.
Lemma lem3127076 (y : int) (x : int) (z : int) : term242 y x z.
Proof. exact (EQ_MP (@lem3125311 y x z) (@lem3125310 y x z)). Qed.
Lemma lem3127077 (x : int) (y : int) : term602 x y.
Proof. exact (@lem3127076 term110 (int_abs x) (int_abs y)). Qed.
Lemma lem3127078 (x : int) (y : int) : (term603 x y) = (term604 x y).
Proof. exact (@lem2954598 (term604 x y)). Qed.
Lemma lem3127095 (x : int) (y : int) : (term605 x y) = (term606 x y).
Proof. exact (@lem17045 (term607 x) (term608 y)). Qed.
Lemma lem3127097 (y : int) : (term609 y) = (term609 y).
Proof. exact (eq_refl (term609 y)). Qed.
Lemma lem3127098 (x : int) (y : int) : (term610 x y) = (term611 x y).
Proof. exact (MK_COMB (@lem3127097 y) (@lem3127095 x y)). Qed.
Lemma lem3127099 (x : int) (y : int) : (term612 x y) = (term610 x y).
Proof. exact (@lem17362 (term135 y) (term613 x y)). Qed.
Lemma lem3127127 (x : int) (y : int) : (term612 x y) = (term611 x y).
Proof. exact (TRANS (@lem3127099 x y) (@lem3127098 x y)). Qed.
Lemma lem3127129 (y : int) (x : int) : (term614 x y) = (term615 y x).
Proof. exact (proj1 (@lem2841544 x y)). Qed.
Lemma lem3127130 (y : int) : (term135 y) = (term616 y).
Proof. exact (@lem3127129 term10 y). Qed.
Lemma lem3127132 (x : int) (y : int) : (int_le x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3127133 (y : int) : (term617 y) = (term618 y).
Proof. exact (@lem3127132 (term619 y) term10). Qed.
Lemma lem3127135 (x : int) (y : int) : (term286 x y) = (term287 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3127136 (y : int) : (term620 y) = (term621 y).
Proof. exact (@lem3127135 y term110). Qed.
Lemma lem3127138 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3127139 : term274 = term275.
Proof. exact (@lem3127138 term22). Qed.
Lemma lem3127140 (y : int) : (term361 y) = (term361 y).
Proof. exact (eq_refl (term361 y)). Qed.
Lemma lem3127141 (y : int) : (term621 y) = (term322 y).
Proof. exact (MK_COMB (@lem3127140 y) (@lem3127139)). Qed.
Lemma lem3127142 (y : int) : (term620 y) = (term322 y).
Proof. exact (TRANS (@lem3127136 y) (@lem3127141 y)). Qed.
Lemma lem3127143 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3127144 (y : int) : (term622 y) = (term623 y).
Proof. exact (MK_COMB (@lem3127143) (@lem3127142 y)). Qed.
Lemma lem3127146 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3127147 : term295 = term296.
Proof. exact (@lem3127146 (NUMERAL 0)). Qed.
Lemma lem3127148 (y : int) : (term618 y) = (term624 y).
Proof. exact (MK_COMB (@lem3127144 y) (@lem3127147)). Qed.
Lemma lem3127149 (y : int) : (term617 y) = (term624 y).
Proof. exact (TRANS (@lem3127133 y) (@lem3127148 y)). Qed.
Lemma lem3127150 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3127151 (y : int) : (term625 y) = (term626 y).
Proof. exact (MK_COMB (@lem3127150) (@lem3127149 y)). Qed.
Lemma lem3127153 (x : int) (y : int) : (int_le x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3127154 (y : int) : (term627 y) = (term628 y).
Proof. exact (@lem3127153 term629 y). Qed.
Lemma lem3127156 (x : int) (y : int) : (term286 x y) = (term287 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3127157 : term630 = term631.
Proof. exact (@lem3127156 term10 term110). Qed.
Lemma lem3127159 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3127160 : term295 = term296.
Proof. exact (@lem3127159 (NUMERAL 0)). Qed.
Lemma lem3127161 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3127162 : term632 = term350.
Proof. exact (MK_COMB (@lem3127161) (@lem3127160)). Qed.
Lemma lem3127164 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3127165 : term274 = term275.
Proof. exact (@lem3127164 term22). Qed.
Lemma lem3127166 : term631 = term633.
Proof. exact (MK_COMB (@lem3127162) (@lem3127165)). Qed.
Lemma lem3127167 : term630 = term633.
Proof. exact (TRANS (@lem3127157) (@lem3127166)). Qed.
Lemma lem3127168 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3127169 : term634 = term635.
Proof. exact (MK_COMB (@lem3127168) (@lem3127167)). Qed.
Lemma lem3127170 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3127171 (y : int) : (term628 y) = (term636 y).
Proof. exact (MK_COMB (@lem3127169) (@lem3127170 y)). Qed.
Lemma lem3127172 (y : int) : (term627 y) = (term636 y).
Proof. exact (TRANS (@lem3127154 y) (@lem3127171 y)). Qed.
Lemma lem3127173 (y : int) : (term616 y) = (term637 y).
Proof. exact (MK_COMB (@lem3127151 y) (@lem3127172 y)). Qed.
Lemma lem3127174 (y : int) : (term135 y) = (term637 y).
Proof. exact (TRANS (@lem3127130 y) (@lem3127173 y)). Qed.
Lemma lem3127176 (y : int) (x : int) : (term280 x y) = (term281 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem3127177 (x : int) : (term638 x) = (term639 x).
Proof. exact (@lem3127176 (int_abs x) term10). Qed.
Lemma lem3127179 (x : int) (y : int) : (int_le x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3127180 (x : int) : (term639 x) = (term640 x).
Proof. exact (@lem3127179 (term641 x) term10). Qed.
Lemma lem3127182 (x : int) (y : int) : (term286 x y) = (term287 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3127183 (x : int) : (term642 x) = (term643 x).
Proof. exact (@lem3127182 (int_abs x) term110). Qed.
Lemma lem3127185 (x : int) : (term269 x) = (term270 x).
Proof. exact (EQ_MP (@lem2841562 x) (@lem2841561 x)). Qed.
Lemma lem3127186 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3127187 (x : int) : (term644 x) = (term645 x).
Proof. exact (MK_COMB (@lem3127186) (@lem3127185 x)). Qed.
Lemma lem3127189 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3127190 : term274 = term275.
Proof. exact (@lem3127189 term22). Qed.
Lemma lem3127191 (x : int) : (term643 x) = (term646 x).
Proof. exact (MK_COMB (@lem3127187 x) (@lem3127190)). Qed.
Lemma lem3127192 (x : int) : (term642 x) = (term646 x).
Proof. exact (TRANS (@lem3127183 x) (@lem3127191 x)). Qed.
Lemma lem3127193 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3127194 (x : int) : (term647 x) = (term648 x).
Proof. exact (MK_COMB (@lem3127193) (@lem3127192 x)). Qed.
Lemma lem3127196 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3127197 : term295 = term296.
Proof. exact (@lem3127196 (NUMERAL 0)). Qed.
Lemma lem3127198 (x : int) : (term640 x) = (term649 x).
Proof. exact (MK_COMB (@lem3127194 x) (@lem3127197)). Qed.
Lemma lem3127199 (x : int) : (term639 x) = (term649 x).
Proof. exact (TRANS (@lem3127180 x) (@lem3127198 x)). Qed.
Lemma lem3127200 (x : int) : (term638 x) = (term649 x).
Proof. exact (TRANS (@lem3127177 x) (@lem3127199 x)). Qed.
Lemma lem3127202 (y : int) (x : int) : (term280 x y) = (term281 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem3127203 (y : int) : (term650 y) = (term651 y).
Proof. exact (@lem3127202 (int_abs y) term110). Qed.
Lemma lem3127205 (x : int) (y : int) : (int_le x y) = (term262 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3127206 (y : int) : (term651 y) = (term652 y).
Proof. exact (@lem3127205 (term641 y) term110). Qed.
Lemma lem3127208 (x : int) (y : int) : (term286 x y) = (term287 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3127209 (y : int) : (term642 y) = (term643 y).
Proof. exact (@lem3127208 (int_abs y) term110). Qed.
Lemma lem3127211 (x : int) : (term269 x) = (term270 x).
Proof. exact (EQ_MP (@lem2841562 x) (@lem2841561 x)). Qed.
Lemma lem3127212 (y : int) : (term269 y) = (term270 y).
Proof. exact (@lem3127211 y). Qed.
Lemma lem3127213 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3127214 (y : int) : (term644 y) = (term645 y).
Proof. exact (MK_COMB (@lem3127213) (@lem3127212 y)). Qed.
Lemma lem3127216 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3127217 : term274 = term275.
Proof. exact (@lem3127216 term22). Qed.
Lemma lem3127218 (y : int) : (term643 y) = (term646 y).
Proof. exact (MK_COMB (@lem3127214 y) (@lem3127217)). Qed.
Lemma lem3127219 (y : int) : (term642 y) = (term646 y).
Proof. exact (TRANS (@lem3127209 y) (@lem3127218 y)). Qed.
Lemma lem3127220 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3127221 (y : int) : (term647 y) = (term648 y).
Proof. exact (MK_COMB (@lem3127220) (@lem3127219 y)). Qed.
Lemma lem3127223 (n : nat) : (term273 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3127224 : term274 = term275.
Proof. exact (@lem3127223 term22). Qed.
Lemma lem3127225 (y : int) : (term652 y) = (term653 y).
Proof. exact (MK_COMB (@lem3127221 y) (@lem3127224)). Qed.
Lemma lem3127226 (y : int) : (term651 y) = (term653 y).
Proof. exact (TRANS (@lem3127206 y) (@lem3127225 y)). Qed.
Lemma lem3127227 (y : int) : (term650 y) = (term653 y).
Proof. exact (TRANS (@lem3127203 y) (@lem3127226 y)). Qed.
Lemma lem3127228 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3127229 (x : int) : (term654 x) = (term655 x).
Proof. exact (MK_COMB (@lem3127228) (@lem3127200 x)). Qed.
Lemma lem3127230 (x : int) (y : int) : (term606 x y) = (term656 x y).
Proof. exact (MK_COMB (@lem3127229 x) (@lem3127227 y)). Qed.
Lemma lem3127231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3127232 (y : int) : (term609 y) = (term657 y).
Proof. exact (MK_COMB (@lem3127231) (@lem3127174 y)). Qed.
Lemma lem3127233 (x : int) (y : int) : (term611 x y) = (term658 x y).
Proof. exact (MK_COMB (@lem3127232 y) (@lem3127230 x y)). Qed.
Lemma lem3127234 (x : int) (y : int) : (term612 x y) = (term658 x y).
Proof. exact (TRANS (@lem3127127 x y) (@lem3127233 x y)). Qed.
Lemma lem3127238 (t : Prop) : (term301 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3127274 (x : int) (y : int) : (term659 x y) = (term658 x y).
Proof. exact (@lem3127238 (term658 x y)). Qed.
Lemma lem3127275 (y : int) : (term624 y) = (term660 y).
Proof. exact (@lem1988287 term296 (term322 y)). Qed.
Lemma lem3127287 (y : int) : (term661 y) = (term662 y).
Proof. exact (@lem1982792 term296 (term322 y)). Qed.
Lemma lem3127288 (y : int) : (term323 y) = (term324 y).
Proof. exact (@lem1982781 (real_of_int y) term321 term275). Qed.
Lemma lem3127290 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3127291 : term275 = term326.
Proof. exact (@lem3127290 term22). Qed.
Lemma lem3127293 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3127294 : term321 = term329.
Proof. exact (@lem3127293 term22). Qed.
Lemma lem3127295 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3127296 : term330 = term331.
Proof. exact (MK_COMB (@lem3127295) (@lem3127294)). Qed.
Lemma lem3127297 : term332 = term333.
Proof. exact (MK_COMB (@lem3127296) (@lem3127291)). Qed.
Lemma lem3127298 : term333 = term334.
Proof. exact (@lem1981613 term321 term275 term275 term275). Qed.
Lemma lem3127300 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3127301 : term337 = term338.
Proof. exact (@lem3127300 term22 term22). Qed.
Lemma lem3127302 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127303 : term340 = term22.
Proof. exact (EQ_MP (@lem3127302) (@lem940073)). Qed.
Lemma lem3127304 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127305 : term338 = term275.
Proof. exact (MK_COMB (@lem3127304) (@lem3127303)). Qed.
Lemma lem3127306 : term337 = term275.
Proof. exact (TRANS (@lem3127301) (@lem3127305)). Qed.
Lemma lem3127308 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3127309 : term332 = term343.
Proof. exact (@lem3127308 term22 term22). Qed.
Lemma lem3127310 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127311 : term340 = term22.
Proof. exact (EQ_MP (@lem3127310) (@lem940073)). Qed.
Lemma lem3127312 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127313 : term338 = term275.
Proof. exact (MK_COMB (@lem3127312) (@lem3127311)). Qed.
Lemma lem3127314 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3127315 : term343 = term321.
Proof. exact (MK_COMB (@lem3127314) (@lem3127313)). Qed.
Lemma lem3127316 : term332 = term321.
Proof. exact (TRANS (@lem3127309) (@lem3127315)). Qed.
Lemma lem3127317 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3127318 : term344 = term345.
Proof. exact (MK_COMB (@lem3127317) (@lem3127316)). Qed.
Lemma lem3127319 : term334 = term329.
Proof. exact (MK_COMB (@lem3127318) (@lem3127306)). Qed.
Lemma lem3127320 : term333 = term329.
Proof. exact (TRANS (@lem3127298) (@lem3127319)). Qed.
Lemma lem3127321 : term332 = term329.
Proof. exact (TRANS (@lem3127297) (@lem3127320)). Qed.
Lemma lem3127323 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3127324 : term329 = term321.
Proof. exact (@lem3127323 term321). Qed.
Lemma lem3127325 : term332 = term321.
Proof. exact (TRANS (@lem3127321) (@lem3127324)). Qed.
Lemma lem3127328 (y : int) : (term347 y) = (term347 y).
Proof. exact (eq_refl (term347 y)). Qed.
Lemma lem3127329 (y : int) : (term324 y) = (term348 y).
Proof. exact (MK_COMB (@lem3127328 y) (@lem3127325)). Qed.
Lemma lem3127330 (y : int) : (term323 y) = (term348 y).
Proof. exact (TRANS (@lem3127288 y) (@lem3127329 y)). Qed.
Lemma lem3127331 : term350 = term350.
Proof. exact (eq_refl term350). Qed.
Lemma lem3127332 (y : int) : (term662 y) = (term663 y).
Proof. exact (MK_COMB (@lem3127331) (@lem3127330 y)). Qed.
Lemma lem3127333 (y : int) : (term663 y) = (term348 y).
Proof. exact (@lem1982721 (term348 y)). Qed.
Lemma lem3127334 (y : int) : (term662 y) = (term348 y).
Proof. exact (TRANS (@lem3127332 y) (@lem3127333 y)). Qed.
Lemma lem3127336 (y : int) : (term661 y) = (term348 y).
Proof. exact (TRANS (@lem3127287 y) (@lem3127334 y)). Qed.
Lemma lem3127337 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3127338 (y : int) : (term664 y) = (term571 y).
Proof. exact (MK_COMB (@lem3127337) (@lem3127336 y)). Qed.
Lemma lem3127339 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3127340 (y : int) : (term660 y) = (term573 y).
Proof. exact (MK_COMB (@lem3127338 y) (@lem3127339)). Qed.
Lemma lem3127341 (y : int) : (term624 y) = (term573 y).
Proof. exact (TRANS (@lem3127275 y) (@lem3127340 y)). Qed.
Lemma lem3127342 (y : int) : (term636 y) = (term665 y).
Proof. exact (@lem1988287 (real_of_int y) term633). Qed.
Lemma lem3127349 : term633 = term275.
Proof. exact (@lem1982721 term275). Qed.
Lemma lem3127352 (y : int) : (term304 y) = (term304 y).
Proof. exact (eq_refl (term304 y)). Qed.
Lemma lem3127353 (y : int) : (term666 y) = (term667 y).
Proof. exact (MK_COMB (@lem3127352 y) (@lem3127349)). Qed.
Lemma lem3127354 (y : int) : (term667 y) = (term668 y).
Proof. exact (@lem1982792 (real_of_int y) term275). Qed.
Lemma lem3127356 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3127357 : term275 = term326.
Proof. exact (@lem3127356 term22). Qed.
Lemma lem3127359 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3127360 : term321 = term329.
Proof. exact (@lem3127359 term22). Qed.
Lemma lem3127361 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3127362 : term330 = term331.
Proof. exact (MK_COMB (@lem3127361) (@lem3127360)). Qed.
Lemma lem3127363 : term332 = term333.
Proof. exact (MK_COMB (@lem3127362) (@lem3127357)). Qed.
Lemma lem3127364 : term333 = term334.
Proof. exact (@lem1981613 term321 term275 term275 term275). Qed.
Lemma lem3127366 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3127367 : term337 = term338.
Proof. exact (@lem3127366 term22 term22). Qed.
Lemma lem3127368 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127369 : term340 = term22.
Proof. exact (EQ_MP (@lem3127368) (@lem940073)). Qed.
Lemma lem3127370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127371 : term338 = term275.
Proof. exact (MK_COMB (@lem3127370) (@lem3127369)). Qed.
Lemma lem3127372 : term337 = term275.
Proof. exact (TRANS (@lem3127367) (@lem3127371)). Qed.
Lemma lem3127374 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3127375 : term332 = term343.
Proof. exact (@lem3127374 term22 term22). Qed.
Lemma lem3127376 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127377 : term340 = term22.
Proof. exact (EQ_MP (@lem3127376) (@lem940073)). Qed.
Lemma lem3127378 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127379 : term338 = term275.
Proof. exact (MK_COMB (@lem3127378) (@lem3127377)). Qed.
Lemma lem3127380 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3127381 : term343 = term321.
Proof. exact (MK_COMB (@lem3127380) (@lem3127379)). Qed.
Lemma lem3127382 : term332 = term321.
Proof. exact (TRANS (@lem3127375) (@lem3127381)). Qed.
Lemma lem3127383 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3127384 : term344 = term345.
Proof. exact (MK_COMB (@lem3127383) (@lem3127382)). Qed.
Lemma lem3127385 : term334 = term329.
Proof. exact (MK_COMB (@lem3127384) (@lem3127372)). Qed.
Lemma lem3127386 : term333 = term329.
Proof. exact (TRANS (@lem3127364) (@lem3127385)). Qed.
Lemma lem3127387 : term332 = term329.
Proof. exact (TRANS (@lem3127363) (@lem3127386)). Qed.
Lemma lem3127389 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3127390 : term329 = term321.
Proof. exact (@lem3127389 term321). Qed.
Lemma lem3127391 : term332 = term321.
Proof. exact (TRANS (@lem3127387) (@lem3127390)). Qed.
Lemma lem3127392 (y : int) : (term361 y) = (term361 y).
Proof. exact (eq_refl (term361 y)). Qed.
Lemma lem3127395 (y : int) : (term668 y) = (term669 y).
Proof. exact (MK_COMB (@lem3127392 y) (@lem3127391)). Qed.
Lemma lem3127396 (y : int) : (term667 y) = (term669 y).
Proof. exact (TRANS (@lem3127354 y) (@lem3127395 y)). Qed.
Lemma lem3127397 (y : int) : (term666 y) = (term669 y).
Proof. exact (TRANS (@lem3127353 y) (@lem3127396 y)). Qed.
Lemma lem3127398 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3127399 (y : int) : (term670 y) = (term671 y).
Proof. exact (MK_COMB (@lem3127398) (@lem3127397 y)). Qed.
Lemma lem3127400 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3127401 (y : int) : (term665 y) = (term672 y).
Proof. exact (MK_COMB (@lem3127399 y) (@lem3127400)). Qed.
Lemma lem3127402 (y : int) : (term636 y) = (term672 y).
Proof. exact (TRANS (@lem3127342 y) (@lem3127401 y)). Qed.
Lemma lem3127403 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3127404 (y : int) : (term626 y) = (term673 y).
Proof. exact (MK_COMB (@lem3127403) (@lem3127341 y)). Qed.
Lemma lem3127405 (y : int) : (term637 y) = (term674 y).
Proof. exact (MK_COMB (@lem3127404 y) (@lem3127402 y)). Qed.
Lemma lem3127406 (x : int) : (term649 x) = (term675 x).
Proof. exact (@lem1988287 term296 (term646 x)). Qed.
Lemma lem3127420 (x : int) : (term676 x) = (term677 x).
Proof. exact (@lem1982792 term296 (term646 x)). Qed.
Lemma lem3127421 (x : int) : (term678 x) = (term679 x).
Proof. exact (@lem1982781 (term270 x) term321 term275). Qed.
Lemma lem3127423 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3127424 : term275 = term326.
Proof. exact (@lem3127423 term22). Qed.
Lemma lem3127426 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3127427 : term321 = term329.
Proof. exact (@lem3127426 term22). Qed.
Lemma lem3127428 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3127429 : term330 = term331.
Proof. exact (MK_COMB (@lem3127428) (@lem3127427)). Qed.
Lemma lem3127430 : term332 = term333.
Proof. exact (MK_COMB (@lem3127429) (@lem3127424)). Qed.
Lemma lem3127431 : term333 = term334.
Proof. exact (@lem1981613 term321 term275 term275 term275). Qed.
Lemma lem3127433 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3127434 : term337 = term338.
Proof. exact (@lem3127433 term22 term22). Qed.
Lemma lem3127435 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127436 : term340 = term22.
Proof. exact (EQ_MP (@lem3127435) (@lem940073)). Qed.
Lemma lem3127437 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127438 : term338 = term275.
Proof. exact (MK_COMB (@lem3127437) (@lem3127436)). Qed.
Lemma lem3127439 : term337 = term275.
Proof. exact (TRANS (@lem3127434) (@lem3127438)). Qed.
Lemma lem3127441 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3127442 : term332 = term343.
Proof. exact (@lem3127441 term22 term22). Qed.
Lemma lem3127443 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127444 : term340 = term22.
Proof. exact (EQ_MP (@lem3127443) (@lem940073)). Qed.
Lemma lem3127445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127446 : term338 = term275.
Proof. exact (MK_COMB (@lem3127445) (@lem3127444)). Qed.
Lemma lem3127447 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3127448 : term343 = term321.
Proof. exact (MK_COMB (@lem3127447) (@lem3127446)). Qed.
Lemma lem3127449 : term332 = term321.
Proof. exact (TRANS (@lem3127442) (@lem3127448)). Qed.
Lemma lem3127450 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3127451 : term344 = term345.
Proof. exact (MK_COMB (@lem3127450) (@lem3127449)). Qed.
Lemma lem3127452 : term334 = term329.
Proof. exact (MK_COMB (@lem3127451) (@lem3127439)). Qed.
Lemma lem3127453 : term333 = term329.
Proof. exact (TRANS (@lem3127431) (@lem3127452)). Qed.
Lemma lem3127454 : term332 = term329.
Proof. exact (TRANS (@lem3127430) (@lem3127453)). Qed.
Lemma lem3127456 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3127457 : term329 = term321.
Proof. exact (@lem3127456 term321). Qed.
Lemma lem3127458 : term332 = term321.
Proof. exact (TRANS (@lem3127454) (@lem3127457)). Qed.
Lemma lem3127461 (x : int) : (term680 x) = (term680 x).
Proof. exact (eq_refl (term680 x)). Qed.
Lemma lem3127462 (x : int) : (term679 x) = (term681 x).
Proof. exact (MK_COMB (@lem3127461 x) (@lem3127458)). Qed.
Lemma lem3127463 (x : int) : (term678 x) = (term681 x).
Proof. exact (TRANS (@lem3127421 x) (@lem3127462 x)). Qed.
Lemma lem3127464 : term350 = term350.
Proof. exact (eq_refl term350). Qed.
Lemma lem3127465 (x : int) : (term677 x) = (term682 x).
Proof. exact (MK_COMB (@lem3127464) (@lem3127463 x)). Qed.
Lemma lem3127466 (x : int) : (term682 x) = (term681 x).
Proof. exact (@lem1982721 (term681 x)). Qed.
Lemma lem3127467 (x : int) : (term677 x) = (term681 x).
Proof. exact (TRANS (@lem3127465 x) (@lem3127466 x)). Qed.
Lemma lem3127469 (x : int) : (term676 x) = (term681 x).
Proof. exact (TRANS (@lem3127420 x) (@lem3127467 x)). Qed.
Lemma lem3127470 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3127471 (x : int) : (term683 x) = (term684 x).
Proof. exact (MK_COMB (@lem3127470) (@lem3127469 x)). Qed.
Lemma lem3127472 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3127473 (x : int) : (term675 x) = (term685 x).
Proof. exact (MK_COMB (@lem3127471 x) (@lem3127472)). Qed.
Lemma lem3127474 (x : int) : (term649 x) = (term685 x).
Proof. exact (TRANS (@lem3127406 x) (@lem3127473 x)). Qed.
Lemma lem3127475 (y : int) : (term653 y) = (term686 y).
Proof. exact (@lem1988287 term275 (term646 y)). Qed.
Lemma lem3127489 (y : int) : (term687 y) = (term688 y).
Proof. exact (@lem1982792 term275 (term646 y)). Qed.
Lemma lem3127490 (y : int) : (term678 y) = (term679 y).
Proof. exact (@lem1982781 (term270 y) term321 term275). Qed.
Lemma lem3127492 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3127493 : term275 = term326.
Proof. exact (@lem3127492 term22). Qed.
Lemma lem3127495 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3127496 : term321 = term329.
Proof. exact (@lem3127495 term22). Qed.
Lemma lem3127497 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3127498 : term330 = term331.
Proof. exact (MK_COMB (@lem3127497) (@lem3127496)). Qed.
Lemma lem3127499 : term332 = term333.
Proof. exact (MK_COMB (@lem3127498) (@lem3127493)). Qed.
Lemma lem3127500 : term333 = term334.
Proof. exact (@lem1981613 term321 term275 term275 term275). Qed.
Lemma lem3127502 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3127503 : term337 = term338.
Proof. exact (@lem3127502 term22 term22). Qed.
Lemma lem3127504 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127505 : term340 = term22.
Proof. exact (EQ_MP (@lem3127504) (@lem940073)). Qed.
Lemma lem3127506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127507 : term338 = term275.
Proof. exact (MK_COMB (@lem3127506) (@lem3127505)). Qed.
Lemma lem3127508 : term337 = term275.
Proof. exact (TRANS (@lem3127503) (@lem3127507)). Qed.
Lemma lem3127510 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3127511 : term332 = term343.
Proof. exact (@lem3127510 term22 term22). Qed.
Lemma lem3127512 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127513 : term340 = term22.
Proof. exact (EQ_MP (@lem3127512) (@lem940073)). Qed.
Lemma lem3127514 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127515 : term338 = term275.
Proof. exact (MK_COMB (@lem3127514) (@lem3127513)). Qed.
Lemma lem3127516 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3127517 : term343 = term321.
Proof. exact (MK_COMB (@lem3127516) (@lem3127515)). Qed.
Lemma lem3127518 : term332 = term321.
Proof. exact (TRANS (@lem3127511) (@lem3127517)). Qed.
Lemma lem3127519 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3127520 : term344 = term345.
Proof. exact (MK_COMB (@lem3127519) (@lem3127518)). Qed.
Lemma lem3127521 : term334 = term329.
Proof. exact (MK_COMB (@lem3127520) (@lem3127508)). Qed.
Lemma lem3127522 : term333 = term329.
Proof. exact (TRANS (@lem3127500) (@lem3127521)). Qed.
Lemma lem3127523 : term332 = term329.
Proof. exact (TRANS (@lem3127499) (@lem3127522)). Qed.
Lemma lem3127525 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3127526 : term329 = term321.
Proof. exact (@lem3127525 term321). Qed.
Lemma lem3127527 : term332 = term321.
Proof. exact (TRANS (@lem3127523) (@lem3127526)). Qed.
Lemma lem3127530 (y : int) : (term680 y) = (term680 y).
Proof. exact (eq_refl (term680 y)). Qed.
Lemma lem3127531 (y : int) : (term679 y) = (term681 y).
Proof. exact (MK_COMB (@lem3127530 y) (@lem3127527)). Qed.
Lemma lem3127532 (y : int) : (term678 y) = (term681 y).
Proof. exact (TRANS (@lem3127490 y) (@lem3127531 y)). Qed.
Lemma lem3127533 : term689 = term689.
Proof. exact (eq_refl term689). Qed.
Lemma lem3127534 (y : int) : (term688 y) = (term690 y).
Proof. exact (MK_COMB (@lem3127533) (@lem3127532 y)). Qed.
Lemma lem3127535 (y : int) : (term690 y) = (term691 y).
Proof. exact (@lem1982757 (term309 y) term275 term321). Qed.
Lemma lem3127537 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3127538 : term321 = term329.
Proof. exact (@lem3127537 term22). Qed.
Lemma lem3127540 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3127541 : term275 = term326.
Proof. exact (@lem3127540 term22). Qed.
Lemma lem3127542 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3127543 : term689 = term692.
Proof. exact (MK_COMB (@lem3127542) (@lem3127541)). Qed.
Lemma lem3127544 : term693 = term694.
Proof. exact (MK_COMB (@lem3127543) (@lem3127538)). Qed.
Lemma lem3127545 : term695.
Proof. exact (@lem1981473 term275 term275 term321 term275 term296 term275). Qed.
Lemma lem3127547 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3127548 : term380 = term387.
Proof. exact (@lem3127547 (NUMERAL 0) term22). Qed.
Lemma lem3127549 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3127550 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3127551 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3127550 h1) (fun h1 : term387 = True => @lem3127549)). Qed.
Lemma lem3127552 : term387 = True.
Proof. exact (EQ_MP (@lem3127551) (@lem3127549)). Qed.
Lemma lem3127553 : term380 = True.
Proof. exact (TRANS (@lem3127548) (@lem3127552)). Qed.
Lemma lem3127554 : True = term380.
Proof. exact (SYM (@lem3127553)). Qed.
Lemma lem3127555 : term380.
Proof. exact (EQ_MP (@lem3127554) (@lem0)). Qed.
Lemma lem3127556 : term696.
Proof. exact (@lem3127545 (@lem3127555)). Qed.
Lemma lem3127558 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3127559 : term380 = term387.
Proof. exact (@lem3127558 (NUMERAL 0) term22). Qed.
Lemma lem3127560 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3127561 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3127562 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3127561 h1) (fun h1 : term387 = True => @lem3127560)). Qed.
Lemma lem3127563 : term387 = True.
Proof. exact (EQ_MP (@lem3127562) (@lem3127560)). Qed.
Lemma lem3127564 : term380 = True.
Proof. exact (TRANS (@lem3127559) (@lem3127563)). Qed.
Lemma lem3127565 : True = term380.
Proof. exact (SYM (@lem3127564)). Qed.
Lemma lem3127566 : term380.
Proof. exact (EQ_MP (@lem3127565) (@lem0)). Qed.
Lemma lem3127567 : term697.
Proof. exact (@lem3127556 (@lem3127566)). Qed.
Lemma lem3127569 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3127570 : term380 = term387.
Proof. exact (@lem3127569 (NUMERAL 0) term22). Qed.
Lemma lem3127571 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3127572 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3127573 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3127572 h1) (fun h1 : term387 = True => @lem3127571)). Qed.
Lemma lem3127574 : term387 = True.
Proof. exact (EQ_MP (@lem3127573) (@lem3127571)). Qed.
Lemma lem3127575 : term380 = True.
Proof. exact (TRANS (@lem3127570) (@lem3127574)). Qed.
Lemma lem3127576 : True = term380.
Proof. exact (SYM (@lem3127575)). Qed.
Lemma lem3127577 : term380.
Proof. exact (EQ_MP (@lem3127576) (@lem0)). Qed.
Lemma lem3127578 : term698.
Proof. exact (@lem3127567 (@lem3127577)). Qed.
Lemma lem3127580 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3127581 : term332 = term343.
Proof. exact (@lem3127580 term22 term22). Qed.
Lemma lem3127582 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127583 : term340 = term22.
Proof. exact (EQ_MP (@lem3127582) (@lem940073)). Qed.
Lemma lem3127584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127585 : term338 = term275.
Proof. exact (MK_COMB (@lem3127584) (@lem3127583)). Qed.
Lemma lem3127586 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3127587 : term343 = term321.
Proof. exact (MK_COMB (@lem3127586) (@lem3127585)). Qed.
Lemma lem3127588 : term332 = term321.
Proof. exact (TRANS (@lem3127581) (@lem3127587)). Qed.
Lemma lem3127590 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3127591 : term337 = term338.
Proof. exact (@lem3127590 term22 term22). Qed.
Lemma lem3127592 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127593 : term340 = term22.
Proof. exact (EQ_MP (@lem3127592) (@lem940073)). Qed.
Lemma lem3127594 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127595 : term338 = term275.
Proof. exact (MK_COMB (@lem3127594) (@lem3127593)). Qed.
Lemma lem3127596 : term337 = term275.
Proof. exact (TRANS (@lem3127591) (@lem3127595)). Qed.
Lemma lem3127597 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3127598 : term699 = term689.
Proof. exact (MK_COMB (@lem3127597) (@lem3127596)). Qed.
Lemma lem3127599 : term700 = term693.
Proof. exact (MK_COMB (@lem3127598) (@lem3127588)). Qed.
Lemma lem3127601 (m : nat) : (term701 m) = term296.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem3127602 : term693 = term296.
Proof. exact (@lem3127601 term22). Qed.
Lemma lem3127603 : term700 = term296.
Proof. exact (TRANS (@lem3127599) (@lem3127602)). Qed.
Lemma lem3127604 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3127605 : term702 = term424.
Proof. exact (MK_COMB (@lem3127604) (@lem3127603)). Qed.
Lemma lem3127606 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem3127607 : term703 = term391.
Proof. exact (MK_COMB (@lem3127605) (@lem3127606)). Qed.
Lemma lem3127609 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3127610 : term391 = term296.
Proof. exact (@lem3127609 term22). Qed.
Lemma lem3127611 : term703 = term296.
Proof. exact (TRANS (@lem3127607) (@lem3127610)). Qed.
Lemma lem3127613 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3127614 : term337 = term338.
Proof. exact (@lem3127613 term22 term22). Qed.
Lemma lem3127615 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127616 : term340 = term22.
Proof. exact (EQ_MP (@lem3127615) (@lem940073)). Qed.
Lemma lem3127617 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127618 : term338 = term275.
Proof. exact (MK_COMB (@lem3127617) (@lem3127616)). Qed.
Lemma lem3127619 : term337 = term275.
Proof. exact (TRANS (@lem3127614) (@lem3127618)). Qed.
Lemma lem3127620 : term424 = term424.
Proof. exact (eq_refl term424). Qed.
Lemma lem3127621 : term426 = term391.
Proof. exact (MK_COMB (@lem3127620) (@lem3127619)). Qed.
Lemma lem3127623 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3127624 : term391 = term296.
Proof. exact (@lem3127623 term22). Qed.
Lemma lem3127625 : term426 = term296.
Proof. exact (TRANS (@lem3127621) (@lem3127624)). Qed.
Lemma lem3127626 : term296 = term426.
Proof. exact (SYM (@lem3127625)). Qed.
Lemma lem3127627 : term703 = term426.
Proof. exact (TRANS (@lem3127611) (@lem3127626)). Qed.
Lemma lem3127628 : term694 = term381.
Proof. exact (@lem3127578 (@lem3127627)). Qed.
Lemma lem3127629 : term693 = term381.
Proof. exact (TRANS (@lem3127544) (@lem3127628)). Qed.
Lemma lem3127631 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3127632 : term381 = term296.
Proof. exact (@lem3127631 term296). Qed.
Lemma lem3127633 : term693 = term296.
Proof. exact (TRANS (@lem3127629) (@lem3127632)). Qed.
Lemma lem3127634 (y : int) : (term680 y) = (term680 y).
Proof. exact (eq_refl (term680 y)). Qed.
Lemma lem3127635 (y : int) : (term691 y) = (term704 y).
Proof. exact (MK_COMB (@lem3127634 y) (@lem3127633)). Qed.
Lemma lem3127636 (y : int) : (term690 y) = (term704 y).
Proof. exact (TRANS (@lem3127535 y) (@lem3127635 y)). Qed.
Lemma lem3127637 (y : int) : (term704 y) = (term309 y).
Proof. exact (@lem1982723 (term309 y)). Qed.
Lemma lem3127638 (y : int) : (term690 y) = (term309 y).
Proof. exact (TRANS (@lem3127636 y) (@lem3127637 y)). Qed.
Lemma lem3127639 (y : int) : (term688 y) = (term309 y).
Proof. exact (TRANS (@lem3127534 y) (@lem3127638 y)). Qed.
Lemma lem3127641 (y : int) : (term687 y) = (term309 y).
Proof. exact (TRANS (@lem3127489 y) (@lem3127639 y)). Qed.
Lemma lem3127642 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3127643 (y : int) : (term705 y) = (term706 y).
Proof. exact (MK_COMB (@lem3127642) (@lem3127641 y)). Qed.
Lemma lem3127644 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3127645 (y : int) : (term686 y) = (term707 y).
Proof. exact (MK_COMB (@lem3127643 y) (@lem3127644)). Qed.
Lemma lem3127646 (y : int) : (term653 y) = (term707 y).
Proof. exact (TRANS (@lem3127475 y) (@lem3127645 y)). Qed.
Lemma lem3127647 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3127648 (x : int) : (term655 x) = (term708 x).
Proof. exact (MK_COMB (@lem3127647) (@lem3127474 x)). Qed.
Lemma lem3127649 (x : int) (y : int) : (term656 x y) = (term709 x y).
Proof. exact (MK_COMB (@lem3127648 x) (@lem3127646 y)). Qed.
Lemma lem3127650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3127651 (y : int) : (term657 y) = (term710 y).
Proof. exact (MK_COMB (@lem3127650) (@lem3127405 y)). Qed.
Lemma lem3127652 (x : int) (y : int) : (term658 x y) = (term711 x y).
Proof. exact (MK_COMB (@lem3127651 y) (@lem3127649 x y)). Qed.
Lemma lem3127659 (x : int) (y : int) : (term659 x y) = (term711 x y).
Proof. exact (TRANS (@lem3127274 x y) (@lem3127652 x y)). Qed.
Lemma lem3127673 (x : int) (y : int) : (term711 x y) = (term712 x y).
Proof. exact (@lem19158 (term685 x) (term674 y) (term707 y)). Qed.
Lemma lem3127680 (y : int) : (term713 y) = (term714 y).
Proof. exact (@lem19367 (term573 y) (term672 y) (term707 y)). Qed.
Lemma lem3127687 (y : int) (x : int) : (term715 y x) = (term716 y x).
Proof. exact (@lem19367 (term573 y) (term672 y) (term685 x)). Qed.
Lemma lem3127688 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3127689 (y : int) (x : int) : (term717 y x) = (term718 y x).
Proof. exact (MK_COMB (@lem3127688) (@lem3127687 y x)). Qed.
Lemma lem3127690 (x : int) (y : int) : (term712 x y) = (term719 x y).
Proof. exact (MK_COMB (@lem3127689 y x) (@lem3127680 y)). Qed.
Lemma lem3127692 (x : int) (y : int) : (term711 x y) = (term719 x y).
Proof. exact (TRANS (@lem3127673 x y) (@lem3127690 x y)). Qed.
Lemma lem3127693 (x : int) (y : int) : (term659 x y) = (term719 x y).
Proof. exact (TRANS (@lem3127659 x y) (@lem3127692 x y)). Qed.
Lemma lem3127695 (a : real) (x : real) (r : real) : (term357 x a r) = (term358 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem3127696 (x : int) : (term685 x) = (term720 x).
Proof. exact (@lem3127695 term321 (real_of_int x) term296). Qed.
Lemma lem3127703 (x : int) : (term360 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem3127706 : term412 = term412.
Proof. exact (eq_refl term412). Qed.
Lemma lem3127707 (x : int) : (term721 x) = (term722 x).
Proof. exact (MK_COMB (@lem3127706) (@lem3127703 x)). Qed.
Lemma lem3127708 (x : int) : (term722 x) = (term669 x).
Proof. exact (@lem1982761 (real_of_int x) term321). Qed.
Lemma lem3127709 (x : int) : (term721 x) = (term669 x).
Proof. exact (TRANS (@lem3127707 x) (@lem3127708 x)). Qed.
Lemma lem3127710 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3127711 (x : int) : (term723 x) = (term671 x).
Proof. exact (MK_COMB (@lem3127710) (@lem3127709 x)). Qed.
Lemma lem3127712 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3127713 (x : int) : (term724 x) = (term672 x).
Proof. exact (MK_COMB (@lem3127711 x) (@lem3127712)). Qed.
Lemma lem3127726 (x : int) : (term725 x) = (term348 x).
Proof. exact (@lem1982761 (term369 x) term321). Qed.
Lemma lem3127727 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3127728 (x : int) : (term726 x) = (term571 x).
Proof. exact (MK_COMB (@lem3127727) (@lem3127726 x)). Qed.
Lemma lem3127729 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3127730 (x : int) : (term727 x) = (term573 x).
Proof. exact (MK_COMB (@lem3127728 x) (@lem3127729)). Qed.
Lemma lem3127731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3127732 (x : int) : (term728 x) = (term578 x).
Proof. exact (MK_COMB (@lem3127731) (@lem3127730 x)). Qed.
Lemma lem3127733 (x : int) : (term720 x) = (term729 x).
Proof. exact (MK_COMB (@lem3127732 x) (@lem3127713 x)). Qed.
Lemma lem3127734 (x : int) : (term685 x) = (term729 x).
Proof. exact (TRANS (@lem3127696 x) (@lem3127733 x)). Qed.
Lemma lem3127735 (y : int) : (term578 y) = (term578 y).
Proof. exact (eq_refl (term578 y)). Qed.
Lemma lem3127738 (y : int) (x : int) : (term730 y x) = (term731 y x).
Proof. exact (MK_COMB (@lem3127735 y) (@lem3127734 x)). Qed.
Lemma lem3127740 (a : real) (x : real) (r : real) : (term357 x a r) = (term358 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem3127741 (x : int) : (term685 x) = (term720 x).
Proof. exact (@lem3127740 term321 (real_of_int x) term296). Qed.
Lemma lem3127748 (x : int) : (term360 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem3127751 : term412 = term412.
Proof. exact (eq_refl term412). Qed.
Lemma lem3127752 (x : int) : (term721 x) = (term722 x).
Proof. exact (MK_COMB (@lem3127751) (@lem3127748 x)). Qed.
Lemma lem3127753 (x : int) : (term722 x) = (term669 x).
Proof. exact (@lem1982761 (real_of_int x) term321). Qed.
Lemma lem3127754 (x : int) : (term721 x) = (term669 x).
Proof. exact (TRANS (@lem3127752 x) (@lem3127753 x)). Qed.
Lemma lem3127755 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3127756 (x : int) : (term723 x) = (term671 x).
Proof. exact (MK_COMB (@lem3127755) (@lem3127754 x)). Qed.
Lemma lem3127757 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3127758 (x : int) : (term724 x) = (term672 x).
Proof. exact (MK_COMB (@lem3127756 x) (@lem3127757)). Qed.
Lemma lem3127771 (x : int) : (term725 x) = (term348 x).
Proof. exact (@lem1982761 (term369 x) term321). Qed.
Lemma lem3127772 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3127773 (x : int) : (term726 x) = (term571 x).
Proof. exact (MK_COMB (@lem3127772) (@lem3127771 x)). Qed.
Lemma lem3127774 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3127775 (x : int) : (term727 x) = (term573 x).
Proof. exact (MK_COMB (@lem3127773 x) (@lem3127774)). Qed.
Lemma lem3127776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3127777 (x : int) : (term728 x) = (term578 x).
Proof. exact (MK_COMB (@lem3127776) (@lem3127775 x)). Qed.
Lemma lem3127778 (x : int) : (term720 x) = (term729 x).
Proof. exact (MK_COMB (@lem3127777 x) (@lem3127758 x)). Qed.
Lemma lem3127779 (x : int) : (term685 x) = (term729 x).
Proof. exact (TRANS (@lem3127741 x) (@lem3127778 x)). Qed.
Lemma lem3127780 (y : int) : (term732 y) = (term732 y).
Proof. exact (eq_refl (term732 y)). Qed.
Lemma lem3127783 (y : int) (x : int) : (term733 y x) = (term734 y x).
Proof. exact (MK_COMB (@lem3127780 y) (@lem3127779 x)). Qed.
Lemma lem3127784 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3127785 (y : int) (x : int) : (term735 y x) = (term736 y x).
Proof. exact (MK_COMB (@lem3127784) (@lem3127738 y x)). Qed.
Lemma lem3127786 (y : int) (x : int) : (term716 y x) = (term737 y x).
Proof. exact (MK_COMB (@lem3127785 y x) (@lem3127783 y x)). Qed.
Lemma lem3127788 (x : real) (r : real) : (term738 x r) = (term739 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem3127789 (y : int) : (term707 y) = (term740 y).
Proof. exact (@lem3127788 (real_of_int y) term296). Qed.
Lemma lem3127796 (y : int) : (term360 y) = (real_of_int y).
Proof. exact (@lem1982733 (real_of_int y)). Qed.
Lemma lem3127797 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3127798 (y : int) : (term585 y) = (term542 y).
Proof. exact (MK_COMB (@lem3127797) (@lem3127796 y)). Qed.
Lemma lem3127799 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3127800 (y : int) : (term584 y) = (term543 y).
Proof. exact (MK_COMB (@lem3127798 y) (@lem3127799)). Qed.
Lemma lem3127813 (y : int) : (term741 y) = (term741 y).
Proof. exact (eq_refl (term741 y)). Qed.
Lemma lem3127814 (y : int) : (term740 y) = (term742 y).
Proof. exact (MK_COMB (@lem3127813 y) (@lem3127800 y)). Qed.
Lemma lem3127815 (y : int) : (term707 y) = (term742 y).
Proof. exact (TRANS (@lem3127789 y) (@lem3127814 y)). Qed.
Lemma lem3127816 (y : int) : (term578 y) = (term578 y).
Proof. exact (eq_refl (term578 y)). Qed.
Lemma lem3127819 (y : int) : (term743 y) = (term744 y).
Proof. exact (MK_COMB (@lem3127816 y) (@lem3127815 y)). Qed.
Lemma lem3127821 (x : real) (r : real) : (term738 x r) = (term739 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem3127822 (y : int) : (term707 y) = (term740 y).
Proof. exact (@lem3127821 (real_of_int y) term296). Qed.
Lemma lem3127829 (y : int) : (term360 y) = (real_of_int y).
Proof. exact (@lem1982733 (real_of_int y)). Qed.
Lemma lem3127830 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3127831 (y : int) : (term585 y) = (term542 y).
Proof. exact (MK_COMB (@lem3127830) (@lem3127829 y)). Qed.
Lemma lem3127832 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3127833 (y : int) : (term584 y) = (term543 y).
Proof. exact (MK_COMB (@lem3127831 y) (@lem3127832)). Qed.
Lemma lem3127846 (y : int) : (term741 y) = (term741 y).
Proof. exact (eq_refl (term741 y)). Qed.
Lemma lem3127847 (y : int) : (term740 y) = (term742 y).
Proof. exact (MK_COMB (@lem3127846 y) (@lem3127833 y)). Qed.
Lemma lem3127848 (y : int) : (term707 y) = (term742 y).
Proof. exact (TRANS (@lem3127822 y) (@lem3127847 y)). Qed.
Lemma lem3127849 (y : int) : (term732 y) = (term732 y).
Proof. exact (eq_refl (term732 y)). Qed.
Lemma lem3127852 (y : int) : (term745 y) = (term746 y).
Proof. exact (MK_COMB (@lem3127849 y) (@lem3127848 y)). Qed.
Lemma lem3127853 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3127854 (y : int) : (term747 y) = (term748 y).
Proof. exact (MK_COMB (@lem3127853) (@lem3127819 y)). Qed.
Lemma lem3127855 (y : int) : (term714 y) = (term749 y).
Proof. exact (MK_COMB (@lem3127854 y) (@lem3127852 y)). Qed.
Lemma lem3127856 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3127857 (y : int) (x : int) : (term718 y x) = (term750 y x).
Proof. exact (MK_COMB (@lem3127856) (@lem3127786 y x)). Qed.
Lemma lem3127858 (x : int) (y : int) : (term719 x y) = (term751 x y).
Proof. exact (MK_COMB (@lem3127857 y x) (@lem3127855 y)). Qed.
Lemma lem3127859 (x : int) (y : int) (h1 : term751 x y) : term751 x y.
Proof. exact (h1). Qed.
Lemma lem3127860 (y : int) (x : int) (h1 : term737 y x) : term737 y x.
Proof. exact (h1). Qed.
Lemma lem3127861 (y : int) (x : int) (h1 : term731 y x) : term731 y x.
Proof. exact (h1). Qed.
Lemma lem3127862 (y : int) (x : int) (h1 : term731 y x) : term729 x.
Proof. exact (proj2 (@lem3127861 y x h1)). Qed.
Lemma lem3127864 (y : int) (x : int) (h1 : term731 y x) : term672 x.
Proof. exact (proj2 (@lem3127862 y x h1)). Qed.
Lemma lem3127865 (y : int) (x : int) (h1 : term731 y x) : term573 x.
Proof. exact (proj1 (@lem3127862 y x h1)). Qed.
Lemma lem3127867 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3127868 : term379 = term380.
Proof. exact (@lem3127867 term296 term275). Qed.
Lemma lem3127870 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3127871 : term275 = term326.
Proof. exact (@lem3127870 term22). Qed.
Lemma lem3127873 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3127874 : term296 = term381.
Proof. exact (@lem3127873 (NUMERAL 0)). Qed.
Lemma lem3127875 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3127876 : term382 = term383.
Proof. exact (MK_COMB (@lem3127875) (@lem3127874)). Qed.
Lemma lem3127877 : term380 = term384.
Proof. exact (MK_COMB (@lem3127876) (@lem3127871)). Qed.
Lemma lem3127878 : term385.
Proof. exact (@lem1980255 term296 term275 term275 term275). Qed.
Lemma lem3127880 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3127881 : term380 = term387.
Proof. exact (@lem3127880 (NUMERAL 0) term22). Qed.
Lemma lem3127882 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3127883 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3127884 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3127883 h1) (fun h1 : term387 = True => @lem3127882)). Qed.
Lemma lem3127885 : term387 = True.
Proof. exact (EQ_MP (@lem3127884) (@lem3127882)). Qed.
Lemma lem3127886 : term380 = True.
Proof. exact (TRANS (@lem3127881) (@lem3127885)). Qed.
Lemma lem3127887 : True = term380.
Proof. exact (SYM (@lem3127886)). Qed.
Lemma lem3127888 : term380.
Proof. exact (EQ_MP (@lem3127887) (@lem0)). Qed.
Lemma lem3127889 : term388.
Proof. exact (@lem3127878 (@lem3127888)). Qed.
Lemma lem3127891 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3127892 : term380 = term387.
Proof. exact (@lem3127891 (NUMERAL 0) term22). Qed.
Lemma lem3127893 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3127894 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3127895 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3127894 h1) (fun h1 : term387 = True => @lem3127893)). Qed.
Lemma lem3127896 : term387 = True.
Proof. exact (EQ_MP (@lem3127895) (@lem3127893)). Qed.
Lemma lem3127897 : term380 = True.
Proof. exact (TRANS (@lem3127892) (@lem3127896)). Qed.
Lemma lem3127898 : True = term380.
Proof. exact (SYM (@lem3127897)). Qed.
Lemma lem3127899 : term380.
Proof. exact (EQ_MP (@lem3127898) (@lem0)). Qed.
Lemma lem3127900 : term384 = term389.
Proof. exact (@lem3127889 (@lem3127899)). Qed.
Lemma lem3127902 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3127903 : term337 = term338.
Proof. exact (@lem3127902 term22 term22). Qed.
Lemma lem3127904 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127905 : term340 = term22.
Proof. exact (EQ_MP (@lem3127904) (@lem940073)). Qed.
Lemma lem3127906 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127907 : term338 = term275.
Proof. exact (MK_COMB (@lem3127906) (@lem3127905)). Qed.
Lemma lem3127908 : term337 = term275.
Proof. exact (TRANS (@lem3127903) (@lem3127907)). Qed.
Lemma lem3127910 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3127911 : term391 = term296.
Proof. exact (@lem3127910 term22). Qed.
Lemma lem3127912 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3127913 : term392 = term382.
Proof. exact (MK_COMB (@lem3127912) (@lem3127911)). Qed.
Lemma lem3127914 : term389 = term380.
Proof. exact (MK_COMB (@lem3127913) (@lem3127908)). Qed.
Lemma lem3127916 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3127917 : term380 = term387.
Proof. exact (@lem3127916 (NUMERAL 0) term22). Qed.
Lemma lem3127918 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3127919 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3127920 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3127919 h1) (fun h1 : term387 = True => @lem3127918)). Qed.
Lemma lem3127921 : term387 = True.
Proof. exact (EQ_MP (@lem3127920) (@lem3127918)). Qed.
Lemma lem3127922 : term380 = True.
Proof. exact (TRANS (@lem3127917) (@lem3127921)). Qed.
Lemma lem3127923 : term389 = True.
Proof. exact (TRANS (@lem3127914) (@lem3127922)). Qed.
Lemma lem3127924 : term384 = True.
Proof. exact (TRANS (@lem3127900) (@lem3127923)). Qed.
Lemma lem3127925 : term380 = True.
Proof. exact (TRANS (@lem3127877) (@lem3127924)). Qed.
Lemma lem3127926 : term379 = True.
Proof. exact (TRANS (@lem3127868) (@lem3127925)). Qed.
Lemma lem3127927 : True = term379.
Proof. exact (SYM (@lem3127926)). Qed.
Lemma lem3127928 : term379.
Proof. exact (EQ_MP (@lem3127927) (@lem0)). Qed.
Lemma lem3127929 (y : int) (x : int) (h1 : term731 y x) : term752 x.
Proof. exact (conj (@lem3127928) (@lem3127864 y x h1)). Qed.
Lemma lem3127931 (x : real) (y : real) : term394 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3127932 (x : int) : term753 x.
Proof. exact (@lem3127931 term275 (term669 x)). Qed.
Lemma lem3127933 (y : int) (x : int) (h1 : term731 y x) : term754 x.
Proof. exact (@lem3127932 x (@lem3127929 y x h1)). Qed.
Lemma lem3127934 (x : int) : (term755 x) = (term669 x).
Proof. exact (@lem1982733 (term669 x)). Qed.
Lemma lem3127935 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3127936 (x : int) : (term756 x) = (term671 x).
Proof. exact (MK_COMB (@lem3127935) (@lem3127934 x)). Qed.
Lemma lem3127937 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3127938 (x : int) : (term754 x) = (term672 x).
Proof. exact (MK_COMB (@lem3127936 x) (@lem3127937)). Qed.
Lemma lem3127939 (y : int) (x : int) (h1 : term731 y x) : term672 x.
Proof. exact (EQ_MP (@lem3127938 x) (@lem3127933 y x h1)). Qed.
Lemma lem3127941 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3127942 : term379 = term380.
Proof. exact (@lem3127941 term296 term275). Qed.
Lemma lem3127944 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3127945 : term275 = term326.
Proof. exact (@lem3127944 term22). Qed.
Lemma lem3127947 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3127948 : term296 = term381.
Proof. exact (@lem3127947 (NUMERAL 0)). Qed.
Lemma lem3127949 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3127950 : term382 = term383.
Proof. exact (MK_COMB (@lem3127949) (@lem3127948)). Qed.
Lemma lem3127951 : term380 = term384.
Proof. exact (MK_COMB (@lem3127950) (@lem3127945)). Qed.
Lemma lem3127952 : term385.
Proof. exact (@lem1980255 term296 term275 term275 term275). Qed.
Lemma lem3127954 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3127955 : term380 = term387.
Proof. exact (@lem3127954 (NUMERAL 0) term22). Qed.
Lemma lem3127956 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3127957 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3127958 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3127957 h1) (fun h1 : term387 = True => @lem3127956)). Qed.
Lemma lem3127959 : term387 = True.
Proof. exact (EQ_MP (@lem3127958) (@lem3127956)). Qed.
Lemma lem3127960 : term380 = True.
Proof. exact (TRANS (@lem3127955) (@lem3127959)). Qed.
Lemma lem3127961 : True = term380.
Proof. exact (SYM (@lem3127960)). Qed.
Lemma lem3127962 : term380.
Proof. exact (EQ_MP (@lem3127961) (@lem0)). Qed.
Lemma lem3127963 : term388.
Proof. exact (@lem3127952 (@lem3127962)). Qed.
Lemma lem3127965 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3127966 : term380 = term387.
Proof. exact (@lem3127965 (NUMERAL 0) term22). Qed.
Lemma lem3127967 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3127968 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3127969 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3127968 h1) (fun h1 : term387 = True => @lem3127967)). Qed.
Lemma lem3127970 : term387 = True.
Proof. exact (EQ_MP (@lem3127969) (@lem3127967)). Qed.
Lemma lem3127971 : term380 = True.
Proof. exact (TRANS (@lem3127966) (@lem3127970)). Qed.
Lemma lem3127972 : True = term380.
Proof. exact (SYM (@lem3127971)). Qed.
Lemma lem3127973 : term380.
Proof. exact (EQ_MP (@lem3127972) (@lem0)). Qed.
Lemma lem3127974 : term384 = term389.
Proof. exact (@lem3127963 (@lem3127973)). Qed.
Lemma lem3127976 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3127977 : term337 = term338.
Proof. exact (@lem3127976 term22 term22). Qed.
Lemma lem3127978 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3127979 : term340 = term22.
Proof. exact (EQ_MP (@lem3127978) (@lem940073)). Qed.
Lemma lem3127980 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3127981 : term338 = term275.
Proof. exact (MK_COMB (@lem3127980) (@lem3127979)). Qed.
Lemma lem3127982 : term337 = term275.
Proof. exact (TRANS (@lem3127977) (@lem3127981)). Qed.
Lemma lem3127984 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3127985 : term391 = term296.
Proof. exact (@lem3127984 term22). Qed.
Lemma lem3127986 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3127987 : term392 = term382.
Proof. exact (MK_COMB (@lem3127986) (@lem3127985)). Qed.
Lemma lem3127988 : term389 = term380.
Proof. exact (MK_COMB (@lem3127987) (@lem3127982)). Qed.
Lemma lem3127990 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3127991 : term380 = term387.
Proof. exact (@lem3127990 (NUMERAL 0) term22). Qed.
Lemma lem3127992 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3127993 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3127994 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3127993 h1) (fun h1 : term387 = True => @lem3127992)). Qed.
Lemma lem3127995 : term387 = True.
Proof. exact (EQ_MP (@lem3127994) (@lem3127992)). Qed.
Lemma lem3127996 : term380 = True.
Proof. exact (TRANS (@lem3127991) (@lem3127995)). Qed.
Lemma lem3127997 : term389 = True.
Proof. exact (TRANS (@lem3127988) (@lem3127996)). Qed.
Lemma lem3127998 : term384 = True.
Proof. exact (TRANS (@lem3127974) (@lem3127997)). Qed.
Lemma lem3127999 : term380 = True.
Proof. exact (TRANS (@lem3127951) (@lem3127998)). Qed.
Lemma lem3128000 : term379 = True.
Proof. exact (TRANS (@lem3127942) (@lem3127999)). Qed.
Lemma lem3128001 : True = term379.
Proof. exact (SYM (@lem3128000)). Qed.
Lemma lem3128002 : term379.
Proof. exact (EQ_MP (@lem3128001) (@lem0)). Qed.
Lemma lem3128003 (y : int) (x : int) (h1 : term731 y x) : term586 x.
Proof. exact (conj (@lem3128002) (@lem3127865 y x h1)). Qed.
Lemma lem3128005 (x : real) (y : real) : term394 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3128006 (x : int) : term587 x.
Proof. exact (@lem3128005 term275 (term348 x)). Qed.
Lemma lem3128007 (y : int) (x : int) (h1 : term731 y x) : term588 x.
Proof. exact (@lem3128006 x (@lem3128003 y x h1)). Qed.
Lemma lem3128008 (x : int) : (term589 x) = (term348 x).
Proof. exact (@lem1982733 (term348 x)). Qed.
Lemma lem3128009 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3128010 (x : int) : (term590 x) = (term571 x).
Proof. exact (MK_COMB (@lem3128009) (@lem3128008 x)). Qed.
Lemma lem3128011 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3128012 (x : int) : (term588 x) = (term573 x).
Proof. exact (MK_COMB (@lem3128010 x) (@lem3128011)). Qed.
Lemma lem3128013 (y : int) (x : int) (h1 : term731 y x) : term573 x.
Proof. exact (EQ_MP (@lem3128012 x) (@lem3128007 y x h1)). Qed.
Lemma lem3128014 (y : int) (x : int) (h1 : term731 y x) : term729 x.
Proof. exact (conj (@lem3128013 y x h1) (@lem3127939 y x h1)). Qed.
Lemma lem3128016 (x : real) (y : real) : term405 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3128017 (x : int) : term757 x.
Proof. exact (@lem3128016 (term348 x) (term669 x)). Qed.
Lemma lem3128018 (y : int) (x : int) (h1 : term731 y x) : term758 x.
Proof. exact (@lem3128017 x (@lem3128014 y x h1)). Qed.
Lemma lem3128019 (x : int) : (term759 x) = (term760 x).
Proof. exact (@lem1982753 (term369 x) (real_of_int x) term321 term321). Qed.
Lemma lem3128020 (x : int) : (term410 x) = (term411 x).
Proof. exact (@lem1982713 term321 (real_of_int x)). Qed.
Lemma lem3128022 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128023 : term275 = term326.
Proof. exact (@lem3128022 term22). Qed.
Lemma lem3128025 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3128026 : term321 = term329.
Proof. exact (@lem3128025 term22). Qed.
Lemma lem3128027 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3128028 : term412 = term413.
Proof. exact (MK_COMB (@lem3128027) (@lem3128026)). Qed.
Lemma lem3128029 : term414 = term415.
Proof. exact (MK_COMB (@lem3128028) (@lem3128023)). Qed.
Lemma lem3128030 : term416.
Proof. exact (@lem1981473 term321 term275 term275 term275 term296 term275). Qed.
Lemma lem3128032 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128033 : term380 = term387.
Proof. exact (@lem3128032 (NUMERAL 0) term22). Qed.
Lemma lem3128034 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128035 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128036 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128035 h1) (fun h1 : term387 = True => @lem3128034)). Qed.
Lemma lem3128037 : term387 = True.
Proof. exact (EQ_MP (@lem3128036) (@lem3128034)). Qed.
Lemma lem3128038 : term380 = True.
Proof. exact (TRANS (@lem3128033) (@lem3128037)). Qed.
Lemma lem3128039 : True = term380.
Proof. exact (SYM (@lem3128038)). Qed.
Lemma lem3128040 : term380.
Proof. exact (EQ_MP (@lem3128039) (@lem0)). Qed.
Lemma lem3128041 : term417.
Proof. exact (@lem3128030 (@lem3128040)). Qed.
Lemma lem3128043 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128044 : term380 = term387.
Proof. exact (@lem3128043 (NUMERAL 0) term22). Qed.
Lemma lem3128045 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128046 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128047 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128046 h1) (fun h1 : term387 = True => @lem3128045)). Qed.
Lemma lem3128048 : term387 = True.
Proof. exact (EQ_MP (@lem3128047) (@lem3128045)). Qed.
Lemma lem3128049 : term380 = True.
Proof. exact (TRANS (@lem3128044) (@lem3128048)). Qed.
Lemma lem3128050 : True = term380.
Proof. exact (SYM (@lem3128049)). Qed.
Lemma lem3128051 : term380.
Proof. exact (EQ_MP (@lem3128050) (@lem0)). Qed.
Lemma lem3128052 : term418.
Proof. exact (@lem3128041 (@lem3128051)). Qed.
Lemma lem3128054 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128055 : term380 = term387.
Proof. exact (@lem3128054 (NUMERAL 0) term22). Qed.
Lemma lem3128056 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128057 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128058 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128057 h1) (fun h1 : term387 = True => @lem3128056)). Qed.
Lemma lem3128059 : term387 = True.
Proof. exact (EQ_MP (@lem3128058) (@lem3128056)). Qed.
Lemma lem3128060 : term380 = True.
Proof. exact (TRANS (@lem3128055) (@lem3128059)). Qed.
Lemma lem3128061 : True = term380.
Proof. exact (SYM (@lem3128060)). Qed.
Lemma lem3128062 : term380.
Proof. exact (EQ_MP (@lem3128061) (@lem0)). Qed.
Lemma lem3128063 : term419.
Proof. exact (@lem3128052 (@lem3128062)). Qed.
Lemma lem3128065 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3128066 : term337 = term338.
Proof. exact (@lem3128065 term22 term22). Qed.
Lemma lem3128067 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128068 : term340 = term22.
Proof. exact (EQ_MP (@lem3128067) (@lem940073)). Qed.
Lemma lem3128069 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128070 : term338 = term275.
Proof. exact (MK_COMB (@lem3128069) (@lem3128068)). Qed.
Lemma lem3128071 : term337 = term275.
Proof. exact (TRANS (@lem3128066) (@lem3128070)). Qed.
Lemma lem3128073 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3128074 : term332 = term343.
Proof. exact (@lem3128073 term22 term22). Qed.
Lemma lem3128075 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128076 : term340 = term22.
Proof. exact (EQ_MP (@lem3128075) (@lem940073)). Qed.
Lemma lem3128077 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128078 : term338 = term275.
Proof. exact (MK_COMB (@lem3128077) (@lem3128076)). Qed.
Lemma lem3128079 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128080 : term343 = term321.
Proof. exact (MK_COMB (@lem3128079) (@lem3128078)). Qed.
Lemma lem3128081 : term332 = term321.
Proof. exact (TRANS (@lem3128074) (@lem3128080)). Qed.
Lemma lem3128082 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3128083 : term420 = term412.
Proof. exact (MK_COMB (@lem3128082) (@lem3128081)). Qed.
Lemma lem3128084 : term421 = term414.
Proof. exact (MK_COMB (@lem3128083) (@lem3128071)). Qed.
Lemma lem3128086 (m : nat) : (term422 m) = term296.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3128087 : term414 = term296.
Proof. exact (@lem3128086 term22). Qed.
Lemma lem3128088 : term421 = term296.
Proof. exact (TRANS (@lem3128084) (@lem3128087)). Qed.
Lemma lem3128089 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3128090 : term423 = term424.
Proof. exact (MK_COMB (@lem3128089) (@lem3128088)). Qed.
Lemma lem3128091 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem3128092 : term425 = term391.
Proof. exact (MK_COMB (@lem3128090) (@lem3128091)). Qed.
Lemma lem3128094 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3128095 : term391 = term296.
Proof. exact (@lem3128094 term22). Qed.
Lemma lem3128096 : term425 = term296.
Proof. exact (TRANS (@lem3128092) (@lem3128095)). Qed.
Lemma lem3128098 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3128099 : term337 = term338.
Proof. exact (@lem3128098 term22 term22). Qed.
Lemma lem3128100 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128101 : term340 = term22.
Proof. exact (EQ_MP (@lem3128100) (@lem940073)). Qed.
Lemma lem3128102 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128103 : term338 = term275.
Proof. exact (MK_COMB (@lem3128102) (@lem3128101)). Qed.
Lemma lem3128104 : term337 = term275.
Proof. exact (TRANS (@lem3128099) (@lem3128103)). Qed.
Lemma lem3128105 : term424 = term424.
Proof. exact (eq_refl term424). Qed.
Lemma lem3128106 : term426 = term391.
Proof. exact (MK_COMB (@lem3128105) (@lem3128104)). Qed.
Lemma lem3128108 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3128109 : term391 = term296.
Proof. exact (@lem3128108 term22). Qed.
Lemma lem3128110 : term426 = term296.
Proof. exact (TRANS (@lem3128106) (@lem3128109)). Qed.
Lemma lem3128111 : term296 = term426.
Proof. exact (SYM (@lem3128110)). Qed.
Lemma lem3128112 : term425 = term426.
Proof. exact (TRANS (@lem3128096) (@lem3128111)). Qed.
Lemma lem3128113 : term415 = term381.
Proof. exact (@lem3128063 (@lem3128112)). Qed.
Lemma lem3128114 : term414 = term381.
Proof. exact (TRANS (@lem3128029) (@lem3128113)). Qed.
Lemma lem3128116 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3128117 : term381 = term296.
Proof. exact (@lem3128116 term296). Qed.
Lemma lem3128118 : term414 = term296.
Proof. exact (TRANS (@lem3128114) (@lem3128117)). Qed.
Lemma lem3128119 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3128120 : term427 = term424.
Proof. exact (MK_COMB (@lem3128119) (@lem3128118)). Qed.
Lemma lem3128121 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3128122 (x : int) : (term411 x) = (term428 x).
Proof. exact (MK_COMB (@lem3128120) (@lem3128121 x)). Qed.
Lemma lem3128123 (x : int) : (term410 x) = (term428 x).
Proof. exact (TRANS (@lem3128020 x) (@lem3128122 x)). Qed.
Lemma lem3128124 (x : int) : (term428 x) = term296.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem3128125 (x : int) : (term410 x) = term296.
Proof. exact (TRANS (@lem3128123 x) (@lem3128124 x)). Qed.
Lemma lem3128126 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3128127 (x : int) : (term429 x) = term350.
Proof. exact (MK_COMB (@lem3128126) (@lem3128125 x)). Qed.
Lemma lem3128129 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3128130 : term321 = term329.
Proof. exact (@lem3128129 term22). Qed.
Lemma lem3128132 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3128133 : term321 = term329.
Proof. exact (@lem3128132 term22). Qed.
Lemma lem3128134 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3128135 : term412 = term413.
Proof. exact (MK_COMB (@lem3128134) (@lem3128133)). Qed.
Lemma lem3128136 : term761 = term762.
Proof. exact (MK_COMB (@lem3128135) (@lem3128130)). Qed.
Lemma lem3128137 : term763.
Proof. exact (@lem1981473 term321 term275 term321 term275 term764 term275). Qed.
Lemma lem3128139 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128140 : term380 = term387.
Proof. exact (@lem3128139 (NUMERAL 0) term22). Qed.
Lemma lem3128141 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128142 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128143 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128142 h1) (fun h1 : term387 = True => @lem3128141)). Qed.
Lemma lem3128144 : term387 = True.
Proof. exact (EQ_MP (@lem3128143) (@lem3128141)). Qed.
Lemma lem3128145 : term380 = True.
Proof. exact (TRANS (@lem3128140) (@lem3128144)). Qed.
Lemma lem3128146 : True = term380.
Proof. exact (SYM (@lem3128145)). Qed.
Lemma lem3128147 : term380.
Proof. exact (EQ_MP (@lem3128146) (@lem0)). Qed.
Lemma lem3128148 : term765.
Proof. exact (@lem3128137 (@lem3128147)). Qed.
Lemma lem3128150 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128151 : term380 = term387.
Proof. exact (@lem3128150 (NUMERAL 0) term22). Qed.
Lemma lem3128152 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128153 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128154 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128153 h1) (fun h1 : term387 = True => @lem3128152)). Qed.
Lemma lem3128155 : term387 = True.
Proof. exact (EQ_MP (@lem3128154) (@lem3128152)). Qed.
Lemma lem3128156 : term380 = True.
Proof. exact (TRANS (@lem3128151) (@lem3128155)). Qed.
Lemma lem3128157 : True = term380.
Proof. exact (SYM (@lem3128156)). Qed.
Lemma lem3128158 : term380.
Proof. exact (EQ_MP (@lem3128157) (@lem0)). Qed.
Lemma lem3128159 : term766.
Proof. exact (@lem3128148 (@lem3128158)). Qed.
Lemma lem3128161 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128162 : term380 = term387.
Proof. exact (@lem3128161 (NUMERAL 0) term22). Qed.
Lemma lem3128163 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128164 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128165 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128164 h1) (fun h1 : term387 = True => @lem3128163)). Qed.
Lemma lem3128166 : term387 = True.
Proof. exact (EQ_MP (@lem3128165) (@lem3128163)). Qed.
Lemma lem3128167 : term380 = True.
Proof. exact (TRANS (@lem3128162) (@lem3128166)). Qed.
Lemma lem3128168 : True = term380.
Proof. exact (SYM (@lem3128167)). Qed.
Lemma lem3128169 : term380.
Proof. exact (EQ_MP (@lem3128168) (@lem0)). Qed.
Lemma lem3128170 : term767.
Proof. exact (@lem3128159 (@lem3128169)). Qed.
Lemma lem3128172 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3128173 : term332 = term343.
Proof. exact (@lem3128172 term22 term22). Qed.
Lemma lem3128174 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128175 : term340 = term22.
Proof. exact (EQ_MP (@lem3128174) (@lem940073)). Qed.
Lemma lem3128176 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128177 : term338 = term275.
Proof. exact (MK_COMB (@lem3128176) (@lem3128175)). Qed.
Lemma lem3128178 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128179 : term343 = term321.
Proof. exact (MK_COMB (@lem3128178) (@lem3128177)). Qed.
Lemma lem3128180 : term332 = term321.
Proof. exact (TRANS (@lem3128173) (@lem3128179)). Qed.
Lemma lem3128182 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3128183 : term332 = term343.
Proof. exact (@lem3128182 term22 term22). Qed.
Lemma lem3128184 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128185 : term340 = term22.
Proof. exact (EQ_MP (@lem3128184) (@lem940073)). Qed.
Lemma lem3128186 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128187 : term338 = term275.
Proof. exact (MK_COMB (@lem3128186) (@lem3128185)). Qed.
Lemma lem3128188 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128189 : term343 = term321.
Proof. exact (MK_COMB (@lem3128188) (@lem3128187)). Qed.
Lemma lem3128190 : term332 = term321.
Proof. exact (TRANS (@lem3128183) (@lem3128189)). Qed.
Lemma lem3128191 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3128192 : term420 = term412.
Proof. exact (MK_COMB (@lem3128191) (@lem3128190)). Qed.
Lemma lem3128193 : term768 = term761.
Proof. exact (MK_COMB (@lem3128192) (@lem3128180)). Qed.
Lemma lem3128194 : term761 = term769.
Proof. exact (@lem1367763 term22 term22). Qed.
Lemma lem3128195 : term770 = term771.
Proof. exact (@lem706885). Qed.
Lemma lem3128196 : (term770 = term771) = (term772 = term773).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term771). Qed.
Lemma lem3128197 : term772 = term773.
Proof. exact (EQ_MP (@lem3128196) (@lem3128195)). Qed.
Lemma lem3128198 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128199 : term774 = term775.
Proof. exact (MK_COMB (@lem3128198) (@lem3128197)). Qed.
Lemma lem3128200 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128201 : term769 = term764.
Proof. exact (MK_COMB (@lem3128200) (@lem3128199)). Qed.
Lemma lem3128202 : term761 = term764.
Proof. exact (TRANS (@lem3128194) (@lem3128201)). Qed.
Lemma lem3128203 : term768 = term764.
Proof. exact (TRANS (@lem3128193) (@lem3128202)). Qed.
Lemma lem3128204 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3128205 : term776 = term777.
Proof. exact (MK_COMB (@lem3128204) (@lem3128203)). Qed.
Lemma lem3128206 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem3128207 : term778 = term779.
Proof. exact (MK_COMB (@lem3128205) (@lem3128206)). Qed.
Lemma lem3128209 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3128210 : term779 = term780.
Proof. exact (@lem3128209 term773 term22). Qed.
Lemma lem3128211 : term781 = term771.
Proof. exact (@lem996237 term771). Qed.
Lemma lem3128212 : (term781 = term771) = (term782 = term773).
Proof. exact (@lem1007663 term771 (BIT1 0) term771). Qed.
Lemma lem3128213 : term782 = term773.
Proof. exact (EQ_MP (@lem3128212) (@lem3128211)). Qed.
Lemma lem3128214 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128215 : term783 = term775.
Proof. exact (MK_COMB (@lem3128214) (@lem3128213)). Qed.
Lemma lem3128216 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128217 : term780 = term764.
Proof. exact (MK_COMB (@lem3128216) (@lem3128215)). Qed.
Lemma lem3128218 : term779 = term764.
Proof. exact (TRANS (@lem3128210) (@lem3128217)). Qed.
Lemma lem3128219 : term778 = term764.
Proof. exact (TRANS (@lem3128207) (@lem3128218)). Qed.
Lemma lem3128221 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3128222 : term337 = term338.
Proof. exact (@lem3128221 term22 term22). Qed.
Lemma lem3128223 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128224 : term340 = term22.
Proof. exact (EQ_MP (@lem3128223) (@lem940073)). Qed.
Lemma lem3128225 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128226 : term338 = term275.
Proof. exact (MK_COMB (@lem3128225) (@lem3128224)). Qed.
Lemma lem3128227 : term337 = term275.
Proof. exact (TRANS (@lem3128222) (@lem3128226)). Qed.
Lemma lem3128228 : term777 = term777.
Proof. exact (eq_refl term777). Qed.
Lemma lem3128229 : term784 = term779.
Proof. exact (MK_COMB (@lem3128228) (@lem3128227)). Qed.
Lemma lem3128231 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3128232 : term779 = term780.
Proof. exact (@lem3128231 term773 term22). Qed.
Lemma lem3128233 : term781 = term771.
Proof. exact (@lem996237 term771). Qed.
Lemma lem3128234 : (term781 = term771) = (term782 = term773).
Proof. exact (@lem1007663 term771 (BIT1 0) term771). Qed.
Lemma lem3128235 : term782 = term773.
Proof. exact (EQ_MP (@lem3128234) (@lem3128233)). Qed.
Lemma lem3128236 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128237 : term783 = term775.
Proof. exact (MK_COMB (@lem3128236) (@lem3128235)). Qed.
Lemma lem3128238 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128239 : term780 = term764.
Proof. exact (MK_COMB (@lem3128238) (@lem3128237)). Qed.
Lemma lem3128240 : term779 = term764.
Proof. exact (TRANS (@lem3128232) (@lem3128239)). Qed.
Lemma lem3128241 : term784 = term764.
Proof. exact (TRANS (@lem3128229) (@lem3128240)). Qed.
Lemma lem3128242 : term764 = term784.
Proof. exact (SYM (@lem3128241)). Qed.
Lemma lem3128243 : term778 = term784.
Proof. exact (TRANS (@lem3128219) (@lem3128242)). Qed.
Lemma lem3128244 : term762 = term785.
Proof. exact (@lem3128170 (@lem3128243)). Qed.
Lemma lem3128245 : term761 = term785.
Proof. exact (TRANS (@lem3128136) (@lem3128244)). Qed.
Lemma lem3128247 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3128248 : term785 = term764.
Proof. exact (@lem3128247 term764). Qed.
Lemma lem3128249 : term761 = term764.
Proof. exact (TRANS (@lem3128245) (@lem3128248)). Qed.
Lemma lem3128250 (x : int) : (term760 x) = term786.
Proof. exact (MK_COMB (@lem3128127 x) (@lem3128249)). Qed.
Lemma lem3128251 (x : int) : (term759 x) = term786.
Proof. exact (TRANS (@lem3128019 x) (@lem3128250 x)). Qed.
Lemma lem3128252 : term786 = term764.
Proof. exact (@lem1982721 term764). Qed.
Lemma lem3128253 (x : int) : (term759 x) = term764.
Proof. exact (TRANS (@lem3128251 x) (@lem3128252)). Qed.
Lemma lem3128254 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3128255 (x : int) : (term787 x) = term788.
Proof. exact (MK_COMB (@lem3128254) (@lem3128253 x)). Qed.
Lemma lem3128256 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3128257 (x : int) : (term758 x) = term789.
Proof. exact (MK_COMB (@lem3128255 x) (@lem3128256)). Qed.
Lemma lem3128258 (y : int) (x : int) (h1 : term731 y x) : term789.
Proof. exact (EQ_MP (@lem3128257 x) (@lem3128018 y x h1)). Qed.
Lemma lem3128260 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3128261 : term789 = term790.
Proof. exact (@lem3128260 term296 term764). Qed.
Lemma lem3128263 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3128264 : term764 = term785.
Proof. exact (@lem3128263 term773). Qed.
Lemma lem3128266 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128267 : term296 = term381.
Proof. exact (@lem3128266 (NUMERAL 0)). Qed.
Lemma lem3128268 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3128269 : term437 = term438.
Proof. exact (MK_COMB (@lem3128268) (@lem3128267)). Qed.
Lemma lem3128270 : term790 = term791.
Proof. exact (MK_COMB (@lem3128269) (@lem3128264)). Qed.
Lemma lem3128271 : term792.
Proof. exact (@lem1980026 term296 term275 term764 term275). Qed.
Lemma lem3128273 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128274 : term380 = term387.
Proof. exact (@lem3128273 (NUMERAL 0) term22). Qed.
Lemma lem3128275 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128276 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128277 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128276 h1) (fun h1 : term387 = True => @lem3128275)). Qed.
Lemma lem3128278 : term387 = True.
Proof. exact (EQ_MP (@lem3128277) (@lem3128275)). Qed.
Lemma lem3128279 : term380 = True.
Proof. exact (TRANS (@lem3128274) (@lem3128278)). Qed.
Lemma lem3128280 : True = term380.
Proof. exact (SYM (@lem3128279)). Qed.
Lemma lem3128281 : term380.
Proof. exact (EQ_MP (@lem3128280) (@lem0)). Qed.
Lemma lem3128282 : term793.
Proof. exact (@lem3128271 (@lem3128281)). Qed.
Lemma lem3128284 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128285 : term380 = term387.
Proof. exact (@lem3128284 (NUMERAL 0) term22). Qed.
Lemma lem3128286 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128287 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128288 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128287 h1) (fun h1 : term387 = True => @lem3128286)). Qed.
Lemma lem3128289 : term387 = True.
Proof. exact (EQ_MP (@lem3128288) (@lem3128286)). Qed.
Lemma lem3128290 : term380 = True.
Proof. exact (TRANS (@lem3128285) (@lem3128289)). Qed.
Lemma lem3128291 : True = term380.
Proof. exact (SYM (@lem3128290)). Qed.
Lemma lem3128292 : term380.
Proof. exact (EQ_MP (@lem3128291) (@lem0)). Qed.
Lemma lem3128293 : term791 = term794.
Proof. exact (@lem3128282 (@lem3128292)). Qed.
Lemma lem3128295 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3128296 : term779 = term780.
Proof. exact (@lem3128295 term773 term22). Qed.
Lemma lem3128297 : term781 = term771.
Proof. exact (@lem996237 term771). Qed.
Lemma lem3128298 : (term781 = term771) = (term782 = term773).
Proof. exact (@lem1007663 term771 (BIT1 0) term771). Qed.
Lemma lem3128299 : term782 = term773.
Proof. exact (EQ_MP (@lem3128298) (@lem3128297)). Qed.
Lemma lem3128300 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128301 : term783 = term775.
Proof. exact (MK_COMB (@lem3128300) (@lem3128299)). Qed.
Lemma lem3128302 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128303 : term780 = term764.
Proof. exact (MK_COMB (@lem3128302) (@lem3128301)). Qed.
Lemma lem3128304 : term779 = term764.
Proof. exact (TRANS (@lem3128296) (@lem3128303)). Qed.
Lemma lem3128306 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3128307 : term391 = term296.
Proof. exact (@lem3128306 term22). Qed.
Lemma lem3128308 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3128309 : term443 = term437.
Proof. exact (MK_COMB (@lem3128308) (@lem3128307)). Qed.
Lemma lem3128310 : term794 = term790.
Proof. exact (MK_COMB (@lem3128309) (@lem3128304)). Qed.
Lemma lem3128312 (m : nat) (n : nat) : (term444 m n) = (term445 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3128313 : term790 = term795.
Proof. exact (@lem3128312 (NUMERAL 0) term773). Qed.
Lemma lem3128314 : term796 = term771.
Proof. exact (@lem912803). Qed.
Lemma lem3128315 (h1 : term796 = term771) : (term773 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term771 h1). Qed.
Lemma lem3128316 : (term796 = term771) = ((term773 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term796 = term771 => @lem3128315 h1) (fun h1 : (term773 = (NUMERAL 0)) = False => @lem3128314)). Qed.
Lemma lem3128317 : (term773 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3128316) (@lem3128314)). Qed.
Lemma lem3128318 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3128319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3128320 : term447 = (and True).
Proof. exact (MK_COMB (@lem3128319) (@lem3128318)). Qed.
Lemma lem3128321 : term795 = (True /\ False).
Proof. exact (MK_COMB (@lem3128320) (@lem3128317)). Qed.
Lemma lem3128323 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3128324 : term795 = False.
Proof. exact (TRANS (@lem3128321) (@lem3128323)). Qed.
Lemma lem3128325 : term790 = False.
Proof. exact (TRANS (@lem3128313) (@lem3128324)). Qed.
Lemma lem3128326 : term794 = False.
Proof. exact (TRANS (@lem3128310) (@lem3128325)). Qed.
Lemma lem3128327 : term791 = False.
Proof. exact (TRANS (@lem3128293) (@lem3128326)). Qed.
Lemma lem3128328 : term790 = False.
Proof. exact (TRANS (@lem3128270) (@lem3128327)). Qed.
Lemma lem3128329 : term789 = False.
Proof. exact (TRANS (@lem3128261) (@lem3128328)). Qed.
Lemma lem3128330 (y : int) (x : int) (h1 : term731 y x) : False.
Proof. exact (EQ_MP (@lem3128329) (@lem3128258 y x h1)). Qed.
Lemma lem3128331 (y : int) (x : int) (h1 : term734 y x) : term734 y x.
Proof. exact (h1). Qed.
Lemma lem3128332 (y : int) (x : int) (h1 : term734 y x) : term729 x.
Proof. exact (proj2 (@lem3128331 y x h1)). Qed.
Lemma lem3128334 (y : int) (x : int) (h1 : term734 y x) : term672 x.
Proof. exact (proj2 (@lem3128332 y x h1)). Qed.
Lemma lem3128335 (y : int) (x : int) (h1 : term734 y x) : term573 x.
Proof. exact (proj1 (@lem3128332 y x h1)). Qed.
Lemma lem3128337 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3128338 : term379 = term380.
Proof. exact (@lem3128337 term296 term275). Qed.
Lemma lem3128340 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128341 : term275 = term326.
Proof. exact (@lem3128340 term22). Qed.
Lemma lem3128343 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128344 : term296 = term381.
Proof. exact (@lem3128343 (NUMERAL 0)). Qed.
Lemma lem3128345 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3128346 : term382 = term383.
Proof. exact (MK_COMB (@lem3128345) (@lem3128344)). Qed.
Lemma lem3128347 : term380 = term384.
Proof. exact (MK_COMB (@lem3128346) (@lem3128341)). Qed.
Lemma lem3128348 : term385.
Proof. exact (@lem1980255 term296 term275 term275 term275). Qed.
Lemma lem3128350 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128351 : term380 = term387.
Proof. exact (@lem3128350 (NUMERAL 0) term22). Qed.
Lemma lem3128352 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128353 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128354 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128353 h1) (fun h1 : term387 = True => @lem3128352)). Qed.
Lemma lem3128355 : term387 = True.
Proof. exact (EQ_MP (@lem3128354) (@lem3128352)). Qed.
Lemma lem3128356 : term380 = True.
Proof. exact (TRANS (@lem3128351) (@lem3128355)). Qed.
Lemma lem3128357 : True = term380.
Proof. exact (SYM (@lem3128356)). Qed.
Lemma lem3128358 : term380.
Proof. exact (EQ_MP (@lem3128357) (@lem0)). Qed.
Lemma lem3128359 : term388.
Proof. exact (@lem3128348 (@lem3128358)). Qed.
Lemma lem3128361 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128362 : term380 = term387.
Proof. exact (@lem3128361 (NUMERAL 0) term22). Qed.
Lemma lem3128363 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128364 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128365 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128364 h1) (fun h1 : term387 = True => @lem3128363)). Qed.
Lemma lem3128366 : term387 = True.
Proof. exact (EQ_MP (@lem3128365) (@lem3128363)). Qed.
Lemma lem3128367 : term380 = True.
Proof. exact (TRANS (@lem3128362) (@lem3128366)). Qed.
Lemma lem3128368 : True = term380.
Proof. exact (SYM (@lem3128367)). Qed.
Lemma lem3128369 : term380.
Proof. exact (EQ_MP (@lem3128368) (@lem0)). Qed.
Lemma lem3128370 : term384 = term389.
Proof. exact (@lem3128359 (@lem3128369)). Qed.
Lemma lem3128372 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3128373 : term337 = term338.
Proof. exact (@lem3128372 term22 term22). Qed.
Lemma lem3128374 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128375 : term340 = term22.
Proof. exact (EQ_MP (@lem3128374) (@lem940073)). Qed.
Lemma lem3128376 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128377 : term338 = term275.
Proof. exact (MK_COMB (@lem3128376) (@lem3128375)). Qed.
Lemma lem3128378 : term337 = term275.
Proof. exact (TRANS (@lem3128373) (@lem3128377)). Qed.
Lemma lem3128380 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3128381 : term391 = term296.
Proof. exact (@lem3128380 term22). Qed.
Lemma lem3128382 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3128383 : term392 = term382.
Proof. exact (MK_COMB (@lem3128382) (@lem3128381)). Qed.
Lemma lem3128384 : term389 = term380.
Proof. exact (MK_COMB (@lem3128383) (@lem3128378)). Qed.
Lemma lem3128386 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128387 : term380 = term387.
Proof. exact (@lem3128386 (NUMERAL 0) term22). Qed.
Lemma lem3128388 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128389 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128390 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128389 h1) (fun h1 : term387 = True => @lem3128388)). Qed.
Lemma lem3128391 : term387 = True.
Proof. exact (EQ_MP (@lem3128390) (@lem3128388)). Qed.
Lemma lem3128392 : term380 = True.
Proof. exact (TRANS (@lem3128387) (@lem3128391)). Qed.
Lemma lem3128393 : term389 = True.
Proof. exact (TRANS (@lem3128384) (@lem3128392)). Qed.
Lemma lem3128394 : term384 = True.
Proof. exact (TRANS (@lem3128370) (@lem3128393)). Qed.
Lemma lem3128395 : term380 = True.
Proof. exact (TRANS (@lem3128347) (@lem3128394)). Qed.
Lemma lem3128396 : term379 = True.
Proof. exact (TRANS (@lem3128338) (@lem3128395)). Qed.
Lemma lem3128397 : True = term379.
Proof. exact (SYM (@lem3128396)). Qed.
Lemma lem3128398 : term379.
Proof. exact (EQ_MP (@lem3128397) (@lem0)). Qed.
Lemma lem3128399 (y : int) (x : int) (h1 : term734 y x) : term752 x.
Proof. exact (conj (@lem3128398) (@lem3128334 y x h1)). Qed.
Lemma lem3128401 (x : real) (y : real) : term394 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3128402 (x : int) : term753 x.
Proof. exact (@lem3128401 term275 (term669 x)). Qed.
Lemma lem3128403 (y : int) (x : int) (h1 : term734 y x) : term754 x.
Proof. exact (@lem3128402 x (@lem3128399 y x h1)). Qed.
Lemma lem3128404 (x : int) : (term755 x) = (term669 x).
Proof. exact (@lem1982733 (term669 x)). Qed.
Lemma lem3128405 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3128406 (x : int) : (term756 x) = (term671 x).
Proof. exact (MK_COMB (@lem3128405) (@lem3128404 x)). Qed.
Lemma lem3128407 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3128408 (x : int) : (term754 x) = (term672 x).
Proof. exact (MK_COMB (@lem3128406 x) (@lem3128407)). Qed.
Lemma lem3128409 (y : int) (x : int) (h1 : term734 y x) : term672 x.
Proof. exact (EQ_MP (@lem3128408 x) (@lem3128403 y x h1)). Qed.
Lemma lem3128411 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3128412 : term379 = term380.
Proof. exact (@lem3128411 term296 term275). Qed.
Lemma lem3128414 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128415 : term275 = term326.
Proof. exact (@lem3128414 term22). Qed.
Lemma lem3128417 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128418 : term296 = term381.
Proof. exact (@lem3128417 (NUMERAL 0)). Qed.
Lemma lem3128419 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3128420 : term382 = term383.
Proof. exact (MK_COMB (@lem3128419) (@lem3128418)). Qed.
Lemma lem3128421 : term380 = term384.
Proof. exact (MK_COMB (@lem3128420) (@lem3128415)). Qed.
Lemma lem3128422 : term385.
Proof. exact (@lem1980255 term296 term275 term275 term275). Qed.
Lemma lem3128424 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128425 : term380 = term387.
Proof. exact (@lem3128424 (NUMERAL 0) term22). Qed.
Lemma lem3128426 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128427 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128428 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128427 h1) (fun h1 : term387 = True => @lem3128426)). Qed.
Lemma lem3128429 : term387 = True.
Proof. exact (EQ_MP (@lem3128428) (@lem3128426)). Qed.
Lemma lem3128430 : term380 = True.
Proof. exact (TRANS (@lem3128425) (@lem3128429)). Qed.
Lemma lem3128431 : True = term380.
Proof. exact (SYM (@lem3128430)). Qed.
Lemma lem3128432 : term380.
Proof. exact (EQ_MP (@lem3128431) (@lem0)). Qed.
Lemma lem3128433 : term388.
Proof. exact (@lem3128422 (@lem3128432)). Qed.
Lemma lem3128435 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128436 : term380 = term387.
Proof. exact (@lem3128435 (NUMERAL 0) term22). Qed.
Lemma lem3128437 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128438 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128439 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128438 h1) (fun h1 : term387 = True => @lem3128437)). Qed.
Lemma lem3128440 : term387 = True.
Proof. exact (EQ_MP (@lem3128439) (@lem3128437)). Qed.
Lemma lem3128441 : term380 = True.
Proof. exact (TRANS (@lem3128436) (@lem3128440)). Qed.
Lemma lem3128442 : True = term380.
Proof. exact (SYM (@lem3128441)). Qed.
Lemma lem3128443 : term380.
Proof. exact (EQ_MP (@lem3128442) (@lem0)). Qed.
Lemma lem3128444 : term384 = term389.
Proof. exact (@lem3128433 (@lem3128443)). Qed.
Lemma lem3128446 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3128447 : term337 = term338.
Proof. exact (@lem3128446 term22 term22). Qed.
Lemma lem3128448 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128449 : term340 = term22.
Proof. exact (EQ_MP (@lem3128448) (@lem940073)). Qed.
Lemma lem3128450 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128451 : term338 = term275.
Proof. exact (MK_COMB (@lem3128450) (@lem3128449)). Qed.
Lemma lem3128452 : term337 = term275.
Proof. exact (TRANS (@lem3128447) (@lem3128451)). Qed.
Lemma lem3128454 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3128455 : term391 = term296.
Proof. exact (@lem3128454 term22). Qed.
Lemma lem3128456 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3128457 : term392 = term382.
Proof. exact (MK_COMB (@lem3128456) (@lem3128455)). Qed.
Lemma lem3128458 : term389 = term380.
Proof. exact (MK_COMB (@lem3128457) (@lem3128452)). Qed.
Lemma lem3128460 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128461 : term380 = term387.
Proof. exact (@lem3128460 (NUMERAL 0) term22). Qed.
Lemma lem3128462 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128463 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128464 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128463 h1) (fun h1 : term387 = True => @lem3128462)). Qed.
Lemma lem3128465 : term387 = True.
Proof. exact (EQ_MP (@lem3128464) (@lem3128462)). Qed.
Lemma lem3128466 : term380 = True.
Proof. exact (TRANS (@lem3128461) (@lem3128465)). Qed.
Lemma lem3128467 : term389 = True.
Proof. exact (TRANS (@lem3128458) (@lem3128466)). Qed.
Lemma lem3128468 : term384 = True.
Proof. exact (TRANS (@lem3128444) (@lem3128467)). Qed.
Lemma lem3128469 : term380 = True.
Proof. exact (TRANS (@lem3128421) (@lem3128468)). Qed.
Lemma lem3128470 : term379 = True.
Proof. exact (TRANS (@lem3128412) (@lem3128469)). Qed.
Lemma lem3128471 : True = term379.
Proof. exact (SYM (@lem3128470)). Qed.
Lemma lem3128472 : term379.
Proof. exact (EQ_MP (@lem3128471) (@lem0)). Qed.
Lemma lem3128473 (y : int) (x : int) (h1 : term734 y x) : term586 x.
Proof. exact (conj (@lem3128472) (@lem3128335 y x h1)). Qed.
Lemma lem3128475 (x : real) (y : real) : term394 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3128476 (x : int) : term587 x.
Proof. exact (@lem3128475 term275 (term348 x)). Qed.
Lemma lem3128477 (y : int) (x : int) (h1 : term734 y x) : term588 x.
Proof. exact (@lem3128476 x (@lem3128473 y x h1)). Qed.
Lemma lem3128478 (x : int) : (term589 x) = (term348 x).
Proof. exact (@lem1982733 (term348 x)). Qed.
Lemma lem3128479 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3128480 (x : int) : (term590 x) = (term571 x).
Proof. exact (MK_COMB (@lem3128479) (@lem3128478 x)). Qed.
Lemma lem3128481 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3128482 (x : int) : (term588 x) = (term573 x).
Proof. exact (MK_COMB (@lem3128480 x) (@lem3128481)). Qed.
Lemma lem3128483 (y : int) (x : int) (h1 : term734 y x) : term573 x.
Proof. exact (EQ_MP (@lem3128482 x) (@lem3128477 y x h1)). Qed.
Lemma lem3128484 (y : int) (x : int) (h1 : term734 y x) : term729 x.
Proof. exact (conj (@lem3128483 y x h1) (@lem3128409 y x h1)). Qed.
Lemma lem3128486 (x : real) (y : real) : term405 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3128487 (x : int) : term757 x.
Proof. exact (@lem3128486 (term348 x) (term669 x)). Qed.
Lemma lem3128488 (y : int) (x : int) (h1 : term734 y x) : term758 x.
Proof. exact (@lem3128487 x (@lem3128484 y x h1)). Qed.
Lemma lem3128489 (x : int) : (term759 x) = (term760 x).
Proof. exact (@lem1982753 (term369 x) (real_of_int x) term321 term321). Qed.
Lemma lem3128490 (x : int) : (term410 x) = (term411 x).
Proof. exact (@lem1982713 term321 (real_of_int x)). Qed.
Lemma lem3128492 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128493 : term275 = term326.
Proof. exact (@lem3128492 term22). Qed.
Lemma lem3128495 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3128496 : term321 = term329.
Proof. exact (@lem3128495 term22). Qed.
Lemma lem3128497 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3128498 : term412 = term413.
Proof. exact (MK_COMB (@lem3128497) (@lem3128496)). Qed.
Lemma lem3128499 : term414 = term415.
Proof. exact (MK_COMB (@lem3128498) (@lem3128493)). Qed.
Lemma lem3128500 : term416.
Proof. exact (@lem1981473 term321 term275 term275 term275 term296 term275). Qed.
Lemma lem3128502 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128503 : term380 = term387.
Proof. exact (@lem3128502 (NUMERAL 0) term22). Qed.
Lemma lem3128504 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128505 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128506 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128505 h1) (fun h1 : term387 = True => @lem3128504)). Qed.
Lemma lem3128507 : term387 = True.
Proof. exact (EQ_MP (@lem3128506) (@lem3128504)). Qed.
Lemma lem3128508 : term380 = True.
Proof. exact (TRANS (@lem3128503) (@lem3128507)). Qed.
Lemma lem3128509 : True = term380.
Proof. exact (SYM (@lem3128508)). Qed.
Lemma lem3128510 : term380.
Proof. exact (EQ_MP (@lem3128509) (@lem0)). Qed.
Lemma lem3128511 : term417.
Proof. exact (@lem3128500 (@lem3128510)). Qed.
Lemma lem3128513 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128514 : term380 = term387.
Proof. exact (@lem3128513 (NUMERAL 0) term22). Qed.
Lemma lem3128515 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128516 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128517 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128516 h1) (fun h1 : term387 = True => @lem3128515)). Qed.
Lemma lem3128518 : term387 = True.
Proof. exact (EQ_MP (@lem3128517) (@lem3128515)). Qed.
Lemma lem3128519 : term380 = True.
Proof. exact (TRANS (@lem3128514) (@lem3128518)). Qed.
Lemma lem3128520 : True = term380.
Proof. exact (SYM (@lem3128519)). Qed.
Lemma lem3128521 : term380.
Proof. exact (EQ_MP (@lem3128520) (@lem0)). Qed.
Lemma lem3128522 : term418.
Proof. exact (@lem3128511 (@lem3128521)). Qed.
Lemma lem3128524 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128525 : term380 = term387.
Proof. exact (@lem3128524 (NUMERAL 0) term22). Qed.
Lemma lem3128526 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128527 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128528 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128527 h1) (fun h1 : term387 = True => @lem3128526)). Qed.
Lemma lem3128529 : term387 = True.
Proof. exact (EQ_MP (@lem3128528) (@lem3128526)). Qed.
Lemma lem3128530 : term380 = True.
Proof. exact (TRANS (@lem3128525) (@lem3128529)). Qed.
Lemma lem3128531 : True = term380.
Proof. exact (SYM (@lem3128530)). Qed.
Lemma lem3128532 : term380.
Proof. exact (EQ_MP (@lem3128531) (@lem0)). Qed.
Lemma lem3128533 : term419.
Proof. exact (@lem3128522 (@lem3128532)). Qed.
Lemma lem3128535 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3128536 : term337 = term338.
Proof. exact (@lem3128535 term22 term22). Qed.
Lemma lem3128537 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128538 : term340 = term22.
Proof. exact (EQ_MP (@lem3128537) (@lem940073)). Qed.
Lemma lem3128539 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128540 : term338 = term275.
Proof. exact (MK_COMB (@lem3128539) (@lem3128538)). Qed.
Lemma lem3128541 : term337 = term275.
Proof. exact (TRANS (@lem3128536) (@lem3128540)). Qed.
Lemma lem3128543 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3128544 : term332 = term343.
Proof. exact (@lem3128543 term22 term22). Qed.
Lemma lem3128545 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128546 : term340 = term22.
Proof. exact (EQ_MP (@lem3128545) (@lem940073)). Qed.
Lemma lem3128547 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128548 : term338 = term275.
Proof. exact (MK_COMB (@lem3128547) (@lem3128546)). Qed.
Lemma lem3128549 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128550 : term343 = term321.
Proof. exact (MK_COMB (@lem3128549) (@lem3128548)). Qed.
Lemma lem3128551 : term332 = term321.
Proof. exact (TRANS (@lem3128544) (@lem3128550)). Qed.
Lemma lem3128552 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3128553 : term420 = term412.
Proof. exact (MK_COMB (@lem3128552) (@lem3128551)). Qed.
Lemma lem3128554 : term421 = term414.
Proof. exact (MK_COMB (@lem3128553) (@lem3128541)). Qed.
Lemma lem3128556 (m : nat) : (term422 m) = term296.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3128557 : term414 = term296.
Proof. exact (@lem3128556 term22). Qed.
Lemma lem3128558 : term421 = term296.
Proof. exact (TRANS (@lem3128554) (@lem3128557)). Qed.
Lemma lem3128559 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3128560 : term423 = term424.
Proof. exact (MK_COMB (@lem3128559) (@lem3128558)). Qed.
Lemma lem3128561 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem3128562 : term425 = term391.
Proof. exact (MK_COMB (@lem3128560) (@lem3128561)). Qed.
Lemma lem3128564 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3128565 : term391 = term296.
Proof. exact (@lem3128564 term22). Qed.
Lemma lem3128566 : term425 = term296.
Proof. exact (TRANS (@lem3128562) (@lem3128565)). Qed.
Lemma lem3128568 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3128569 : term337 = term338.
Proof. exact (@lem3128568 term22 term22). Qed.
Lemma lem3128570 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128571 : term340 = term22.
Proof. exact (EQ_MP (@lem3128570) (@lem940073)). Qed.
Lemma lem3128572 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128573 : term338 = term275.
Proof. exact (MK_COMB (@lem3128572) (@lem3128571)). Qed.
Lemma lem3128574 : term337 = term275.
Proof. exact (TRANS (@lem3128569) (@lem3128573)). Qed.
Lemma lem3128575 : term424 = term424.
Proof. exact (eq_refl term424). Qed.
Lemma lem3128576 : term426 = term391.
Proof. exact (MK_COMB (@lem3128575) (@lem3128574)). Qed.
Lemma lem3128578 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3128579 : term391 = term296.
Proof. exact (@lem3128578 term22). Qed.
Lemma lem3128580 : term426 = term296.
Proof. exact (TRANS (@lem3128576) (@lem3128579)). Qed.
Lemma lem3128581 : term296 = term426.
Proof. exact (SYM (@lem3128580)). Qed.
Lemma lem3128582 : term425 = term426.
Proof. exact (TRANS (@lem3128566) (@lem3128581)). Qed.
Lemma lem3128583 : term415 = term381.
Proof. exact (@lem3128533 (@lem3128582)). Qed.
Lemma lem3128584 : term414 = term381.
Proof. exact (TRANS (@lem3128499) (@lem3128583)). Qed.
Lemma lem3128586 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3128587 : term381 = term296.
Proof. exact (@lem3128586 term296). Qed.
Lemma lem3128588 : term414 = term296.
Proof. exact (TRANS (@lem3128584) (@lem3128587)). Qed.
Lemma lem3128589 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3128590 : term427 = term424.
Proof. exact (MK_COMB (@lem3128589) (@lem3128588)). Qed.
Lemma lem3128591 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem3128592 (x : int) : (term411 x) = (term428 x).
Proof. exact (MK_COMB (@lem3128590) (@lem3128591 x)). Qed.
Lemma lem3128593 (x : int) : (term410 x) = (term428 x).
Proof. exact (TRANS (@lem3128490 x) (@lem3128592 x)). Qed.
Lemma lem3128594 (x : int) : (term428 x) = term296.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem3128595 (x : int) : (term410 x) = term296.
Proof. exact (TRANS (@lem3128593 x) (@lem3128594 x)). Qed.
Lemma lem3128596 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3128597 (x : int) : (term429 x) = term350.
Proof. exact (MK_COMB (@lem3128596) (@lem3128595 x)). Qed.
Lemma lem3128599 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3128600 : term321 = term329.
Proof. exact (@lem3128599 term22). Qed.
Lemma lem3128602 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3128603 : term321 = term329.
Proof. exact (@lem3128602 term22). Qed.
Lemma lem3128604 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3128605 : term412 = term413.
Proof. exact (MK_COMB (@lem3128604) (@lem3128603)). Qed.
Lemma lem3128606 : term761 = term762.
Proof. exact (MK_COMB (@lem3128605) (@lem3128600)). Qed.
Lemma lem3128607 : term763.
Proof. exact (@lem1981473 term321 term275 term321 term275 term764 term275). Qed.
Lemma lem3128609 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128610 : term380 = term387.
Proof. exact (@lem3128609 (NUMERAL 0) term22). Qed.
Lemma lem3128611 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128612 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128613 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128612 h1) (fun h1 : term387 = True => @lem3128611)). Qed.
Lemma lem3128614 : term387 = True.
Proof. exact (EQ_MP (@lem3128613) (@lem3128611)). Qed.
Lemma lem3128615 : term380 = True.
Proof. exact (TRANS (@lem3128610) (@lem3128614)). Qed.
Lemma lem3128616 : True = term380.
Proof. exact (SYM (@lem3128615)). Qed.
Lemma lem3128617 : term380.
Proof. exact (EQ_MP (@lem3128616) (@lem0)). Qed.
Lemma lem3128618 : term765.
Proof. exact (@lem3128607 (@lem3128617)). Qed.
Lemma lem3128620 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128621 : term380 = term387.
Proof. exact (@lem3128620 (NUMERAL 0) term22). Qed.
Lemma lem3128622 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128623 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128624 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128623 h1) (fun h1 : term387 = True => @lem3128622)). Qed.
Lemma lem3128625 : term387 = True.
Proof. exact (EQ_MP (@lem3128624) (@lem3128622)). Qed.
Lemma lem3128626 : term380 = True.
Proof. exact (TRANS (@lem3128621) (@lem3128625)). Qed.
Lemma lem3128627 : True = term380.
Proof. exact (SYM (@lem3128626)). Qed.
Lemma lem3128628 : term380.
Proof. exact (EQ_MP (@lem3128627) (@lem0)). Qed.
Lemma lem3128629 : term766.
Proof. exact (@lem3128618 (@lem3128628)). Qed.
Lemma lem3128631 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128632 : term380 = term387.
Proof. exact (@lem3128631 (NUMERAL 0) term22). Qed.
Lemma lem3128633 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128634 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128635 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128634 h1) (fun h1 : term387 = True => @lem3128633)). Qed.
Lemma lem3128636 : term387 = True.
Proof. exact (EQ_MP (@lem3128635) (@lem3128633)). Qed.
Lemma lem3128637 : term380 = True.
Proof. exact (TRANS (@lem3128632) (@lem3128636)). Qed.
Lemma lem3128638 : True = term380.
Proof. exact (SYM (@lem3128637)). Qed.
Lemma lem3128639 : term380.
Proof. exact (EQ_MP (@lem3128638) (@lem0)). Qed.
Lemma lem3128640 : term767.
Proof. exact (@lem3128629 (@lem3128639)). Qed.
Lemma lem3128642 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3128643 : term332 = term343.
Proof. exact (@lem3128642 term22 term22). Qed.
Lemma lem3128644 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128645 : term340 = term22.
Proof. exact (EQ_MP (@lem3128644) (@lem940073)). Qed.
Lemma lem3128646 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128647 : term338 = term275.
Proof. exact (MK_COMB (@lem3128646) (@lem3128645)). Qed.
Lemma lem3128648 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128649 : term343 = term321.
Proof. exact (MK_COMB (@lem3128648) (@lem3128647)). Qed.
Lemma lem3128650 : term332 = term321.
Proof. exact (TRANS (@lem3128643) (@lem3128649)). Qed.
Lemma lem3128652 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3128653 : term332 = term343.
Proof. exact (@lem3128652 term22 term22). Qed.
Lemma lem3128654 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128655 : term340 = term22.
Proof. exact (EQ_MP (@lem3128654) (@lem940073)). Qed.
Lemma lem3128656 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128657 : term338 = term275.
Proof. exact (MK_COMB (@lem3128656) (@lem3128655)). Qed.
Lemma lem3128658 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128659 : term343 = term321.
Proof. exact (MK_COMB (@lem3128658) (@lem3128657)). Qed.
Lemma lem3128660 : term332 = term321.
Proof. exact (TRANS (@lem3128653) (@lem3128659)). Qed.
Lemma lem3128661 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3128662 : term420 = term412.
Proof. exact (MK_COMB (@lem3128661) (@lem3128660)). Qed.
Lemma lem3128663 : term768 = term761.
Proof. exact (MK_COMB (@lem3128662) (@lem3128650)). Qed.
Lemma lem3128664 : term761 = term769.
Proof. exact (@lem1367763 term22 term22). Qed.
Lemma lem3128665 : term770 = term771.
Proof. exact (@lem706885). Qed.
Lemma lem3128666 : (term770 = term771) = (term772 = term773).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term771). Qed.
Lemma lem3128667 : term772 = term773.
Proof. exact (EQ_MP (@lem3128666) (@lem3128665)). Qed.
Lemma lem3128668 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128669 : term774 = term775.
Proof. exact (MK_COMB (@lem3128668) (@lem3128667)). Qed.
Lemma lem3128670 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128671 : term769 = term764.
Proof. exact (MK_COMB (@lem3128670) (@lem3128669)). Qed.
Lemma lem3128672 : term761 = term764.
Proof. exact (TRANS (@lem3128664) (@lem3128671)). Qed.
Lemma lem3128673 : term768 = term764.
Proof. exact (TRANS (@lem3128663) (@lem3128672)). Qed.
Lemma lem3128674 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3128675 : term776 = term777.
Proof. exact (MK_COMB (@lem3128674) (@lem3128673)). Qed.
Lemma lem3128676 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem3128677 : term778 = term779.
Proof. exact (MK_COMB (@lem3128675) (@lem3128676)). Qed.
Lemma lem3128679 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3128680 : term779 = term780.
Proof. exact (@lem3128679 term773 term22). Qed.
Lemma lem3128681 : term781 = term771.
Proof. exact (@lem996237 term771). Qed.
Lemma lem3128682 : (term781 = term771) = (term782 = term773).
Proof. exact (@lem1007663 term771 (BIT1 0) term771). Qed.
Lemma lem3128683 : term782 = term773.
Proof. exact (EQ_MP (@lem3128682) (@lem3128681)). Qed.
Lemma lem3128684 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128685 : term783 = term775.
Proof. exact (MK_COMB (@lem3128684) (@lem3128683)). Qed.
Lemma lem3128686 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128687 : term780 = term764.
Proof. exact (MK_COMB (@lem3128686) (@lem3128685)). Qed.
Lemma lem3128688 : term779 = term764.
Proof. exact (TRANS (@lem3128680) (@lem3128687)). Qed.
Lemma lem3128689 : term778 = term764.
Proof. exact (TRANS (@lem3128677) (@lem3128688)). Qed.
Lemma lem3128691 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3128692 : term337 = term338.
Proof. exact (@lem3128691 term22 term22). Qed.
Lemma lem3128693 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128694 : term340 = term22.
Proof. exact (EQ_MP (@lem3128693) (@lem940073)). Qed.
Lemma lem3128695 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128696 : term338 = term275.
Proof. exact (MK_COMB (@lem3128695) (@lem3128694)). Qed.
Lemma lem3128697 : term337 = term275.
Proof. exact (TRANS (@lem3128692) (@lem3128696)). Qed.
Lemma lem3128698 : term777 = term777.
Proof. exact (eq_refl term777). Qed.
Lemma lem3128699 : term784 = term779.
Proof. exact (MK_COMB (@lem3128698) (@lem3128697)). Qed.
Lemma lem3128701 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3128702 : term779 = term780.
Proof. exact (@lem3128701 term773 term22). Qed.
Lemma lem3128703 : term781 = term771.
Proof. exact (@lem996237 term771). Qed.
Lemma lem3128704 : (term781 = term771) = (term782 = term773).
Proof. exact (@lem1007663 term771 (BIT1 0) term771). Qed.
Lemma lem3128705 : term782 = term773.
Proof. exact (EQ_MP (@lem3128704) (@lem3128703)). Qed.
Lemma lem3128706 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128707 : term783 = term775.
Proof. exact (MK_COMB (@lem3128706) (@lem3128705)). Qed.
Lemma lem3128708 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128709 : term780 = term764.
Proof. exact (MK_COMB (@lem3128708) (@lem3128707)). Qed.
Lemma lem3128710 : term779 = term764.
Proof. exact (TRANS (@lem3128702) (@lem3128709)). Qed.
Lemma lem3128711 : term784 = term764.
Proof. exact (TRANS (@lem3128699) (@lem3128710)). Qed.
Lemma lem3128712 : term764 = term784.
Proof. exact (SYM (@lem3128711)). Qed.
Lemma lem3128713 : term778 = term784.
Proof. exact (TRANS (@lem3128689) (@lem3128712)). Qed.
Lemma lem3128714 : term762 = term785.
Proof. exact (@lem3128640 (@lem3128713)). Qed.
Lemma lem3128715 : term761 = term785.
Proof. exact (TRANS (@lem3128606) (@lem3128714)). Qed.
Lemma lem3128717 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3128718 : term785 = term764.
Proof. exact (@lem3128717 term764). Qed.
Lemma lem3128719 : term761 = term764.
Proof. exact (TRANS (@lem3128715) (@lem3128718)). Qed.
Lemma lem3128720 (x : int) : (term760 x) = term786.
Proof. exact (MK_COMB (@lem3128597 x) (@lem3128719)). Qed.
Lemma lem3128721 (x : int) : (term759 x) = term786.
Proof. exact (TRANS (@lem3128489 x) (@lem3128720 x)). Qed.
Lemma lem3128722 : term786 = term764.
Proof. exact (@lem1982721 term764). Qed.
Lemma lem3128723 (x : int) : (term759 x) = term764.
Proof. exact (TRANS (@lem3128721 x) (@lem3128722)). Qed.
Lemma lem3128724 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3128725 (x : int) : (term787 x) = term788.
Proof. exact (MK_COMB (@lem3128724) (@lem3128723 x)). Qed.
Lemma lem3128726 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3128727 (x : int) : (term758 x) = term789.
Proof. exact (MK_COMB (@lem3128725 x) (@lem3128726)). Qed.
Lemma lem3128728 (y : int) (x : int) (h1 : term734 y x) : term789.
Proof. exact (EQ_MP (@lem3128727 x) (@lem3128488 y x h1)). Qed.
Lemma lem3128730 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3128731 : term789 = term790.
Proof. exact (@lem3128730 term296 term764). Qed.
Lemma lem3128733 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3128734 : term764 = term785.
Proof. exact (@lem3128733 term773). Qed.
Lemma lem3128736 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128737 : term296 = term381.
Proof. exact (@lem3128736 (NUMERAL 0)). Qed.
Lemma lem3128738 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3128739 : term437 = term438.
Proof. exact (MK_COMB (@lem3128738) (@lem3128737)). Qed.
Lemma lem3128740 : term790 = term791.
Proof. exact (MK_COMB (@lem3128739) (@lem3128734)). Qed.
Lemma lem3128741 : term792.
Proof. exact (@lem1980026 term296 term275 term764 term275). Qed.
Lemma lem3128743 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128744 : term380 = term387.
Proof. exact (@lem3128743 (NUMERAL 0) term22). Qed.
Lemma lem3128745 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128746 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128747 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128746 h1) (fun h1 : term387 = True => @lem3128745)). Qed.
Lemma lem3128748 : term387 = True.
Proof. exact (EQ_MP (@lem3128747) (@lem3128745)). Qed.
Lemma lem3128749 : term380 = True.
Proof. exact (TRANS (@lem3128744) (@lem3128748)). Qed.
Lemma lem3128750 : True = term380.
Proof. exact (SYM (@lem3128749)). Qed.
Lemma lem3128751 : term380.
Proof. exact (EQ_MP (@lem3128750) (@lem0)). Qed.
Lemma lem3128752 : term793.
Proof. exact (@lem3128741 (@lem3128751)). Qed.
Lemma lem3128754 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128755 : term380 = term387.
Proof. exact (@lem3128754 (NUMERAL 0) term22). Qed.
Lemma lem3128756 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128757 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128758 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128757 h1) (fun h1 : term387 = True => @lem3128756)). Qed.
Lemma lem3128759 : term387 = True.
Proof. exact (EQ_MP (@lem3128758) (@lem3128756)). Qed.
Lemma lem3128760 : term380 = True.
Proof. exact (TRANS (@lem3128755) (@lem3128759)). Qed.
Lemma lem3128761 : True = term380.
Proof. exact (SYM (@lem3128760)). Qed.
Lemma lem3128762 : term380.
Proof. exact (EQ_MP (@lem3128761) (@lem0)). Qed.
Lemma lem3128763 : term791 = term794.
Proof. exact (@lem3128752 (@lem3128762)). Qed.
Lemma lem3128765 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3128766 : term779 = term780.
Proof. exact (@lem3128765 term773 term22). Qed.
Lemma lem3128767 : term781 = term771.
Proof. exact (@lem996237 term771). Qed.
Lemma lem3128768 : (term781 = term771) = (term782 = term773).
Proof. exact (@lem1007663 term771 (BIT1 0) term771). Qed.
Lemma lem3128769 : term782 = term773.
Proof. exact (EQ_MP (@lem3128768) (@lem3128767)). Qed.
Lemma lem3128770 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128771 : term783 = term775.
Proof. exact (MK_COMB (@lem3128770) (@lem3128769)). Qed.
Lemma lem3128772 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3128773 : term780 = term764.
Proof. exact (MK_COMB (@lem3128772) (@lem3128771)). Qed.
Lemma lem3128774 : term779 = term764.
Proof. exact (TRANS (@lem3128766) (@lem3128773)). Qed.
Lemma lem3128776 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3128777 : term391 = term296.
Proof. exact (@lem3128776 term22). Qed.
Lemma lem3128778 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3128779 : term443 = term437.
Proof. exact (MK_COMB (@lem3128778) (@lem3128777)). Qed.
Lemma lem3128780 : term794 = term790.
Proof. exact (MK_COMB (@lem3128779) (@lem3128774)). Qed.
Lemma lem3128782 (m : nat) (n : nat) : (term444 m n) = (term445 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3128783 : term790 = term795.
Proof. exact (@lem3128782 (NUMERAL 0) term773). Qed.
Lemma lem3128784 : term796 = term771.
Proof. exact (@lem912803). Qed.
Lemma lem3128785 (h1 : term796 = term771) : (term773 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term771 h1). Qed.
Lemma lem3128786 : (term796 = term771) = ((term773 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term796 = term771 => @lem3128785 h1) (fun h1 : (term773 = (NUMERAL 0)) = False => @lem3128784)). Qed.
Lemma lem3128787 : (term773 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3128786) (@lem3128784)). Qed.
Lemma lem3128788 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3128789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3128790 : term447 = (and True).
Proof. exact (MK_COMB (@lem3128789) (@lem3128788)). Qed.
Lemma lem3128791 : term795 = (True /\ False).
Proof. exact (MK_COMB (@lem3128790) (@lem3128787)). Qed.
Lemma lem3128793 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3128794 : term795 = False.
Proof. exact (TRANS (@lem3128791) (@lem3128793)). Qed.
Lemma lem3128795 : term790 = False.
Proof. exact (TRANS (@lem3128783) (@lem3128794)). Qed.
Lemma lem3128796 : term794 = False.
Proof. exact (TRANS (@lem3128780) (@lem3128795)). Qed.
Lemma lem3128797 : term791 = False.
Proof. exact (TRANS (@lem3128763) (@lem3128796)). Qed.
Lemma lem3128798 : term790 = False.
Proof. exact (TRANS (@lem3128740) (@lem3128797)). Qed.
Lemma lem3128799 : term789 = False.
Proof. exact (TRANS (@lem3128731) (@lem3128798)). Qed.
Lemma lem3128800 (y : int) (x : int) (h1 : term734 y x) : False.
Proof. exact (EQ_MP (@lem3128799) (@lem3128728 y x h1)). Qed.
Lemma lem3128801 (y : int) (x : int) (h1 : term737 y x) : False.
Proof. exact (or_elim (@lem3127860 y x h1) (fun h0 : term731 y x => @lem3128330 y x h0) (fun h0 : term734 y x => @lem3128800 y x h0)). Qed.
Lemma lem3128802 (y : int) (h1 : term749 y) : term749 y.
Proof. exact (h1). Qed.
Lemma lem3128803 (y : int) (h1 : term744 y) : term744 y.
Proof. exact (h1). Qed.
Lemma lem3128804 (y : int) (h1 : term744 y) : term742 y.
Proof. exact (proj2 (@lem3128803 y h1)). Qed.
Lemma lem3128805 (y : int) (h1 : term744 y) : term573 y.
Proof. exact (proj1 (@lem3128803 y h1)). Qed.
Lemma lem3128806 (y : int) (h1 : term744 y) : term543 y.
Proof. exact (proj2 (@lem3128804 y h1)). Qed.
Lemma lem3128809 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3128810 : term379 = term380.
Proof. exact (@lem3128809 term296 term275). Qed.
Lemma lem3128812 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128813 : term275 = term326.
Proof. exact (@lem3128812 term22). Qed.
Lemma lem3128815 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128816 : term296 = term381.
Proof. exact (@lem3128815 (NUMERAL 0)). Qed.
Lemma lem3128817 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3128818 : term382 = term383.
Proof. exact (MK_COMB (@lem3128817) (@lem3128816)). Qed.
Lemma lem3128819 : term380 = term384.
Proof. exact (MK_COMB (@lem3128818) (@lem3128813)). Qed.
Lemma lem3128820 : term385.
Proof. exact (@lem1980255 term296 term275 term275 term275). Qed.
Lemma lem3128822 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128823 : term380 = term387.
Proof. exact (@lem3128822 (NUMERAL 0) term22). Qed.
Lemma lem3128824 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128825 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128826 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128825 h1) (fun h1 : term387 = True => @lem3128824)). Qed.
Lemma lem3128827 : term387 = True.
Proof. exact (EQ_MP (@lem3128826) (@lem3128824)). Qed.
Lemma lem3128828 : term380 = True.
Proof. exact (TRANS (@lem3128823) (@lem3128827)). Qed.
Lemma lem3128829 : True = term380.
Proof. exact (SYM (@lem3128828)). Qed.
Lemma lem3128830 : term380.
Proof. exact (EQ_MP (@lem3128829) (@lem0)). Qed.
Lemma lem3128831 : term388.
Proof. exact (@lem3128820 (@lem3128830)). Qed.
Lemma lem3128833 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128834 : term380 = term387.
Proof. exact (@lem3128833 (NUMERAL 0) term22). Qed.
Lemma lem3128835 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128836 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128837 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128836 h1) (fun h1 : term387 = True => @lem3128835)). Qed.
Lemma lem3128838 : term387 = True.
Proof. exact (EQ_MP (@lem3128837) (@lem3128835)). Qed.
Lemma lem3128839 : term380 = True.
Proof. exact (TRANS (@lem3128834) (@lem3128838)). Qed.
Lemma lem3128840 : True = term380.
Proof. exact (SYM (@lem3128839)). Qed.
Lemma lem3128841 : term380.
Proof. exact (EQ_MP (@lem3128840) (@lem0)). Qed.
Lemma lem3128842 : term384 = term389.
Proof. exact (@lem3128831 (@lem3128841)). Qed.
Lemma lem3128844 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3128845 : term337 = term338.
Proof. exact (@lem3128844 term22 term22). Qed.
Lemma lem3128846 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128847 : term340 = term22.
Proof. exact (EQ_MP (@lem3128846) (@lem940073)). Qed.
Lemma lem3128848 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128849 : term338 = term275.
Proof. exact (MK_COMB (@lem3128848) (@lem3128847)). Qed.
Lemma lem3128850 : term337 = term275.
Proof. exact (TRANS (@lem3128845) (@lem3128849)). Qed.
Lemma lem3128852 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3128853 : term391 = term296.
Proof. exact (@lem3128852 term22). Qed.
Lemma lem3128854 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3128855 : term392 = term382.
Proof. exact (MK_COMB (@lem3128854) (@lem3128853)). Qed.
Lemma lem3128856 : term389 = term380.
Proof. exact (MK_COMB (@lem3128855) (@lem3128850)). Qed.
Lemma lem3128858 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128859 : term380 = term387.
Proof. exact (@lem3128858 (NUMERAL 0) term22). Qed.
Lemma lem3128860 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128861 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128862 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128861 h1) (fun h1 : term387 = True => @lem3128860)). Qed.
Lemma lem3128863 : term387 = True.
Proof. exact (EQ_MP (@lem3128862) (@lem3128860)). Qed.
Lemma lem3128864 : term380 = True.
Proof. exact (TRANS (@lem3128859) (@lem3128863)). Qed.
Lemma lem3128865 : term389 = True.
Proof. exact (TRANS (@lem3128856) (@lem3128864)). Qed.
Lemma lem3128866 : term384 = True.
Proof. exact (TRANS (@lem3128842) (@lem3128865)). Qed.
Lemma lem3128867 : term380 = True.
Proof. exact (TRANS (@lem3128819) (@lem3128866)). Qed.
Lemma lem3128868 : term379 = True.
Proof. exact (TRANS (@lem3128810) (@lem3128867)). Qed.
Lemma lem3128869 : True = term379.
Proof. exact (SYM (@lem3128868)). Qed.
Lemma lem3128870 : term379.
Proof. exact (EQ_MP (@lem3128869) (@lem0)). Qed.
Lemma lem3128871 (y : int) (h1 : term744 y) : term582 y.
Proof. exact (conj (@lem3128870) (@lem3128806 y h1)). Qed.
Lemma lem3128873 (x : real) (y : real) : term394 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3128874 (y : int) : term583 y.
Proof. exact (@lem3128873 term275 (real_of_int y)). Qed.
Lemma lem3128875 (y : int) (h1 : term744 y) : term584 y.
Proof. exact (@lem3128874 y (@lem3128871 y h1)). Qed.
Lemma lem3128876 (y : int) : (term360 y) = (real_of_int y).
Proof. exact (@lem1982733 (real_of_int y)). Qed.
Lemma lem3128877 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3128878 (y : int) : (term585 y) = (term542 y).
Proof. exact (MK_COMB (@lem3128877) (@lem3128876 y)). Qed.
Lemma lem3128879 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3128880 (y : int) : (term584 y) = (term543 y).
Proof. exact (MK_COMB (@lem3128878 y) (@lem3128879)). Qed.
Lemma lem3128881 (y : int) (h1 : term744 y) : term543 y.
Proof. exact (EQ_MP (@lem3128880 y) (@lem3128875 y h1)). Qed.
Lemma lem3128883 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3128884 : term379 = term380.
Proof. exact (@lem3128883 term296 term275). Qed.
Lemma lem3128886 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128887 : term275 = term326.
Proof. exact (@lem3128886 term22). Qed.
Lemma lem3128889 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128890 : term296 = term381.
Proof. exact (@lem3128889 (NUMERAL 0)). Qed.
Lemma lem3128891 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3128892 : term382 = term383.
Proof. exact (MK_COMB (@lem3128891) (@lem3128890)). Qed.
Lemma lem3128893 : term380 = term384.
Proof. exact (MK_COMB (@lem3128892) (@lem3128887)). Qed.
Lemma lem3128894 : term385.
Proof. exact (@lem1980255 term296 term275 term275 term275). Qed.
Lemma lem3128896 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128897 : term380 = term387.
Proof. exact (@lem3128896 (NUMERAL 0) term22). Qed.
Lemma lem3128898 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128899 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128900 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128899 h1) (fun h1 : term387 = True => @lem3128898)). Qed.
Lemma lem3128901 : term387 = True.
Proof. exact (EQ_MP (@lem3128900) (@lem3128898)). Qed.
Lemma lem3128902 : term380 = True.
Proof. exact (TRANS (@lem3128897) (@lem3128901)). Qed.
Lemma lem3128903 : True = term380.
Proof. exact (SYM (@lem3128902)). Qed.
Lemma lem3128904 : term380.
Proof. exact (EQ_MP (@lem3128903) (@lem0)). Qed.
Lemma lem3128905 : term388.
Proof. exact (@lem3128894 (@lem3128904)). Qed.
Lemma lem3128907 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128908 : term380 = term387.
Proof. exact (@lem3128907 (NUMERAL 0) term22). Qed.
Lemma lem3128909 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128910 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128911 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128910 h1) (fun h1 : term387 = True => @lem3128909)). Qed.
Lemma lem3128912 : term387 = True.
Proof. exact (EQ_MP (@lem3128911) (@lem3128909)). Qed.
Lemma lem3128913 : term380 = True.
Proof. exact (TRANS (@lem3128908) (@lem3128912)). Qed.
Lemma lem3128914 : True = term380.
Proof. exact (SYM (@lem3128913)). Qed.
Lemma lem3128915 : term380.
Proof. exact (EQ_MP (@lem3128914) (@lem0)). Qed.
Lemma lem3128916 : term384 = term389.
Proof. exact (@lem3128905 (@lem3128915)). Qed.
Lemma lem3128918 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3128919 : term337 = term338.
Proof. exact (@lem3128918 term22 term22). Qed.
Lemma lem3128920 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3128921 : term340 = term22.
Proof. exact (EQ_MP (@lem3128920) (@lem940073)). Qed.
Lemma lem3128922 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3128923 : term338 = term275.
Proof. exact (MK_COMB (@lem3128922) (@lem3128921)). Qed.
Lemma lem3128924 : term337 = term275.
Proof. exact (TRANS (@lem3128919) (@lem3128923)). Qed.
Lemma lem3128926 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3128927 : term391 = term296.
Proof. exact (@lem3128926 term22). Qed.
Lemma lem3128928 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3128929 : term392 = term382.
Proof. exact (MK_COMB (@lem3128928) (@lem3128927)). Qed.
Lemma lem3128930 : term389 = term380.
Proof. exact (MK_COMB (@lem3128929) (@lem3128924)). Qed.
Lemma lem3128932 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128933 : term380 = term387.
Proof. exact (@lem3128932 (NUMERAL 0) term22). Qed.
Lemma lem3128934 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128935 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128936 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128935 h1) (fun h1 : term387 = True => @lem3128934)). Qed.
Lemma lem3128937 : term387 = True.
Proof. exact (EQ_MP (@lem3128936) (@lem3128934)). Qed.
Lemma lem3128938 : term380 = True.
Proof. exact (TRANS (@lem3128933) (@lem3128937)). Qed.
Lemma lem3128939 : term389 = True.
Proof. exact (TRANS (@lem3128930) (@lem3128938)). Qed.
Lemma lem3128940 : term384 = True.
Proof. exact (TRANS (@lem3128916) (@lem3128939)). Qed.
Lemma lem3128941 : term380 = True.
Proof. exact (TRANS (@lem3128893) (@lem3128940)). Qed.
Lemma lem3128942 : term379 = True.
Proof. exact (TRANS (@lem3128884) (@lem3128941)). Qed.
Lemma lem3128943 : True = term379.
Proof. exact (SYM (@lem3128942)). Qed.
Lemma lem3128944 : term379.
Proof. exact (EQ_MP (@lem3128943) (@lem0)). Qed.
Lemma lem3128945 (y : int) (h1 : term744 y) : term586 y.
Proof. exact (conj (@lem3128944) (@lem3128805 y h1)). Qed.
Lemma lem3128947 (x : real) (y : real) : term394 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3128948 (y : int) : term587 y.
Proof. exact (@lem3128947 term275 (term348 y)). Qed.
Lemma lem3128949 (y : int) (h1 : term744 y) : term588 y.
Proof. exact (@lem3128948 y (@lem3128945 y h1)). Qed.
Lemma lem3128950 (y : int) : (term589 y) = (term348 y).
Proof. exact (@lem1982733 (term348 y)). Qed.
Lemma lem3128951 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3128952 (y : int) : (term590 y) = (term571 y).
Proof. exact (MK_COMB (@lem3128951) (@lem3128950 y)). Qed.
Lemma lem3128953 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3128954 (y : int) : (term588 y) = (term573 y).
Proof. exact (MK_COMB (@lem3128952 y) (@lem3128953)). Qed.
Lemma lem3128955 (y : int) (h1 : term744 y) : term573 y.
Proof. exact (EQ_MP (@lem3128954 y) (@lem3128949 y h1)). Qed.
Lemma lem3128956 (y : int) (h1 : term744 y) : term591 y.
Proof. exact (conj (@lem3128955 y h1) (@lem3128881 y h1)). Qed.
Lemma lem3128958 (x : real) (y : real) : term405 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3128959 (y : int) : term592 y.
Proof. exact (@lem3128958 (term348 y) (real_of_int y)). Qed.
Lemma lem3128960 (y : int) (h1 : term744 y) : term593 y.
Proof. exact (@lem3128959 y (@lem3128956 y h1)). Qed.
Lemma lem3128961 (y : int) : (term430 y) = (term431 y).
Proof. exact (@lem1982759 (term369 y) (real_of_int y) term321). Qed.
Lemma lem3128962 (y : int) : (term410 y) = (term411 y).
Proof. exact (@lem1982713 term321 (real_of_int y)). Qed.
Lemma lem3128964 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3128965 : term275 = term326.
Proof. exact (@lem3128964 term22). Qed.
Lemma lem3128967 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3128968 : term321 = term329.
Proof. exact (@lem3128967 term22). Qed.
Lemma lem3128969 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3128970 : term412 = term413.
Proof. exact (MK_COMB (@lem3128969) (@lem3128968)). Qed.
Lemma lem3128971 : term414 = term415.
Proof. exact (MK_COMB (@lem3128970) (@lem3128965)). Qed.
Lemma lem3128972 : term416.
Proof. exact (@lem1981473 term321 term275 term275 term275 term296 term275). Qed.
Lemma lem3128974 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128975 : term380 = term387.
Proof. exact (@lem3128974 (NUMERAL 0) term22). Qed.
Lemma lem3128976 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128977 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128978 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128977 h1) (fun h1 : term387 = True => @lem3128976)). Qed.
Lemma lem3128979 : term387 = True.
Proof. exact (EQ_MP (@lem3128978) (@lem3128976)). Qed.
Lemma lem3128980 : term380 = True.
Proof. exact (TRANS (@lem3128975) (@lem3128979)). Qed.
Lemma lem3128981 : True = term380.
Proof. exact (SYM (@lem3128980)). Qed.
Lemma lem3128982 : term380.
Proof. exact (EQ_MP (@lem3128981) (@lem0)). Qed.
Lemma lem3128983 : term417.
Proof. exact (@lem3128972 (@lem3128982)). Qed.
Lemma lem3128985 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128986 : term380 = term387.
Proof. exact (@lem3128985 (NUMERAL 0) term22). Qed.
Lemma lem3128987 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128988 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3128989 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128988 h1) (fun h1 : term387 = True => @lem3128987)). Qed.
Lemma lem3128990 : term387 = True.
Proof. exact (EQ_MP (@lem3128989) (@lem3128987)). Qed.
Lemma lem3128991 : term380 = True.
Proof. exact (TRANS (@lem3128986) (@lem3128990)). Qed.
Lemma lem3128992 : True = term380.
Proof. exact (SYM (@lem3128991)). Qed.
Lemma lem3128993 : term380.
Proof. exact (EQ_MP (@lem3128992) (@lem0)). Qed.
Lemma lem3128994 : term418.
Proof. exact (@lem3128983 (@lem3128993)). Qed.
Lemma lem3128996 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3128997 : term380 = term387.
Proof. exact (@lem3128996 (NUMERAL 0) term22). Qed.
Lemma lem3128998 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3128999 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129000 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3128999 h1) (fun h1 : term387 = True => @lem3128998)). Qed.
Lemma lem3129001 : term387 = True.
Proof. exact (EQ_MP (@lem3129000) (@lem3128998)). Qed.
Lemma lem3129002 : term380 = True.
Proof. exact (TRANS (@lem3128997) (@lem3129001)). Qed.
Lemma lem3129003 : True = term380.
Proof. exact (SYM (@lem3129002)). Qed.
Lemma lem3129004 : term380.
Proof. exact (EQ_MP (@lem3129003) (@lem0)). Qed.
Lemma lem3129005 : term419.
Proof. exact (@lem3128994 (@lem3129004)). Qed.
Lemma lem3129007 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3129008 : term337 = term338.
Proof. exact (@lem3129007 term22 term22). Qed.
Lemma lem3129009 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3129010 : term340 = term22.
Proof. exact (EQ_MP (@lem3129009) (@lem940073)). Qed.
Lemma lem3129011 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3129012 : term338 = term275.
Proof. exact (MK_COMB (@lem3129011) (@lem3129010)). Qed.
Lemma lem3129013 : term337 = term275.
Proof. exact (TRANS (@lem3129008) (@lem3129012)). Qed.
Lemma lem3129015 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3129016 : term332 = term343.
Proof. exact (@lem3129015 term22 term22). Qed.
Lemma lem3129017 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3129018 : term340 = term22.
Proof. exact (EQ_MP (@lem3129017) (@lem940073)). Qed.
Lemma lem3129019 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3129020 : term338 = term275.
Proof. exact (MK_COMB (@lem3129019) (@lem3129018)). Qed.
Lemma lem3129021 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3129022 : term343 = term321.
Proof. exact (MK_COMB (@lem3129021) (@lem3129020)). Qed.
Lemma lem3129023 : term332 = term321.
Proof. exact (TRANS (@lem3129016) (@lem3129022)). Qed.
Lemma lem3129024 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3129025 : term420 = term412.
Proof. exact (MK_COMB (@lem3129024) (@lem3129023)). Qed.
Lemma lem3129026 : term421 = term414.
Proof. exact (MK_COMB (@lem3129025) (@lem3129013)). Qed.
Lemma lem3129028 (m : nat) : (term422 m) = term296.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3129029 : term414 = term296.
Proof. exact (@lem3129028 term22). Qed.
Lemma lem3129030 : term421 = term296.
Proof. exact (TRANS (@lem3129026) (@lem3129029)). Qed.
Lemma lem3129031 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3129032 : term423 = term424.
Proof. exact (MK_COMB (@lem3129031) (@lem3129030)). Qed.
Lemma lem3129033 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem3129034 : term425 = term391.
Proof. exact (MK_COMB (@lem3129032) (@lem3129033)). Qed.
Lemma lem3129036 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3129037 : term391 = term296.
Proof. exact (@lem3129036 term22). Qed.
Lemma lem3129038 : term425 = term296.
Proof. exact (TRANS (@lem3129034) (@lem3129037)). Qed.
Lemma lem3129040 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3129041 : term337 = term338.
Proof. exact (@lem3129040 term22 term22). Qed.
Lemma lem3129042 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3129043 : term340 = term22.
Proof. exact (EQ_MP (@lem3129042) (@lem940073)). Qed.
Lemma lem3129044 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3129045 : term338 = term275.
Proof. exact (MK_COMB (@lem3129044) (@lem3129043)). Qed.
Lemma lem3129046 : term337 = term275.
Proof. exact (TRANS (@lem3129041) (@lem3129045)). Qed.
Lemma lem3129047 : term424 = term424.
Proof. exact (eq_refl term424). Qed.
Lemma lem3129048 : term426 = term391.
Proof. exact (MK_COMB (@lem3129047) (@lem3129046)). Qed.
Lemma lem3129050 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3129051 : term391 = term296.
Proof. exact (@lem3129050 term22). Qed.
Lemma lem3129052 : term426 = term296.
Proof. exact (TRANS (@lem3129048) (@lem3129051)). Qed.
Lemma lem3129053 : term296 = term426.
Proof. exact (SYM (@lem3129052)). Qed.
Lemma lem3129054 : term425 = term426.
Proof. exact (TRANS (@lem3129038) (@lem3129053)). Qed.
Lemma lem3129055 : term415 = term381.
Proof. exact (@lem3129005 (@lem3129054)). Qed.
Lemma lem3129056 : term414 = term381.
Proof. exact (TRANS (@lem3128971) (@lem3129055)). Qed.
Lemma lem3129058 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3129059 : term381 = term296.
Proof. exact (@lem3129058 term296). Qed.
Lemma lem3129060 : term414 = term296.
Proof. exact (TRANS (@lem3129056) (@lem3129059)). Qed.
Lemma lem3129061 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3129062 : term427 = term424.
Proof. exact (MK_COMB (@lem3129061) (@lem3129060)). Qed.
Lemma lem3129063 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3129064 (y : int) : (term411 y) = (term428 y).
Proof. exact (MK_COMB (@lem3129062) (@lem3129063 y)). Qed.
Lemma lem3129065 (y : int) : (term410 y) = (term428 y).
Proof. exact (TRANS (@lem3128962 y) (@lem3129064 y)). Qed.
Lemma lem3129066 (y : int) : (term428 y) = term296.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem3129067 (y : int) : (term410 y) = term296.
Proof. exact (TRANS (@lem3129065 y) (@lem3129066 y)). Qed.
Lemma lem3129068 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3129069 (y : int) : (term429 y) = term350.
Proof. exact (MK_COMB (@lem3129068) (@lem3129067 y)). Qed.
Lemma lem3129070 : term321 = term321.
Proof. exact (eq_refl term321). Qed.
Lemma lem3129071 (y : int) : (term431 y) = term432.
Proof. exact (MK_COMB (@lem3129069 y) (@lem3129070)). Qed.
Lemma lem3129072 (y : int) : (term430 y) = term432.
Proof. exact (TRANS (@lem3128961 y) (@lem3129071 y)). Qed.
Lemma lem3129073 : term432 = term321.
Proof. exact (@lem1982721 term321). Qed.
Lemma lem3129074 (y : int) : (term430 y) = term321.
Proof. exact (TRANS (@lem3129072 y) (@lem3129073)). Qed.
Lemma lem3129075 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3129076 (y : int) : (term594 y) = term434.
Proof. exact (MK_COMB (@lem3129075) (@lem3129074 y)). Qed.
Lemma lem3129077 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3129078 (y : int) : (term593 y) = term435.
Proof. exact (MK_COMB (@lem3129076 y) (@lem3129077)). Qed.
Lemma lem3129079 (y : int) (h1 : term744 y) : term435.
Proof. exact (EQ_MP (@lem3129078 y) (@lem3128960 y h1)). Qed.
Lemma lem3129081 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3129082 : term435 = term436.
Proof. exact (@lem3129081 term296 term321). Qed.
Lemma lem3129084 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3129085 : term321 = term329.
Proof. exact (@lem3129084 term22). Qed.
Lemma lem3129087 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3129088 : term296 = term381.
Proof. exact (@lem3129087 (NUMERAL 0)). Qed.
Lemma lem3129089 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3129090 : term437 = term438.
Proof. exact (MK_COMB (@lem3129089) (@lem3129088)). Qed.
Lemma lem3129091 : term436 = term439.
Proof. exact (MK_COMB (@lem3129090) (@lem3129085)). Qed.
Lemma lem3129092 : term440.
Proof. exact (@lem1980026 term296 term275 term321 term275). Qed.
Lemma lem3129094 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129095 : term380 = term387.
Proof. exact (@lem3129094 (NUMERAL 0) term22). Qed.
Lemma lem3129096 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129097 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129098 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129097 h1) (fun h1 : term387 = True => @lem3129096)). Qed.
Lemma lem3129099 : term387 = True.
Proof. exact (EQ_MP (@lem3129098) (@lem3129096)). Qed.
Lemma lem3129100 : term380 = True.
Proof. exact (TRANS (@lem3129095) (@lem3129099)). Qed.
Lemma lem3129101 : True = term380.
Proof. exact (SYM (@lem3129100)). Qed.
Lemma lem3129102 : term380.
Proof. exact (EQ_MP (@lem3129101) (@lem0)). Qed.
Lemma lem3129103 : term441.
Proof. exact (@lem3129092 (@lem3129102)). Qed.
Lemma lem3129105 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129106 : term380 = term387.
Proof. exact (@lem3129105 (NUMERAL 0) term22). Qed.
Lemma lem3129107 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129108 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129109 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129108 h1) (fun h1 : term387 = True => @lem3129107)). Qed.
Lemma lem3129110 : term387 = True.
Proof. exact (EQ_MP (@lem3129109) (@lem3129107)). Qed.
Lemma lem3129111 : term380 = True.
Proof. exact (TRANS (@lem3129106) (@lem3129110)). Qed.
Lemma lem3129112 : True = term380.
Proof. exact (SYM (@lem3129111)). Qed.
Lemma lem3129113 : term380.
Proof. exact (EQ_MP (@lem3129112) (@lem0)). Qed.
Lemma lem3129114 : term439 = term442.
Proof. exact (@lem3129103 (@lem3129113)). Qed.
Lemma lem3129116 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3129117 : term332 = term343.
Proof. exact (@lem3129116 term22 term22). Qed.
Lemma lem3129118 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3129119 : term340 = term22.
Proof. exact (EQ_MP (@lem3129118) (@lem940073)). Qed.
Lemma lem3129120 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3129121 : term338 = term275.
Proof. exact (MK_COMB (@lem3129120) (@lem3129119)). Qed.
Lemma lem3129122 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3129123 : term343 = term321.
Proof. exact (MK_COMB (@lem3129122) (@lem3129121)). Qed.
Lemma lem3129124 : term332 = term321.
Proof. exact (TRANS (@lem3129117) (@lem3129123)). Qed.
Lemma lem3129126 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3129127 : term391 = term296.
Proof. exact (@lem3129126 term22). Qed.
Lemma lem3129128 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3129129 : term443 = term437.
Proof. exact (MK_COMB (@lem3129128) (@lem3129127)). Qed.
Lemma lem3129130 : term442 = term436.
Proof. exact (MK_COMB (@lem3129129) (@lem3129124)). Qed.
Lemma lem3129132 (m : nat) (n : nat) : (term444 m n) = (term445 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3129133 : term436 = term446.
Proof. exact (@lem3129132 (NUMERAL 0) term22). Qed.
Lemma lem3129134 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129135 (h1 : term121 = (BIT1 0)) : (term22 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3129136 : (term121 = (BIT1 0)) = ((term22 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129135 h1) (fun h1 : (term22 = (NUMERAL 0)) = False => @lem3129134)). Qed.
Lemma lem3129137 : (term22 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3129136) (@lem3129134)). Qed.
Lemma lem3129138 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3129139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3129140 : term447 = (and True).
Proof. exact (MK_COMB (@lem3129139) (@lem3129138)). Qed.
Lemma lem3129141 : term446 = (True /\ False).
Proof. exact (MK_COMB (@lem3129140) (@lem3129137)). Qed.
Lemma lem3129143 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3129144 : term446 = False.
Proof. exact (TRANS (@lem3129141) (@lem3129143)). Qed.
Lemma lem3129145 : term436 = False.
Proof. exact (TRANS (@lem3129133) (@lem3129144)). Qed.
Lemma lem3129146 : term442 = False.
Proof. exact (TRANS (@lem3129130) (@lem3129145)). Qed.
Lemma lem3129147 : term439 = False.
Proof. exact (TRANS (@lem3129114) (@lem3129146)). Qed.
Lemma lem3129148 : term436 = False.
Proof. exact (TRANS (@lem3129091) (@lem3129147)). Qed.
Lemma lem3129149 : term435 = False.
Proof. exact (TRANS (@lem3129082) (@lem3129148)). Qed.
Lemma lem3129150 (y : int) (h1 : term744 y) : False.
Proof. exact (EQ_MP (@lem3129149) (@lem3129079 y h1)). Qed.
Lemma lem3129151 (y : int) (h1 : term746 y) : term746 y.
Proof. exact (h1). Qed.
Lemma lem3129152 (y : int) (h1 : term746 y) : term742 y.
Proof. exact (proj2 (@lem3129151 y h1)). Qed.
Lemma lem3129153 (y : int) (h1 : term746 y) : term672 y.
Proof. exact (proj1 (@lem3129151 y h1)). Qed.
Lemma lem3129155 (y : int) (h1 : term746 y) : term797 y.
Proof. exact (proj1 (@lem3129152 y h1)). Qed.
Lemma lem3129157 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3129158 : term379 = term380.
Proof. exact (@lem3129157 term296 term275). Qed.
Lemma lem3129160 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3129161 : term275 = term326.
Proof. exact (@lem3129160 term22). Qed.
Lemma lem3129163 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3129164 : term296 = term381.
Proof. exact (@lem3129163 (NUMERAL 0)). Qed.
Lemma lem3129165 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3129166 : term382 = term383.
Proof. exact (MK_COMB (@lem3129165) (@lem3129164)). Qed.
Lemma lem3129167 : term380 = term384.
Proof. exact (MK_COMB (@lem3129166) (@lem3129161)). Qed.
Lemma lem3129168 : term385.
Proof. exact (@lem1980255 term296 term275 term275 term275). Qed.
Lemma lem3129170 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129171 : term380 = term387.
Proof. exact (@lem3129170 (NUMERAL 0) term22). Qed.
Lemma lem3129172 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129173 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129174 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129173 h1) (fun h1 : term387 = True => @lem3129172)). Qed.
Lemma lem3129175 : term387 = True.
Proof. exact (EQ_MP (@lem3129174) (@lem3129172)). Qed.
Lemma lem3129176 : term380 = True.
Proof. exact (TRANS (@lem3129171) (@lem3129175)). Qed.
Lemma lem3129177 : True = term380.
Proof. exact (SYM (@lem3129176)). Qed.
Lemma lem3129178 : term380.
Proof. exact (EQ_MP (@lem3129177) (@lem0)). Qed.
Lemma lem3129179 : term388.
Proof. exact (@lem3129168 (@lem3129178)). Qed.
Lemma lem3129181 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129182 : term380 = term387.
Proof. exact (@lem3129181 (NUMERAL 0) term22). Qed.
Lemma lem3129183 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129184 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129185 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129184 h1) (fun h1 : term387 = True => @lem3129183)). Qed.
Lemma lem3129186 : term387 = True.
Proof. exact (EQ_MP (@lem3129185) (@lem3129183)). Qed.
Lemma lem3129187 : term380 = True.
Proof. exact (TRANS (@lem3129182) (@lem3129186)). Qed.
Lemma lem3129188 : True = term380.
Proof. exact (SYM (@lem3129187)). Qed.
Lemma lem3129189 : term380.
Proof. exact (EQ_MP (@lem3129188) (@lem0)). Qed.
Lemma lem3129190 : term384 = term389.
Proof. exact (@lem3129179 (@lem3129189)). Qed.
Lemma lem3129192 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3129193 : term337 = term338.
Proof. exact (@lem3129192 term22 term22). Qed.
Lemma lem3129194 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3129195 : term340 = term22.
Proof. exact (EQ_MP (@lem3129194) (@lem940073)). Qed.
Lemma lem3129196 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3129197 : term338 = term275.
Proof. exact (MK_COMB (@lem3129196) (@lem3129195)). Qed.
Lemma lem3129198 : term337 = term275.
Proof. exact (TRANS (@lem3129193) (@lem3129197)). Qed.
Lemma lem3129200 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3129201 : term391 = term296.
Proof. exact (@lem3129200 term22). Qed.
Lemma lem3129202 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3129203 : term392 = term382.
Proof. exact (MK_COMB (@lem3129202) (@lem3129201)). Qed.
Lemma lem3129204 : term389 = term380.
Proof. exact (MK_COMB (@lem3129203) (@lem3129198)). Qed.
Lemma lem3129206 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129207 : term380 = term387.
Proof. exact (@lem3129206 (NUMERAL 0) term22). Qed.
Lemma lem3129208 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129209 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129210 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129209 h1) (fun h1 : term387 = True => @lem3129208)). Qed.
Lemma lem3129211 : term387 = True.
Proof. exact (EQ_MP (@lem3129210) (@lem3129208)). Qed.
Lemma lem3129212 : term380 = True.
Proof. exact (TRANS (@lem3129207) (@lem3129211)). Qed.
Lemma lem3129213 : term389 = True.
Proof. exact (TRANS (@lem3129204) (@lem3129212)). Qed.
Lemma lem3129214 : term384 = True.
Proof. exact (TRANS (@lem3129190) (@lem3129213)). Qed.
Lemma lem3129215 : term380 = True.
Proof. exact (TRANS (@lem3129167) (@lem3129214)). Qed.
Lemma lem3129216 : term379 = True.
Proof. exact (TRANS (@lem3129158) (@lem3129215)). Qed.
Lemma lem3129217 : True = term379.
Proof. exact (SYM (@lem3129216)). Qed.
Lemma lem3129218 : term379.
Proof. exact (EQ_MP (@lem3129217) (@lem0)). Qed.
Lemma lem3129219 (y : int) (h1 : term746 y) : term752 y.
Proof. exact (conj (@lem3129218) (@lem3129153 y h1)). Qed.
Lemma lem3129221 (x : real) (y : real) : term394 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3129222 (y : int) : term753 y.
Proof. exact (@lem3129221 term275 (term669 y)). Qed.
Lemma lem3129223 (y : int) (h1 : term746 y) : term754 y.
Proof. exact (@lem3129222 y (@lem3129219 y h1)). Qed.
Lemma lem3129224 (y : int) : (term755 y) = (term669 y).
Proof. exact (@lem1982733 (term669 y)). Qed.
Lemma lem3129225 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3129226 (y : int) : (term756 y) = (term671 y).
Proof. exact (MK_COMB (@lem3129225) (@lem3129224 y)). Qed.
Lemma lem3129227 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3129228 (y : int) : (term754 y) = (term672 y).
Proof. exact (MK_COMB (@lem3129226 y) (@lem3129227)). Qed.
Lemma lem3129229 (y : int) (h1 : term746 y) : term672 y.
Proof. exact (EQ_MP (@lem3129228 y) (@lem3129223 y h1)). Qed.
Lemma lem3129231 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3129232 : term379 = term380.
Proof. exact (@lem3129231 term296 term275). Qed.
Lemma lem3129234 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3129235 : term275 = term326.
Proof. exact (@lem3129234 term22). Qed.
Lemma lem3129237 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3129238 : term296 = term381.
Proof. exact (@lem3129237 (NUMERAL 0)). Qed.
Lemma lem3129239 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3129240 : term382 = term383.
Proof. exact (MK_COMB (@lem3129239) (@lem3129238)). Qed.
Lemma lem3129241 : term380 = term384.
Proof. exact (MK_COMB (@lem3129240) (@lem3129235)). Qed.
Lemma lem3129242 : term385.
Proof. exact (@lem1980255 term296 term275 term275 term275). Qed.
Lemma lem3129244 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129245 : term380 = term387.
Proof. exact (@lem3129244 (NUMERAL 0) term22). Qed.
Lemma lem3129246 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129247 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129248 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129247 h1) (fun h1 : term387 = True => @lem3129246)). Qed.
Lemma lem3129249 : term387 = True.
Proof. exact (EQ_MP (@lem3129248) (@lem3129246)). Qed.
Lemma lem3129250 : term380 = True.
Proof. exact (TRANS (@lem3129245) (@lem3129249)). Qed.
Lemma lem3129251 : True = term380.
Proof. exact (SYM (@lem3129250)). Qed.
Lemma lem3129252 : term380.
Proof. exact (EQ_MP (@lem3129251) (@lem0)). Qed.
Lemma lem3129253 : term388.
Proof. exact (@lem3129242 (@lem3129252)). Qed.
Lemma lem3129255 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129256 : term380 = term387.
Proof. exact (@lem3129255 (NUMERAL 0) term22). Qed.
Lemma lem3129257 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129258 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129259 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129258 h1) (fun h1 : term387 = True => @lem3129257)). Qed.
Lemma lem3129260 : term387 = True.
Proof. exact (EQ_MP (@lem3129259) (@lem3129257)). Qed.
Lemma lem3129261 : term380 = True.
Proof. exact (TRANS (@lem3129256) (@lem3129260)). Qed.
Lemma lem3129262 : True = term380.
Proof. exact (SYM (@lem3129261)). Qed.
Lemma lem3129263 : term380.
Proof. exact (EQ_MP (@lem3129262) (@lem0)). Qed.
Lemma lem3129264 : term384 = term389.
Proof. exact (@lem3129253 (@lem3129263)). Qed.
Lemma lem3129266 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3129267 : term337 = term338.
Proof. exact (@lem3129266 term22 term22). Qed.
Lemma lem3129268 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3129269 : term340 = term22.
Proof. exact (EQ_MP (@lem3129268) (@lem940073)). Qed.
Lemma lem3129270 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3129271 : term338 = term275.
Proof. exact (MK_COMB (@lem3129270) (@lem3129269)). Qed.
Lemma lem3129272 : term337 = term275.
Proof. exact (TRANS (@lem3129267) (@lem3129271)). Qed.
Lemma lem3129274 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3129275 : term391 = term296.
Proof. exact (@lem3129274 term22). Qed.
Lemma lem3129276 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3129277 : term392 = term382.
Proof. exact (MK_COMB (@lem3129276) (@lem3129275)). Qed.
Lemma lem3129278 : term389 = term380.
Proof. exact (MK_COMB (@lem3129277) (@lem3129272)). Qed.
Lemma lem3129280 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129281 : term380 = term387.
Proof. exact (@lem3129280 (NUMERAL 0) term22). Qed.
Lemma lem3129282 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129283 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129284 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129283 h1) (fun h1 : term387 = True => @lem3129282)). Qed.
Lemma lem3129285 : term387 = True.
Proof. exact (EQ_MP (@lem3129284) (@lem3129282)). Qed.
Lemma lem3129286 : term380 = True.
Proof. exact (TRANS (@lem3129281) (@lem3129285)). Qed.
Lemma lem3129287 : term389 = True.
Proof. exact (TRANS (@lem3129278) (@lem3129286)). Qed.
Lemma lem3129288 : term384 = True.
Proof. exact (TRANS (@lem3129264) (@lem3129287)). Qed.
Lemma lem3129289 : term380 = True.
Proof. exact (TRANS (@lem3129241) (@lem3129288)). Qed.
Lemma lem3129290 : term379 = True.
Proof. exact (TRANS (@lem3129232) (@lem3129289)). Qed.
Lemma lem3129291 : True = term379.
Proof. exact (SYM (@lem3129290)). Qed.
Lemma lem3129292 : term379.
Proof. exact (EQ_MP (@lem3129291) (@lem0)). Qed.
Lemma lem3129293 (y : int) (h1 : term746 y) : term798 y.
Proof. exact (conj (@lem3129292) (@lem3129155 y h1)). Qed.
Lemma lem3129295 (x : real) (y : real) : term394 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3129296 (y : int) : term799 y.
Proof. exact (@lem3129295 term275 (term369 y)). Qed.
Lemma lem3129297 (y : int) (h1 : term746 y) : term800 y.
Proof. exact (@lem3129296 y (@lem3129293 y h1)). Qed.
Lemma lem3129298 (y : int) : (term801 y) = (term369 y).
Proof. exact (@lem1982733 (term369 y)). Qed.
Lemma lem3129299 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3129300 (y : int) : (term802 y) = (term803 y).
Proof. exact (MK_COMB (@lem3129299) (@lem3129298 y)). Qed.
Lemma lem3129301 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3129302 (y : int) : (term800 y) = (term797 y).
Proof. exact (MK_COMB (@lem3129300 y) (@lem3129301)). Qed.
Lemma lem3129303 (y : int) (h1 : term746 y) : term797 y.
Proof. exact (EQ_MP (@lem3129302 y) (@lem3129297 y h1)). Qed.
Lemma lem3129304 (y : int) (h1 : term746 y) : term804 y.
Proof. exact (conj (@lem3129303 y h1) (@lem3129229 y h1)). Qed.
Lemma lem3129306 (x : real) (y : real) : term405 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3129307 (y : int) : term805 y.
Proof. exact (@lem3129306 (term369 y) (term669 y)). Qed.
Lemma lem3129308 (y : int) (h1 : term746 y) : term806 y.
Proof. exact (@lem3129307 y (@lem3129304 y h1)). Qed.
Lemma lem3129309 (y : int) : (term807 y) = (term431 y).
Proof. exact (@lem1982763 (term369 y) (real_of_int y) term321). Qed.
Lemma lem3129310 (y : int) : (term410 y) = (term411 y).
Proof. exact (@lem1982713 term321 (real_of_int y)). Qed.
Lemma lem3129312 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3129313 : term275 = term326.
Proof. exact (@lem3129312 term22). Qed.
Lemma lem3129315 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3129316 : term321 = term329.
Proof. exact (@lem3129315 term22). Qed.
Lemma lem3129317 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3129318 : term412 = term413.
Proof. exact (MK_COMB (@lem3129317) (@lem3129316)). Qed.
Lemma lem3129319 : term414 = term415.
Proof. exact (MK_COMB (@lem3129318) (@lem3129313)). Qed.
Lemma lem3129320 : term416.
Proof. exact (@lem1981473 term321 term275 term275 term275 term296 term275). Qed.
Lemma lem3129322 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129323 : term380 = term387.
Proof. exact (@lem3129322 (NUMERAL 0) term22). Qed.
Lemma lem3129324 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129325 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129326 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129325 h1) (fun h1 : term387 = True => @lem3129324)). Qed.
Lemma lem3129327 : term387 = True.
Proof. exact (EQ_MP (@lem3129326) (@lem3129324)). Qed.
Lemma lem3129328 : term380 = True.
Proof. exact (TRANS (@lem3129323) (@lem3129327)). Qed.
Lemma lem3129329 : True = term380.
Proof. exact (SYM (@lem3129328)). Qed.
Lemma lem3129330 : term380.
Proof. exact (EQ_MP (@lem3129329) (@lem0)). Qed.
Lemma lem3129331 : term417.
Proof. exact (@lem3129320 (@lem3129330)). Qed.
Lemma lem3129333 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129334 : term380 = term387.
Proof. exact (@lem3129333 (NUMERAL 0) term22). Qed.
Lemma lem3129335 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129336 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129337 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129336 h1) (fun h1 : term387 = True => @lem3129335)). Qed.
Lemma lem3129338 : term387 = True.
Proof. exact (EQ_MP (@lem3129337) (@lem3129335)). Qed.
Lemma lem3129339 : term380 = True.
Proof. exact (TRANS (@lem3129334) (@lem3129338)). Qed.
Lemma lem3129340 : True = term380.
Proof. exact (SYM (@lem3129339)). Qed.
Lemma lem3129341 : term380.
Proof. exact (EQ_MP (@lem3129340) (@lem0)). Qed.
Lemma lem3129342 : term418.
Proof. exact (@lem3129331 (@lem3129341)). Qed.
Lemma lem3129344 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129345 : term380 = term387.
Proof. exact (@lem3129344 (NUMERAL 0) term22). Qed.
Lemma lem3129346 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129347 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129348 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129347 h1) (fun h1 : term387 = True => @lem3129346)). Qed.
Lemma lem3129349 : term387 = True.
Proof. exact (EQ_MP (@lem3129348) (@lem3129346)). Qed.
Lemma lem3129350 : term380 = True.
Proof. exact (TRANS (@lem3129345) (@lem3129349)). Qed.
Lemma lem3129351 : True = term380.
Proof. exact (SYM (@lem3129350)). Qed.
Lemma lem3129352 : term380.
Proof. exact (EQ_MP (@lem3129351) (@lem0)). Qed.
Lemma lem3129353 : term419.
Proof. exact (@lem3129342 (@lem3129352)). Qed.
Lemma lem3129355 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3129356 : term337 = term338.
Proof. exact (@lem3129355 term22 term22). Qed.
Lemma lem3129357 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3129358 : term340 = term22.
Proof. exact (EQ_MP (@lem3129357) (@lem940073)). Qed.
Lemma lem3129359 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3129360 : term338 = term275.
Proof. exact (MK_COMB (@lem3129359) (@lem3129358)). Qed.
Lemma lem3129361 : term337 = term275.
Proof. exact (TRANS (@lem3129356) (@lem3129360)). Qed.
Lemma lem3129363 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3129364 : term332 = term343.
Proof. exact (@lem3129363 term22 term22). Qed.
Lemma lem3129365 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3129366 : term340 = term22.
Proof. exact (EQ_MP (@lem3129365) (@lem940073)). Qed.
Lemma lem3129367 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3129368 : term338 = term275.
Proof. exact (MK_COMB (@lem3129367) (@lem3129366)). Qed.
Lemma lem3129369 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3129370 : term343 = term321.
Proof. exact (MK_COMB (@lem3129369) (@lem3129368)). Qed.
Lemma lem3129371 : term332 = term321.
Proof. exact (TRANS (@lem3129364) (@lem3129370)). Qed.
Lemma lem3129372 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3129373 : term420 = term412.
Proof. exact (MK_COMB (@lem3129372) (@lem3129371)). Qed.
Lemma lem3129374 : term421 = term414.
Proof. exact (MK_COMB (@lem3129373) (@lem3129361)). Qed.
Lemma lem3129376 (m : nat) : (term422 m) = term296.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3129377 : term414 = term296.
Proof. exact (@lem3129376 term22). Qed.
Lemma lem3129378 : term421 = term296.
Proof. exact (TRANS (@lem3129374) (@lem3129377)). Qed.
Lemma lem3129379 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3129380 : term423 = term424.
Proof. exact (MK_COMB (@lem3129379) (@lem3129378)). Qed.
Lemma lem3129381 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem3129382 : term425 = term391.
Proof. exact (MK_COMB (@lem3129380) (@lem3129381)). Qed.
Lemma lem3129384 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3129385 : term391 = term296.
Proof. exact (@lem3129384 term22). Qed.
Lemma lem3129386 : term425 = term296.
Proof. exact (TRANS (@lem3129382) (@lem3129385)). Qed.
Lemma lem3129388 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3129389 : term337 = term338.
Proof. exact (@lem3129388 term22 term22). Qed.
Lemma lem3129390 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3129391 : term340 = term22.
Proof. exact (EQ_MP (@lem3129390) (@lem940073)). Qed.
Lemma lem3129392 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3129393 : term338 = term275.
Proof. exact (MK_COMB (@lem3129392) (@lem3129391)). Qed.
Lemma lem3129394 : term337 = term275.
Proof. exact (TRANS (@lem3129389) (@lem3129393)). Qed.
Lemma lem3129395 : term424 = term424.
Proof. exact (eq_refl term424). Qed.
Lemma lem3129396 : term426 = term391.
Proof. exact (MK_COMB (@lem3129395) (@lem3129394)). Qed.
Lemma lem3129398 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3129399 : term391 = term296.
Proof. exact (@lem3129398 term22). Qed.
Lemma lem3129400 : term426 = term296.
Proof. exact (TRANS (@lem3129396) (@lem3129399)). Qed.
Lemma lem3129401 : term296 = term426.
Proof. exact (SYM (@lem3129400)). Qed.
Lemma lem3129402 : term425 = term426.
Proof. exact (TRANS (@lem3129386) (@lem3129401)). Qed.
Lemma lem3129403 : term415 = term381.
Proof. exact (@lem3129353 (@lem3129402)). Qed.
Lemma lem3129404 : term414 = term381.
Proof. exact (TRANS (@lem3129319) (@lem3129403)). Qed.
Lemma lem3129406 (x : real) : (term346 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3129407 : term381 = term296.
Proof. exact (@lem3129406 term296). Qed.
Lemma lem3129408 : term414 = term296.
Proof. exact (TRANS (@lem3129404) (@lem3129407)). Qed.
Lemma lem3129409 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3129410 : term427 = term424.
Proof. exact (MK_COMB (@lem3129409) (@lem3129408)). Qed.
Lemma lem3129411 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem3129412 (y : int) : (term411 y) = (term428 y).
Proof. exact (MK_COMB (@lem3129410) (@lem3129411 y)). Qed.
Lemma lem3129413 (y : int) : (term410 y) = (term428 y).
Proof. exact (TRANS (@lem3129310 y) (@lem3129412 y)). Qed.
Lemma lem3129414 (y : int) : (term428 y) = term296.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem3129415 (y : int) : (term410 y) = term296.
Proof. exact (TRANS (@lem3129413 y) (@lem3129414 y)). Qed.
Lemma lem3129416 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3129417 (y : int) : (term429 y) = term350.
Proof. exact (MK_COMB (@lem3129416) (@lem3129415 y)). Qed.
Lemma lem3129418 : term321 = term321.
Proof. exact (eq_refl term321). Qed.
Lemma lem3129419 (y : int) : (term431 y) = term432.
Proof. exact (MK_COMB (@lem3129417 y) (@lem3129418)). Qed.
Lemma lem3129420 (y : int) : (term807 y) = term432.
Proof. exact (TRANS (@lem3129309 y) (@lem3129419 y)). Qed.
Lemma lem3129421 : term432 = term321.
Proof. exact (@lem1982721 term321). Qed.
Lemma lem3129422 (y : int) : (term807 y) = term321.
Proof. exact (TRANS (@lem3129420 y) (@lem3129421)). Qed.
Lemma lem3129423 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3129424 (y : int) : (term808 y) = term434.
Proof. exact (MK_COMB (@lem3129423) (@lem3129422 y)). Qed.
Lemma lem3129425 : term296 = term296.
Proof. exact (eq_refl term296). Qed.
Lemma lem3129426 (y : int) : (term806 y) = term435.
Proof. exact (MK_COMB (@lem3129424 y) (@lem3129425)). Qed.
Lemma lem3129427 (y : int) (h1 : term746 y) : term435.
Proof. exact (EQ_MP (@lem3129426 y) (@lem3129308 y h1)). Qed.
Lemma lem3129429 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3129430 : term435 = term436.
Proof. exact (@lem3129429 term296 term321). Qed.
Lemma lem3129432 (x : nat) : (term327 x) = (term328 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3129433 : term321 = term329.
Proof. exact (@lem3129432 term22). Qed.
Lemma lem3129435 (x : nat) : (real_of_num x) = (term325 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3129436 : term296 = term381.
Proof. exact (@lem3129435 (NUMERAL 0)). Qed.
Lemma lem3129437 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3129438 : term437 = term438.
Proof. exact (MK_COMB (@lem3129437) (@lem3129436)). Qed.
Lemma lem3129439 : term436 = term439.
Proof. exact (MK_COMB (@lem3129438) (@lem3129433)). Qed.
Lemma lem3129440 : term440.
Proof. exact (@lem1980026 term296 term275 term321 term275). Qed.
Lemma lem3129442 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129443 : term380 = term387.
Proof. exact (@lem3129442 (NUMERAL 0) term22). Qed.
Lemma lem3129444 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129445 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129446 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129445 h1) (fun h1 : term387 = True => @lem3129444)). Qed.
Lemma lem3129447 : term387 = True.
Proof. exact (EQ_MP (@lem3129446) (@lem3129444)). Qed.
Lemma lem3129448 : term380 = True.
Proof. exact (TRANS (@lem3129443) (@lem3129447)). Qed.
Lemma lem3129449 : True = term380.
Proof. exact (SYM (@lem3129448)). Qed.
Lemma lem3129450 : term380.
Proof. exact (EQ_MP (@lem3129449) (@lem0)). Qed.
Lemma lem3129451 : term441.
Proof. exact (@lem3129440 (@lem3129450)). Qed.
Lemma lem3129453 (m : nat) (n : nat) : (term386 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3129454 : term380 = term387.
Proof. exact (@lem3129453 (NUMERAL 0) term22). Qed.
Lemma lem3129455 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129456 (h1 : term121 = (BIT1 0)) : term387 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3129457 : (term121 = (BIT1 0)) = (term387 = True).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129456 h1) (fun h1 : term387 = True => @lem3129455)). Qed.
Lemma lem3129458 : term387 = True.
Proof. exact (EQ_MP (@lem3129457) (@lem3129455)). Qed.
Lemma lem3129459 : term380 = True.
Proof. exact (TRANS (@lem3129454) (@lem3129458)). Qed.
Lemma lem3129460 : True = term380.
Proof. exact (SYM (@lem3129459)). Qed.
Lemma lem3129461 : term380.
Proof. exact (EQ_MP (@lem3129460) (@lem0)). Qed.
Lemma lem3129462 : term439 = term442.
Proof. exact (@lem3129451 (@lem3129461)). Qed.
Lemma lem3129464 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3129465 : term332 = term343.
Proof. exact (@lem3129464 term22 term22). Qed.
Lemma lem3129466 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3129467 : term340 = term22.
Proof. exact (EQ_MP (@lem3129466) (@lem940073)). Qed.
Lemma lem3129468 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3129469 : term338 = term275.
Proof. exact (MK_COMB (@lem3129468) (@lem3129467)). Qed.
Lemma lem3129470 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3129471 : term343 = term321.
Proof. exact (MK_COMB (@lem3129470) (@lem3129469)). Qed.
Lemma lem3129472 : term332 = term321.
Proof. exact (TRANS (@lem3129465) (@lem3129471)). Qed.
Lemma lem3129474 (x : nat) : (term390 x) = term296.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3129475 : term391 = term296.
Proof. exact (@lem3129474 term22). Qed.
Lemma lem3129476 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3129477 : term443 = term437.
Proof. exact (MK_COMB (@lem3129476) (@lem3129475)). Qed.
Lemma lem3129478 : term442 = term436.
Proof. exact (MK_COMB (@lem3129477) (@lem3129472)). Qed.
Lemma lem3129480 (m : nat) (n : nat) : (term444 m n) = (term445 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3129481 : term436 = term446.
Proof. exact (@lem3129480 (NUMERAL 0) term22). Qed.
Lemma lem3129482 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3129483 (h1 : term121 = (BIT1 0)) : (term22 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3129484 : (term121 = (BIT1 0)) = ((term22 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem3129483 h1) (fun h1 : (term22 = (NUMERAL 0)) = False => @lem3129482)). Qed.
Lemma lem3129485 : (term22 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3129484) (@lem3129482)). Qed.
Lemma lem3129486 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3129487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3129488 : term447 = (and True).
Proof. exact (MK_COMB (@lem3129487) (@lem3129486)). Qed.
Lemma lem3129489 : term446 = (True /\ False).
Proof. exact (MK_COMB (@lem3129488) (@lem3129485)). Qed.
Lemma lem3129491 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3129492 : term446 = False.
Proof. exact (TRANS (@lem3129489) (@lem3129491)). Qed.
Lemma lem3129493 : term436 = False.
Proof. exact (TRANS (@lem3129481) (@lem3129492)). Qed.
Lemma lem3129494 : term442 = False.
Proof. exact (TRANS (@lem3129478) (@lem3129493)). Qed.
Lemma lem3129495 : term439 = False.
Proof. exact (TRANS (@lem3129462) (@lem3129494)). Qed.
Lemma lem3129496 : term436 = False.
Proof. exact (TRANS (@lem3129439) (@lem3129495)). Qed.
Lemma lem3129497 : term435 = False.
Proof. exact (TRANS (@lem3129430) (@lem3129496)). Qed.
Lemma lem3129498 (y : int) (h1 : term746 y) : False.
Proof. exact (EQ_MP (@lem3129497) (@lem3129427 y h1)). Qed.
Lemma lem3129499 (y : int) (h1 : term749 y) : False.
Proof. exact (or_elim (@lem3128802 y h1) (fun h0 : term744 y => @lem3129150 y h0) (fun h0 : term746 y => @lem3129498 y h0)). Qed.
Lemma lem3129500 (x : int) (y : int) (h1 : term751 x y) : False.
Proof. exact (or_elim (@lem3127859 x y h1) (fun h0 : term737 y x => @lem3128801 y x h0) (fun h0 : term749 y => @lem3129499 y h0)). Qed.
Lemma lem3129501 (x : int) (y : int) (h1 : term719 x y) : term719 x y.
Proof. exact (h1). Qed.
Lemma lem3129502 (x : int) (y : int) (h1 : term719 x y) : term751 x y.
Proof. exact (EQ_MP (@lem3127858 x y) (@lem3129501 x y h1)). Qed.
Lemma lem3129503 (x : int) (y : int) (h1 : term719 x y) : (term751 x y) = False.
Proof. exact (prop_ext (fun h2 : term751 x y => @lem3129500 x y h2) (fun h2 : False => @lem3129502 x y h1)). Qed.
Lemma lem3129504 (x : int) (y : int) (h1 : term719 x y) : False.
Proof. exact (EQ_MP (@lem3129503 x y h1) (@lem3129502 x y h1)). Qed.
Lemma lem3129505 (x : int) (y : int) (h1 : term659 x y) : term659 x y.
Proof. exact (h1). Qed.
Lemma lem3129506 (x : int) (y : int) (h1 : term659 x y) : term719 x y.
Proof. exact (EQ_MP (@lem3127693 x y) (@lem3129505 x y h1)). Qed.
Lemma lem3129507 (x : int) (y : int) (h1 : term659 x y) : (term719 x y) = False.
Proof. exact (prop_ext (fun h2 : term719 x y => @lem3129504 x y h2) (fun h2 : False => @lem3129506 x y h1)). Qed.
Lemma lem3129508 (x : int) (y : int) (h1 : term659 x y) : False.
Proof. exact (EQ_MP (@lem3129507 x y h1) (@lem3129506 x y h1)). Qed.
Lemma lem3129509 (x : int) (y : int) : term809 x y.
Proof. exact (fun h0 : term659 x y => @lem3129508 x y h0). Qed.
Lemma lem3129510 (x : int) (y : int) : term810 x y.
Proof. exact (@lem1386578 (term811 x y)). Qed.
Lemma lem3129513 (x : int) (y : int) : term811 x y.
Proof. exact (@lem3129510 x y (@lem3129509 x y)). Qed.
Lemma lem3129514 (x : int) (y : int) : (term658 x y) = (term612 x y).
Proof. exact (SYM (@lem3127234 x y)). Qed.
Lemma lem3129515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3129516 (x : int) (y : int) : (term811 x y) = (term603 x y).
Proof. exact (MK_COMB (@lem3129515) (@lem3129514 x y)). Qed.
Lemma lem3129517 (x : int) (y : int) : term603 x y.
Proof. exact (EQ_MP (@lem3129516 x y) (@lem3129513 x y)). Qed.
Lemma lem3129518 (x : int) (y : int) : term604 x y.
Proof. exact (EQ_MP (@lem3127078 x y) (@lem3129517 x y)). Qed.
Lemma lem3129519 (x : int) (y : int) : (term604 x y) = ((term604 x y) = True).
Proof. exact (@lem7 (term604 x y)). Qed.
Lemma lem3129520 (x : int) (y : int) : (term604 x y) = True.
Proof. exact (EQ_MP (@lem3129519 x y) (@lem3129518 x y)). Qed.
Lemma lem3129521 (x : int) (y : int) : True = (term604 x y).
Proof. exact (SYM (@lem3129520 x y)). Qed.
Lemma lem3129522 (x : int) (y : int) : term604 x y.
Proof. exact (EQ_MP (@lem3129521 x y) (@lem0)). Qed.
Lemma lem3129523 (x : int) (y : int) (h1 : term135 y) : term613 x y.
Proof. exact (@lem3129522 x y (@lem3126088 y h1)). Qed.
Lemma lem3129524 (x : int) (y : int) (h1 : term135 y) : term601 x y.
Proof. exact (@lem3127077 x y (@lem3129523 x y h1)). Qed.
Lemma lem3129525 (x : int) (y : int) (h1 : term135 y) : term600 x y.
Proof. exact (EQ_MP (@lem3127074 x y) (@lem3129524 x y h1)). Qed.
Lemma lem3129526 (x : int) (y : int) (h1 : term135 y) : term462 x y.
Proof. exact (@lem3127069 x y (@lem3129525 x y h1)). Qed.
Lemma lem3129527 (x : int) (y : int) (h1 : term135 y) : term475 x y.
Proof. exact (EQ_MP (@lem3126179 x y h1) (@lem3129526 x y h1)). Qed.
Lemma lem3129528 (x : int) (y : int) (h1 : y = term10) : term475 x y.
Proof. exact (EQ_MP (@lem3126141 x y h1) (@lem3127066 x y h1)). Qed.
Lemma lem3129529 (x : int) (y : int) : term475 x y.
Proof. exact (or_elim (@lem3126086 y) (fun h0 : y = term10 => @lem3129528 x y h0) (fun h0 : term135 y => @lem3129527 x y h0)). Qed.
Lemma lem3129530 (y : int) (x : int) (h1 : term457 y x) : term462 x y.
Proof. exact (@lem3129529 x y (@lem3126092 y x h1)). Qed.
Lemma lem3129531 (x : int) (y : int) (h1 : (term463 x y) = (term459 x y)) : (term463 x y) = (term459 x y).
Proof. exact (h1). Qed.
Lemma lem3129532 (x : int) (y : int) : (term812 x y) = (term812 x y).
Proof. exact (eq_refl (term812 x y)). Qed.
Lemma lem3129533 (x : int) (y : int) (h1 : (term463 x y) = (term459 x y)) : (term813 x y) = (term814 x y).
Proof. exact (MK_COMB (@lem3129532 x y) (@lem3129531 x y h1)). Qed.
Lemma lem3129534 (x : int) (y : int) : (term814 x y) = (term815 x y).
Proof. exact (eq_refl (term814 x y)). Qed.
Lemma lem3129535 (x : int) (y : int) : (term816 x y) = (term816 x y).
Proof. exact (eq_refl (term816 x y)). Qed.
Lemma lem3129536 (x : int) (y : int) : ((term813 x y) = (term814 x y)) = ((term813 x y) = (term815 x y)).
Proof. exact (MK_COMB (@lem3129535 x y) (@lem3129534 x y)). Qed.
Lemma lem3129537 (x : int) (y : int) : (term813 x y) = (term464 x y).
Proof. exact (eq_refl (term813 x y)). Qed.
Lemma lem3129538 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3129539 (x : int) (y : int) : (term816 x y) = (term817 x y).
Proof. exact (MK_COMB (@lem3129538) (@lem3129537 x y)). Qed.
Lemma lem3129540 (x : int) (y : int) : (term815 x y) = (term815 x y).
Proof. exact (eq_refl (term815 x y)). Qed.
Lemma lem3129541 (x : int) (y : int) : ((term813 x y) = (term815 x y)) = ((term464 x y) = (term815 x y)).
Proof. exact (MK_COMB (@lem3129539 x y) (@lem3129540 x y)). Qed.
Lemma lem3129542 (x : int) (y : int) : ((term813 x y) = (term814 x y)) = ((term464 x y) = (term815 x y)).
Proof. exact (TRANS (@lem3129536 x y) (@lem3129541 x y)). Qed.
Lemma lem3129543 (x : int) (y : int) (h1 : (term463 x y) = (term459 x y)) : (term464 x y) = (term815 x y).
Proof. exact (EQ_MP (@lem3129542 x y) (@lem3129533 x y h1)). Qed.
Lemma lem3129544 (x : int) (y : int) (h1 : (term463 x y) = (term459 x y)) : (term815 x y) = (term464 x y).
Proof. exact (SYM (@lem3129543 x y h1)). Qed.
Lemma lem3129546 (x : int) (n : int) (a : int) : (term4 a x n) = (int_divides n a).
Proof. exact (EQ_MP (@lem3123815 x n a) (@lem3125280 x a n)). Qed.
Lemma lem3129547 (x : int) (y : int) : (term815 x y) = (term818 x y).
Proof. exact (@lem3129546 x y (term254 x y)). Qed.
Lemma lem3129548 (x : int) (y : int) : (term818 x y) = (term815 x y).
Proof. exact (SYM (@lem3129547 x y)). Qed.
Lemma lem3129550 (x : int) : (int_abs x) = (term1 x).
Proof. exact (EQ_MP (@lem3123786 x) (@lem3123785 x)). Qed.
Lemma lem3129551 (x : int) (y : int) : (term254 x y) = (term819 x y).
Proof. exact (@lem3129550 (int_mul x y)). Qed.
Lemma lem3129552 (y : int) : (int_divides y) = (int_divides y).
Proof. exact (eq_refl (int_divides y)). Qed.
Lemma lem3129553 (x : int) (y : int) : (term818 x y) = (term820 x y).
Proof. exact (MK_COMB (@lem3129552 y) (@lem3129551 x y)). Qed.
Lemma lem3129554 (x : int) (y : int) : (term820 x y) = (term818 x y).
Proof. exact (SYM (@lem3129553 x y)). Qed.
Lemma lem3129555 (_474 : int) (_475 : Prop) (_476 : int -> Prop) (_477 : int) : (term821 _476 _475 _474 _477) = (term822 _474 _475 _476 _477).
Proof. exact (@lem13473 int _474 _475 _476 _477). Qed.
Lemma lem3129556 (_474 : int) (_475 : Prop) (y : int) (_477 : int) : (term823 y _475 _474 _477) = (term824 _474 _475 y _477).
Proof. exact (@lem3129555 _474 _475 (term825 y) _477). Qed.
Lemma lem3129557 (x : int) (y : int) : (term826 x y) = (term827 x y).
Proof. exact (@lem3129556 (int_mul x y) (term828 x y) y (term829 x y)). Qed.
Lemma lem3129558 (x : int) (y : int) : (term830 x y) = (term831 x y).
Proof. exact (eq_refl (term830 x y)). Qed.
Lemma lem3129559 (x : int) (y : int) : (term832 x y) = (term832 x y).
Proof. exact (eq_refl (term832 x y)). Qed.
Lemma lem3129560 (x : int) (y : int) : (term833 x y) = (term834 x y).
Proof. exact (MK_COMB (@lem3129559 x y) (@lem3129558 x y)). Qed.
Lemma lem3129561 (x : int) (y : int) : (term835 x y) = (term836 x y).
Proof. exact (eq_refl (term835 x y)). Qed.
Lemma lem3129562 (x : int) (y : int) : (term837 x y) = (term837 x y).
Proof. exact (eq_refl (term837 x y)). Qed.
Lemma lem3129563 (x : int) (y : int) : (term838 x y) = (term839 x y).
Proof. exact (MK_COMB (@lem3129562 x y) (@lem3129561 x y)). Qed.
Lemma lem3129564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3129565 (x : int) (y : int) : (term840 x y) = (term841 x y).
Proof. exact (MK_COMB (@lem3129564) (@lem3129563 x y)). Qed.
Lemma lem3129566 (x : int) (y : int) : (term827 x y) = (term842 x y).
Proof. exact (MK_COMB (@lem3129565 x y) (@lem3129560 x y)). Qed.
Lemma lem3129567 (x : int) (y : int) : (term826 x y) = (term820 x y).
Proof. exact (eq_refl (term826 x y)). Qed.
Lemma lem3129568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3129569 (x : int) (y : int) : (term843 x y) = (term844 x y).
Proof. exact (MK_COMB (@lem3129568) (@lem3129567 x y)). Qed.
Lemma lem3129570 (x : int) (y : int) : ((term826 x y) = (term827 x y)) = ((term820 x y) = (term842 x y)).
Proof. exact (MK_COMB (@lem3129569 x y) (@lem3129566 x y)). Qed.
Lemma lem3129571 (x : int) (y : int) : (term820 x y) = (term842 x y).
Proof. exact (EQ_MP (@lem3129570 x y) (@lem3129557 x y)). Qed.
Lemma lem3129572 (x : int) (y : int) : (term842 x y) = (term820 x y).
Proof. exact (SYM (@lem3129571 x y)). Qed.
Lemma lem3129610 (b : int) (a : int) : (int_divides a b) = (term8 b a).
Proof. exact (EQ_MP (@lem2447298 b a) (@lem2447297 b a)). Qed.
Lemma lem3129611 (x : int) (y : int) : (term836 x y) = (term845 x y).
Proof. exact (@lem3129610 (int_mul x y) y). Qed.
Lemma lem3129618 (x : int) (y : int) : (term845 x y) = (term836 x y).
Proof. exact (SYM (@lem3129611 x y)). Qed.
Lemma lem3129710 (x : int) (y : int) : (x = y) = ((int_sub x y) = term10).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem3129711 (x : int) (y : int) (x' : int) : ((int_mul x y) = (int_mul y x')) = ((term846 x y x') = term10).
Proof. exact (@lem3129710 (int_mul x y) (int_mul y x')). Qed.
Lemma lem3129718 (x' : int) (y : int) : (int_mul y x') = (int_mul x' y).
Proof. exact (@lem2416549 x' y). Qed.
Lemma lem3129727 (x : int) (y : int) : (term27 x y) = (term27 x y).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem3129728 (x : int) (x' : int) (y : int) : (term846 x y x') = (term847 x x' y).
Proof. exact (MK_COMB (@lem3129727 x y) (@lem3129718 x' y)). Qed.
Lemma lem3129735 (x : int) (x' : int) (y : int) : (term847 x x' y) = (term848 x x' y).
Proof. exact (@lem2416594 (int_mul x y) (int_mul x' y)). Qed.
Lemma lem3129736 (x : int) (x' : int) (y : int) : (term846 x y x') = (term848 x x' y).
Proof. exact (TRANS (@lem3129728 x x' y) (@lem3129735 x x' y)). Qed.
Lemma lem3129737 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3129738 (x : int) (x' : int) (y : int) : (term849 x y x') = (term850 x x' y).
Proof. exact (MK_COMB (@lem3129737) (@lem3129736 x x' y)). Qed.
Lemma lem3129739 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3129740 (x : int) (x' : int) (y : int) : ((term846 x y x') = term10) = ((term848 x x' y) = term10).
Proof. exact (MK_COMB (@lem3129738 x x' y) (@lem3129739)). Qed.
Lemma lem3129741 (x : int) (x' : int) (y : int) : ((int_mul x y) = (int_mul y x')) = ((term848 x x' y) = term10).
Proof. exact (TRANS (@lem3129711 x y x') (@lem3129740 x x' y)). Qed.
Lemma lem3129742 (x : int) (y : int) : (term851 x y) = (term852 x y).
Proof. exact (fun_ext (fun x' : int => @lem3129741 x x' y)). Qed.
Lemma lem3129743 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3129744 (x : int) (y : int) : (term845 x y) = (term853 x y).
Proof. exact (MK_COMB (@lem3129743) (@lem3129742 x y)). Qed.
Lemma lem3129745 (x : int) (y : int) : (term853 x y) = (term845 x y).
Proof. exact (SYM (@lem3129744 x y)). Qed.
Lemma lem3129757 (x : int) (_32430 : int) (y : int) : ((term848 x _32430 y) = term10) = ((term848 x _32430 y) = term10).
Proof. exact (eq_refl ((term848 x _32430 y) = term10)). Qed.
Lemma lem3129758 (x : int) (y : int) : (term852 x y) = (term852 x y).
Proof. exact (fun_ext (fun _32430 : int => @lem3129757 x _32430 y)). Qed.
Lemma lem3129759 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3129761 (x : int) (y : int) : (term853 x y) = (term853 x y).
Proof. exact (MK_COMB (@lem3129759) (@lem3129758 x y)). Qed.
Lemma lem3129762 (x : int) (y : int) : (term853 x y) = (term853 x y).
Proof. exact (SYM (@lem3129761 x y)). Qed.
Lemma lem3129764 (x : int) (y : int) : (x = y) = ((int_sub x y) = term10).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem3129765 (x : int) (_32430 : int) (y : int) : ((term848 x _32430 y) = term10) = ((term854 x _32430 y) = term10).
Proof. exact (@lem3129764 (term848 x _32430 y) term10). Qed.
Lemma lem3129766 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3129791 (_32430 : int) (x : int) (y : int) : (term848 x _32430 y) = (term855 _32430 x y).
Proof. exact (@lem2416563 (term37 _32430 y) (int_mul x y)). Qed.
Lemma lem3129792 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem3129793 (_32430 : int) (x : int) (y : int) : (term856 x _32430 y) = (term857 _32430 x y).
Proof. exact (MK_COMB (@lem3129792) (@lem3129791 _32430 x y)). Qed.
Lemma lem3129794 (_32430 : int) (x : int) (y : int) : (term854 x _32430 y) = (term858 _32430 x y).
Proof. exact (MK_COMB (@lem3129793 _32430 x y) (@lem3129766)). Qed.
Lemma lem3129795 (_32430 : int) (x : int) (y : int) : (term858 _32430 x y) = (term859 _32430 x y).
Proof. exact (@lem2416594 (term855 _32430 x y) term10). Qed.
Lemma lem3129797 (x : nat) : (term60 x) = term10.
Proof. exact (proj2 (@lem2405764 x)). Qed.
Lemma lem3129798 : term61 = term10.
Proof. exact (@lem3129797 term22). Qed.
Lemma lem3129799 (_32430 : int) (x : int) (y : int) : (term860 _32430 x y) = (term860 _32430 x y).
Proof. exact (eq_refl (term860 _32430 x y)). Qed.
Lemma lem3129800 (_32430 : int) (x : int) (y : int) : (term859 _32430 x y) = (term861 _32430 x y).
Proof. exact (MK_COMB (@lem3129799 _32430 x y) (@lem3129798)). Qed.
Lemma lem3129801 (_32430 : int) (x : int) (y : int) : (term861 _32430 x y) = (term855 _32430 x y).
Proof. exact (@lem2416525 (term855 _32430 x y)). Qed.
Lemma lem3129802 (_32430 : int) (x : int) (y : int) : (term859 _32430 x y) = (term855 _32430 x y).
Proof. exact (TRANS (@lem3129800 _32430 x y) (@lem3129801 _32430 x y)). Qed.
Lemma lem3129803 (_32430 : int) (x : int) (y : int) : (term858 _32430 x y) = (term855 _32430 x y).
Proof. exact (TRANS (@lem3129795 _32430 x y) (@lem3129802 _32430 x y)). Qed.
Lemma lem3129804 (_32430 : int) (x : int) (y : int) : (term854 x _32430 y) = (term855 _32430 x y).
Proof. exact (TRANS (@lem3129794 _32430 x y) (@lem3129803 _32430 x y)). Qed.
Lemma lem3129805 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3129806 (_32430 : int) (x : int) (y : int) : (term862 x _32430 y) = (term863 _32430 x y).
Proof. exact (MK_COMB (@lem3129805) (@lem3129804 _32430 x y)). Qed.
Lemma lem3129807 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3129808 (_32430 : int) (x : int) (y : int) : ((term854 x _32430 y) = term10) = ((term855 _32430 x y) = term10).
Proof. exact (MK_COMB (@lem3129806 _32430 x y) (@lem3129807)). Qed.
Lemma lem3129809 (_32430 : int) (x : int) (y : int) : ((term848 x _32430 y) = term10) = ((term855 _32430 x y) = term10).
Proof. exact (TRANS (@lem3129765 x _32430 y) (@lem3129808 _32430 x y)). Qed.
Lemma lem3129810 (x : int) (y : int) : (term852 x y) = (term864 x y).
Proof. exact (fun_ext (fun _32430 : int => @lem3129809 _32430 x y)). Qed.
Lemma lem3129811 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3129812 (x : int) (y : int) : (term853 x y) = (term865 x y).
Proof. exact (MK_COMB (@lem3129811) (@lem3129810 x y)). Qed.
Lemma lem3129813 (x : int) (y : int) : (term865 x y) = (term853 x y).
Proof. exact (SYM (@lem3129812 x y)). Qed.
Lemma lem3129825 (x : int) (y : int) : ((term866 x y) = term10) = ((term866 x y) = term10).
Proof. exact (eq_refl ((term866 x y) = term10)). Qed.
Lemma lem3129826 (x : int) : (term867 x) = (term867 x).
Proof. exact (fun_ext (fun y : int => @lem3129825 x y)). Qed.
Lemma lem3129827 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3129828 (x : int) : (term868 x) = (term868 x).
Proof. exact (MK_COMB (@lem3129827) (@lem3129826 x)). Qed.
Lemma lem3129829 : term869 = term869.
Proof. exact (fun_ext (fun x : int => @lem3129828 x)). Qed.
Lemma lem3129830 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3129831 : term870 = term870.
Proof. exact (MK_COMB (@lem3129830) (@lem3129829)). Qed.
Lemma lem3129832 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3129834 : term871 = term871.
Proof. exact (MK_COMB (@lem3129832) (@lem3129831)). Qed.
Lemma lem3129836 (P : int -> Prop) : (term76 P) = (term77 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3129837 (x : int) : (term872 x) = (term873 x).
Proof. exact (@lem3129836 (term867 x)). Qed.
Lemma lem3129838 (x : int) (y : int) : (term874 x y) = ((term866 x y) = term10).
Proof. exact (eq_refl (term874 x y)). Qed.
Lemma lem3129839 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3129841 (x : int) (y : int) : (term875 x y) = (term876 x y).
Proof. exact (MK_COMB (@lem3129839) (@lem3129838 x y)). Qed.
Lemma lem3129842 (x : int) : (term877 x) = (term878 x).
Proof. exact (fun_ext (fun y : int => @lem3129841 x y)). Qed.
Lemma lem3129843 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3129844 (x : int) : (term873 x) = (term879 x).
Proof. exact (MK_COMB (@lem3129843) (@lem3129842 x)). Qed.
Lemma lem3129845 (x : int) : (term872 x) = (term879 x).
Proof. exact (TRANS (@lem3129837 x) (@lem3129844 x)). Qed.
Lemma lem3129846 (P : int -> Prop) : (term76 P) = (term77 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3129847 : term871 = term880.
Proof. exact (@lem3129846 term869). Qed.
Lemma lem3129848 (x : int) : (term881 x) = (term868 x).
Proof. exact (eq_refl (term881 x)). Qed.
Lemma lem3129849 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3129850 (x : int) : (term882 x) = (term872 x).
Proof. exact (MK_COMB (@lem3129849) (@lem3129848 x)). Qed.
Lemma lem3129851 (x : int) : (term882 x) = (term879 x).
Proof. exact (TRANS (@lem3129850 x) (@lem3129845 x)). Qed.
Lemma lem3129852 : term883 = term884.
Proof. exact (fun_ext (fun x : int => @lem3129851 x)). Qed.
Lemma lem3129853 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3129854 : term880 = term885.
Proof. exact (MK_COMB (@lem3129853) (@lem3129852)). Qed.
Lemma lem3129855 : term871 = term885.
Proof. exact (TRANS (@lem3129847) (@lem3129854)). Qed.
Lemma lem3129860 : term871 = term885.
Proof. exact (TRANS (@lem3129834) (@lem3129855)). Qed.
Lemma lem3129862 (x : int) (y : int) (h1 : term876 x y) : term876 x y.
Proof. exact (h1). Qed.
Lemma lem3129863 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3129870 (x : int) (y : int) : (int_mul x y) = (int_mul x y).
Proof. exact (eq_refl (int_mul x y)). Qed.
Lemma lem3129871 (y : int) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3129878 (x : int) : (term99 x) = x.
Proof. exact (@lem2416535 x). Qed.
Lemma lem3129879 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3129880 (x : int) : (term100 x) = (int_mul x).
Proof. exact (MK_COMB (@lem3129879) (@lem3129878 x)). Qed.
Lemma lem3129883 (x : int) (y : int) : (term101 x y) = (int_mul x y).
Proof. exact (MK_COMB (@lem3129880 x) (@lem3129871 y)). Qed.
Lemma lem3129886 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem3129889 (x : int) (y : int) : (term102 x y) = (term37 x y).
Proof. exact (MK_COMB (@lem3129886) (@lem3129883 x y)). Qed.
Lemma lem3129890 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3129891 (x : int) (y : int) : (term103 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem3129890) (@lem3129889 x y)). Qed.
Lemma lem3129892 (x : int) (y : int) : (term866 x y) = (term886 x y).
Proof. exact (MK_COMB (@lem3129891 x y) (@lem3129870 x y)). Qed.
Lemma lem3129893 (x : int) (y : int) : (term886 x y) = (term178 x y).
Proof. exact (@lem2416515 term19 (int_mul x y)). Qed.
Lemma lem3129895 (m : nat) : (term20 m) = term10.
Proof. exact (proj1 (@lem2405813 m)). Qed.
Lemma lem3129896 : term21 = term10.
Proof. exact (@lem3129895 term22). Qed.
Lemma lem3129897 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3129898 : term23 = term24.
Proof. exact (MK_COMB (@lem3129897) (@lem3129896)). Qed.
Lemma lem3129899 (x : int) (y : int) : (int_mul x y) = (int_mul x y).
Proof. exact (eq_refl (int_mul x y)). Qed.
Lemma lem3129900 (x : int) (y : int) : (term178 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem3129898) (@lem3129899 x y)). Qed.
Lemma lem3129901 (x : int) (y : int) : (term886 x y) = (term179 x y).
Proof. exact (TRANS (@lem3129893 x y) (@lem3129900 x y)). Qed.
Lemma lem3129902 (x : int) (y : int) : (term179 x y) = term10.
Proof. exact (@lem2416521 (int_mul x y)). Qed.
Lemma lem3129903 (x : int) (y : int) : (term886 x y) = term10.
Proof. exact (TRANS (@lem3129901 x y) (@lem3129902 x y)). Qed.
Lemma lem3129904 (x : int) (y : int) : (term866 x y) = term10.
Proof. exact (TRANS (@lem3129892 x y) (@lem3129903 x y)). Qed.
Lemma lem3129905 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3129906 (x : int) (y : int) : (term887 x y) = term183.
Proof. exact (MK_COMB (@lem3129905) (@lem3129904 x y)). Qed.
Lemma lem3129907 (x : int) (y : int) : ((term866 x y) = term10) = (term10 = term10).
Proof. exact (MK_COMB (@lem3129906 x y) (@lem3129863)). Qed.
Lemma lem3129908 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3129909 (x : int) (y : int) : (term876 x y) = term184.
Proof. exact (MK_COMB (@lem3129908) (@lem3129907 x y)). Qed.
Lemma lem3129910 (x : int) (y : int) (h1 : term876 x y) : term184.
Proof. exact (EQ_MP (@lem3129909 x y) (@lem3129862 x y h1)). Qed.
Lemma lem3129911 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3129912 : term185.
Proof. exact (@lem82 (term10 = term10)). Qed.
Lemma lem3129913 (x : int) (y : int) (h1 : term876 x y) : (term10 = term10) = False.
Proof. exact (@lem3129912 (@lem3129910 x y h1)). Qed.
Lemma lem3129914 (x : int) (y : int) (h1 : term876 x y) : False.
Proof. exact (EQ_MP (@lem3129913 x y h1) (@lem3129911)). Qed.
Lemma lem3129915 (x : int) (y : int) : term888 x y.
Proof. exact (fun h0 : term876 x y => @lem3129914 x y h0). Qed.
Lemma lem3129916 (x : int) (y : int) : (term888 x y) = (term889 x y).
Proof. exact (@lem69 (term876 x y)). Qed.
Lemma lem3129917 (x : int) (y : int) : term889 x y.
Proof. exact (EQ_MP (@lem3129916 x y) (@lem3129915 x y)). Qed.
Lemma lem3129918 (x : int) (y : int) : term890 x y.
Proof. exact (@lem82 (term876 x y)). Qed.
Lemma lem3129920 (x : int) (y : int) : (term876 x y) = False.
Proof. exact (@lem3129918 x y (@lem3129917 x y)). Qed.
Lemma lem3129921 (x : int) (y : int) : term891 x y.
Proof. exact (@lem93 (term876 x y)). Qed.
Lemma lem3129922 (x : int) (y : int) : term889 x y.
Proof. exact (@lem3129921 x y (@lem3129920 x y)). Qed.
Lemma lem3129923 (x : int) (y : int) : (term889 x y) = (term888 x y).
Proof. exact (@lem62 (term876 x y)). Qed.
Lemma lem3129924 (x : int) (y : int) : term888 x y.
Proof. exact (EQ_MP (@lem3129923 x y) (@lem3129922 x y)). Qed.
Lemma lem3129925 (x : int) (y : int) (h1 : term876 x y) : term876 x y.
Proof. exact (h1). Qed.
Lemma lem3129926 (x : int) (y : int) (h1 : term876 x y) : False.
Proof. exact (@lem3129924 x y (@lem3129925 x y h1)). Qed.
Lemma lem3129927 (x : int) (h1 : term879 x) : term879 x.
Proof. exact (h1). Qed.
Lemma lem3129928 (x : int) (h1 : term879 x) : False.
Proof. exact (ex_elim (@lem3129927 x h1) (fun y : int => fun h0 : term878 x y => @lem3129926 x y h0)). Qed.
Lemma lem3129929 (h1 : term885) : term885.
Proof. exact (h1). Qed.
Lemma lem3129930 (h1 : term885) : False.
Proof. exact (ex_elim (@lem3129929 h1) (fun x : int => fun h0 : term884 x => @lem3129928 x h0)). Qed.
Lemma lem3129931 : term892.
Proof. exact (fun h0 : term885 => @lem3129930 h0). Qed.
Lemma lem3129933 (p : Prop) (q : Prop) : term191 p q.
Proof. exact (EQ_MP (@lem1032627 p q) (@lem1032730 p q)). Qed.
Lemma lem3129934 (q : Prop) : term893 q.
Proof. exact (@lem3129933 term885 q). Qed.
Lemma lem3129937 (q : Prop) : term894 q.
Proof. exact (@lem3129934 q (@lem3129931)). Qed.
Lemma lem3129938 : term895.
Proof. exact (@lem3129937 term870). Qed.
Lemma lem3129939 : term870.
Proof. exact (@lem3129938 (@lem3129860)). Qed.
Lemma lem3129940 (x : int) : term881 x.
Proof. exact (@lem3129939 x). Qed.
Lemma lem3129941 (x : int) : (term881 x) = (term868 x).
Proof. exact (eq_refl (term881 x)). Qed.
Lemma lem3129942 (x : int) : term868 x.
Proof. exact (EQ_MP (@lem3129941 x) (@lem3129940 x)). Qed.
Lemma lem3129943 (x : int) (y : int) : term874 x y.
Proof. exact (@lem3129942 x y). Qed.
Lemma lem3129944 (x : int) (y : int) : (term874 x y) = ((term866 x y) = term10).
Proof. exact (eq_refl (term874 x y)). Qed.
Lemma lem3129945 (x : int) (y : int) : (term866 x y) = term10.
Proof. exact (EQ_MP (@lem3129944 x y) (@lem3129943 x y)). Qed.
Lemma lem3129946 (x : int) (y : int) : term865 x y.
Proof. exact (ex_intro (term864 x y) (term99 x) (@lem3129945 x y)). Qed.
Lemma lem3129947 (x : int) (y : int) : term853 x y.
Proof. exact (EQ_MP (@lem3129813 x y) (@lem3129946 x y)). Qed.
Lemma lem3129949 (x : int) (y : int) : term853 x y.
Proof. exact (EQ_MP (@lem3129762 x y) (@lem3129947 x y)). Qed.
Lemma lem3129953 (x : int) (y : int) : term845 x y.
Proof. exact (EQ_MP (@lem3129745 x y) (@lem3129949 x y)). Qed.
Lemma lem3129959 (b : int) (a : int) : (int_divides a b) = (term8 b a).
Proof. exact (EQ_MP (@lem2447298 b a) (@lem2447297 b a)). Qed.
Lemma lem3129960 (x : int) (y : int) : (term831 x y) = (term896 x y).
Proof. exact (@lem3129959 (term829 x y) y). Qed.
Lemma lem3129967 (x : int) (y : int) : (term896 x y) = (term831 x y).
Proof. exact (SYM (@lem3129960 x y)). Qed.
Lemma lem3130086 (x : int) (y : int) : (x = y) = ((int_sub x y) = term10).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem3130087 (x : int) (y : int) (x' : int) : ((term829 x y) = (int_mul y x')) = ((term897 x y x') = term10).
Proof. exact (@lem3130086 (term829 x y) (int_mul y x')). Qed.
Lemma lem3130094 (x' : int) (y : int) : (int_mul y x') = (int_mul x' y).
Proof. exact (@lem2416549 x' y). Qed.
Lemma lem3130107 (x : int) (y : int) : (term829 x y) = (term37 x y).
Proof. exact (@lem2416587 (int_mul x y)). Qed.
Lemma lem3130108 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem3130109 (x : int) (y : int) : (term898 x y) = (term899 x y).
Proof. exact (MK_COMB (@lem3130108) (@lem3130107 x y)). Qed.
Lemma lem3130110 (x : int) (x' : int) (y : int) : (term897 x y x') = (term900 x x' y).
Proof. exact (MK_COMB (@lem3130109 x y) (@lem3130094 x' y)). Qed.
Lemma lem3130117 (x : int) (x' : int) (y : int) : (term900 x x' y) = (term901 x x' y).
Proof. exact (@lem2416594 (term37 x y) (int_mul x' y)). Qed.
Lemma lem3130118 (x : int) (x' : int) (y : int) : (term897 x y x') = (term901 x x' y).
Proof. exact (TRANS (@lem3130110 x x' y) (@lem3130117 x x' y)). Qed.
Lemma lem3130119 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3130120 (x : int) (x' : int) (y : int) : (term902 x y x') = (term903 x x' y).
Proof. exact (MK_COMB (@lem3130119) (@lem3130118 x x' y)). Qed.
Lemma lem3130121 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3130122 (x : int) (x' : int) (y : int) : ((term897 x y x') = term10) = ((term901 x x' y) = term10).
Proof. exact (MK_COMB (@lem3130120 x x' y) (@lem3130121)). Qed.
Lemma lem3130123 (x : int) (x' : int) (y : int) : ((term829 x y) = (int_mul y x')) = ((term901 x x' y) = term10).
Proof. exact (TRANS (@lem3130087 x y x') (@lem3130122 x x' y)). Qed.
Lemma lem3130124 (x : int) (y : int) : (term904 x y) = (term905 x y).
Proof. exact (fun_ext (fun x' : int => @lem3130123 x x' y)). Qed.
Lemma lem3130125 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3130126 (x : int) (y : int) : (term896 x y) = (term906 x y).
Proof. exact (MK_COMB (@lem3130125) (@lem3130124 x y)). Qed.
Lemma lem3130127 (x : int) (y : int) : (term906 x y) = (term896 x y).
Proof. exact (SYM (@lem3130126 x y)). Qed.
Lemma lem3130139 (x : int) (_32431 : int) (y : int) : ((term901 x _32431 y) = term10) = ((term901 x _32431 y) = term10).
Proof. exact (eq_refl ((term901 x _32431 y) = term10)). Qed.
Lemma lem3130140 (x : int) (y : int) : (term905 x y) = (term905 x y).
Proof. exact (fun_ext (fun _32431 : int => @lem3130139 x _32431 y)). Qed.
Lemma lem3130141 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3130143 (x : int) (y : int) : (term906 x y) = (term906 x y).
Proof. exact (MK_COMB (@lem3130141) (@lem3130140 x y)). Qed.
Lemma lem3130144 (x : int) (y : int) : (term906 x y) = (term906 x y).
Proof. exact (SYM (@lem3130143 x y)). Qed.
Lemma lem3130146 (x : int) (y : int) : (x = y) = ((int_sub x y) = term10).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem3130147 (x : int) (_32431 : int) (y : int) : ((term901 x _32431 y) = term10) = ((term907 x _32431 y) = term10).
Proof. exact (@lem3130146 (term901 x _32431 y) term10). Qed.
Lemma lem3130148 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3130179 (_32431 : int) (x : int) (y : int) : (term901 x _32431 y) = (term901 _32431 x y).
Proof. exact (@lem2416563 (term37 _32431 y) (term37 x y)). Qed.
Lemma lem3130180 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem3130181 (_32431 : int) (x : int) (y : int) : (term908 x _32431 y) = (term908 _32431 x y).
Proof. exact (MK_COMB (@lem3130180) (@lem3130179 _32431 x y)). Qed.
Lemma lem3130182 (_32431 : int) (x : int) (y : int) : (term907 x _32431 y) = (term907 _32431 x y).
Proof. exact (MK_COMB (@lem3130181 _32431 x y) (@lem3130148)). Qed.
Lemma lem3130183 (_32431 : int) (x : int) (y : int) : (term907 _32431 x y) = (term909 _32431 x y).
Proof. exact (@lem2416594 (term901 _32431 x y) term10). Qed.
Lemma lem3130185 (x : nat) : (term60 x) = term10.
Proof. exact (proj2 (@lem2405764 x)). Qed.
Lemma lem3130186 : term61 = term10.
Proof. exact (@lem3130185 term22). Qed.
Lemma lem3130187 (_32431 : int) (x : int) (y : int) : (term910 _32431 x y) = (term910 _32431 x y).
Proof. exact (eq_refl (term910 _32431 x y)). Qed.
Lemma lem3130188 (_32431 : int) (x : int) (y : int) : (term909 _32431 x y) = (term911 _32431 x y).
Proof. exact (MK_COMB (@lem3130187 _32431 x y) (@lem3130186)). Qed.
Lemma lem3130189 (_32431 : int) (x : int) (y : int) : (term911 _32431 x y) = (term901 _32431 x y).
Proof. exact (@lem2416525 (term901 _32431 x y)). Qed.
Lemma lem3130190 (_32431 : int) (x : int) (y : int) : (term909 _32431 x y) = (term901 _32431 x y).
Proof. exact (TRANS (@lem3130188 _32431 x y) (@lem3130189 _32431 x y)). Qed.
Lemma lem3130191 (_32431 : int) (x : int) (y : int) : (term907 _32431 x y) = (term901 _32431 x y).
Proof. exact (TRANS (@lem3130183 _32431 x y) (@lem3130190 _32431 x y)). Qed.
Lemma lem3130192 (_32431 : int) (x : int) (y : int) : (term907 x _32431 y) = (term901 _32431 x y).
Proof. exact (TRANS (@lem3130182 _32431 x y) (@lem3130191 _32431 x y)). Qed.
Lemma lem3130193 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3130194 (_32431 : int) (x : int) (y : int) : (term912 x _32431 y) = (term903 _32431 x y).
Proof. exact (MK_COMB (@lem3130193) (@lem3130192 _32431 x y)). Qed.
Lemma lem3130195 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3130196 (_32431 : int) (x : int) (y : int) : ((term907 x _32431 y) = term10) = ((term901 _32431 x y) = term10).
Proof. exact (MK_COMB (@lem3130194 _32431 x y) (@lem3130195)). Qed.
Lemma lem3130197 (_32431 : int) (x : int) (y : int) : ((term901 x _32431 y) = term10) = ((term901 _32431 x y) = term10).
Proof. exact (TRANS (@lem3130147 x _32431 y) (@lem3130196 _32431 x y)). Qed.
Lemma lem3130198 (x : int) (y : int) : (term905 x y) = (term913 x y).
Proof. exact (fun_ext (fun _32431 : int => @lem3130197 _32431 x y)). Qed.
Lemma lem3130199 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3130200 (x : int) (y : int) : (term906 x y) = (term914 x y).
Proof. exact (MK_COMB (@lem3130199) (@lem3130198 x y)). Qed.
Lemma lem3130201 (x : int) (y : int) : (term914 x y) = (term906 x y).
Proof. exact (SYM (@lem3130200 x y)). Qed.
Lemma lem3130213 (x : int) (y : int) : ((term915 x y) = term10) = ((term915 x y) = term10).
Proof. exact (eq_refl ((term915 x y) = term10)). Qed.
Lemma lem3130214 (x : int) : (term916 x) = (term916 x).
Proof. exact (fun_ext (fun y : int => @lem3130213 x y)). Qed.
Lemma lem3130215 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3130216 (x : int) : (term917 x) = (term917 x).
Proof. exact (MK_COMB (@lem3130215) (@lem3130214 x)). Qed.
Lemma lem3130217 : term918 = term918.
Proof. exact (fun_ext (fun x : int => @lem3130216 x)). Qed.
Lemma lem3130218 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3130219 : term919 = term919.
Proof. exact (MK_COMB (@lem3130218) (@lem3130217)). Qed.
Lemma lem3130220 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3130222 : term920 = term920.
Proof. exact (MK_COMB (@lem3130220) (@lem3130219)). Qed.
Lemma lem3130224 (P : int -> Prop) : (term76 P) = (term77 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3130225 (x : int) : (term921 x) = (term922 x).
Proof. exact (@lem3130224 (term916 x)). Qed.
Lemma lem3130226 (x : int) (y : int) : (term923 x y) = ((term915 x y) = term10).
Proof. exact (eq_refl (term923 x y)). Qed.
Lemma lem3130227 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3130229 (x : int) (y : int) : (term924 x y) = (term925 x y).
Proof. exact (MK_COMB (@lem3130227) (@lem3130226 x y)). Qed.
Lemma lem3130230 (x : int) : (term926 x) = (term927 x).
Proof. exact (fun_ext (fun y : int => @lem3130229 x y)). Qed.
Lemma lem3130231 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3130232 (x : int) : (term922 x) = (term928 x).
Proof. exact (MK_COMB (@lem3130231) (@lem3130230 x)). Qed.
Lemma lem3130233 (x : int) : (term921 x) = (term928 x).
Proof. exact (TRANS (@lem3130225 x) (@lem3130232 x)). Qed.
Lemma lem3130234 (P : int -> Prop) : (term76 P) = (term77 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3130235 : term920 = term929.
Proof. exact (@lem3130234 term918). Qed.
Lemma lem3130236 (x : int) : (term930 x) = (term917 x).
Proof. exact (eq_refl (term930 x)). Qed.
Lemma lem3130237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3130238 (x : int) : (term931 x) = (term921 x).
Proof. exact (MK_COMB (@lem3130237) (@lem3130236 x)). Qed.
Lemma lem3130239 (x : int) : (term931 x) = (term928 x).
Proof. exact (TRANS (@lem3130238 x) (@lem3130233 x)). Qed.
Lemma lem3130240 : term932 = term933.
Proof. exact (fun_ext (fun x : int => @lem3130239 x)). Qed.
Lemma lem3130241 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3130242 : term929 = term934.
Proof. exact (MK_COMB (@lem3130241) (@lem3130240)). Qed.
Lemma lem3130243 : term920 = term934.
Proof. exact (TRANS (@lem3130235) (@lem3130242)). Qed.
Lemma lem3130248 : term920 = term934.
Proof. exact (TRANS (@lem3130222) (@lem3130243)). Qed.
Lemma lem3130250 (x : int) (y : int) (h1 : term925 x y) : term925 x y.
Proof. exact (h1). Qed.
Lemma lem3130251 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3130264 (x : int) (y : int) : (term37 x y) = (term37 x y).
Proof. exact (eq_refl (term37 x y)). Qed.
Lemma lem3130281 (x : int) (y : int) : (term935 x y) = (term37 x y).
Proof. exact (@lem2416547 term19 x y). Qed.
Lemma lem3130284 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem3130285 (x : int) (y : int) : (term936 x y) = (term937 x y).
Proof. exact (MK_COMB (@lem3130284) (@lem3130281 x y)). Qed.
Lemma lem3130286 (x : int) (y : int) : (term937 x y) = (term938 x y).
Proof. exact (@lem2416551 term19 term19 (int_mul x y)). Qed.
Lemma lem3130288 (m : nat) (n : nat) : (term939 m n) = (term940 m n).
Proof. exact (proj2 (@lem2405758 m n)). Qed.
Lemma lem3130289 : term941 = term942.
Proof. exact (@lem3130288 term22 term22). Qed.
Lemma lem3130290 : (term339 = (BIT1 0)) = (term340 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3130291 : term340 = term22.
Proof. exact (EQ_MP (@lem3130290) (@lem940073)). Qed.
Lemma lem3130292 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem3130293 : term942 = term110.
Proof. exact (MK_COMB (@lem3130292) (@lem3130291)). Qed.
Lemma lem3130294 : term941 = term110.
Proof. exact (TRANS (@lem3130289) (@lem3130293)). Qed.
Lemma lem3130295 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3130296 : term943 = term113.
Proof. exact (MK_COMB (@lem3130295) (@lem3130294)). Qed.
Lemma lem3130297 (x : int) (y : int) : (int_mul x y) = (int_mul x y).
Proof. exact (eq_refl (int_mul x y)). Qed.
Lemma lem3130298 (x : int) (y : int) : (term938 x y) = (term944 x y).
Proof. exact (MK_COMB (@lem3130296) (@lem3130297 x y)). Qed.
Lemma lem3130299 (x : int) (y : int) : (term937 x y) = (term944 x y).
Proof. exact (TRANS (@lem3130286 x y) (@lem3130298 x y)). Qed.
Lemma lem3130300 (x : int) (y : int) : (term944 x y) = (int_mul x y).
Proof. exact (@lem2416511 (int_mul x y)). Qed.
Lemma lem3130301 (x : int) (y : int) : (term937 x y) = (int_mul x y).
Proof. exact (TRANS (@lem3130299 x y) (@lem3130300 x y)). Qed.
Lemma lem3130302 (x : int) (y : int) : (term936 x y) = (int_mul x y).
Proof. exact (TRANS (@lem3130285 x y) (@lem3130301 x y)). Qed.
Lemma lem3130303 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3130304 (x : int) (y : int) : (term945 x y) = (term946 x y).
Proof. exact (MK_COMB (@lem3130303) (@lem3130302 x y)). Qed.
Lemma lem3130305 (x : int) (y : int) : (term915 x y) = (term177 x y).
Proof. exact (MK_COMB (@lem3130304 x y) (@lem3130264 x y)). Qed.
Lemma lem3130306 (x : int) (y : int) : (term177 x y) = (term178 x y).
Proof. exact (@lem2416517 term19 (int_mul x y)). Qed.
Lemma lem3130308 (m : nat) : (term20 m) = term10.
Proof. exact (proj1 (@lem2405813 m)). Qed.
Lemma lem3130309 : term21 = term10.
Proof. exact (@lem3130308 term22). Qed.
Lemma lem3130310 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3130311 : term23 = term24.
Proof. exact (MK_COMB (@lem3130310) (@lem3130309)). Qed.
Lemma lem3130312 (x : int) (y : int) : (int_mul x y) = (int_mul x y).
Proof. exact (eq_refl (int_mul x y)). Qed.
Lemma lem3130313 (x : int) (y : int) : (term178 x y) = (term179 x y).
Proof. exact (MK_COMB (@lem3130311) (@lem3130312 x y)). Qed.
Lemma lem3130314 (x : int) (y : int) : (term177 x y) = (term179 x y).
Proof. exact (TRANS (@lem3130306 x y) (@lem3130313 x y)). Qed.
Lemma lem3130315 (x : int) (y : int) : (term179 x y) = term10.
Proof. exact (@lem2416521 (int_mul x y)). Qed.
Lemma lem3130316 (x : int) (y : int) : (term177 x y) = term10.
Proof. exact (TRANS (@lem3130314 x y) (@lem3130315 x y)). Qed.
Lemma lem3130317 (x : int) (y : int) : (term915 x y) = term10.
Proof. exact (TRANS (@lem3130305 x y) (@lem3130316 x y)). Qed.
Lemma lem3130318 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3130319 (x : int) (y : int) : (term947 x y) = term183.
Proof. exact (MK_COMB (@lem3130318) (@lem3130317 x y)). Qed.
Lemma lem3130320 (x : int) (y : int) : ((term915 x y) = term10) = (term10 = term10).
Proof. exact (MK_COMB (@lem3130319 x y) (@lem3130251)). Qed.
Lemma lem3130321 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3130322 (x : int) (y : int) : (term925 x y) = term184.
Proof. exact (MK_COMB (@lem3130321) (@lem3130320 x y)). Qed.
Lemma lem3130323 (x : int) (y : int) (h1 : term925 x y) : term184.
Proof. exact (EQ_MP (@lem3130322 x y) (@lem3130250 x y h1)). Qed.
Lemma lem3130324 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem3130325 : term185.
Proof. exact (@lem82 (term10 = term10)). Qed.
Lemma lem3130326 (x : int) (y : int) (h1 : term925 x y) : (term10 = term10) = False.
Proof. exact (@lem3130325 (@lem3130323 x y h1)). Qed.
Lemma lem3130327 (x : int) (y : int) (h1 : term925 x y) : False.
Proof. exact (EQ_MP (@lem3130326 x y h1) (@lem3130324)). Qed.
Lemma lem3130328 (x : int) (y : int) : term948 x y.
Proof. exact (fun h0 : term925 x y => @lem3130327 x y h0). Qed.
Lemma lem3130329 (x : int) (y : int) : (term948 x y) = (term949 x y).
Proof. exact (@lem69 (term925 x y)). Qed.
Lemma lem3130330 (x : int) (y : int) : term949 x y.
Proof. exact (EQ_MP (@lem3130329 x y) (@lem3130328 x y)). Qed.
Lemma lem3130331 (x : int) (y : int) : term950 x y.
Proof. exact (@lem82 (term925 x y)). Qed.
Lemma lem3130333 (x : int) (y : int) : (term925 x y) = False.
Proof. exact (@lem3130331 x y (@lem3130330 x y)). Qed.
Lemma lem3130334 (x : int) (y : int) : term951 x y.
Proof. exact (@lem93 (term925 x y)). Qed.
Lemma lem3130335 (x : int) (y : int) : term949 x y.
Proof. exact (@lem3130334 x y (@lem3130333 x y)). Qed.
Lemma lem3130336 (x : int) (y : int) : (term949 x y) = (term948 x y).
Proof. exact (@lem62 (term925 x y)). Qed.
Lemma lem3130337 (x : int) (y : int) : term948 x y.
Proof. exact (EQ_MP (@lem3130336 x y) (@lem3130335 x y)). Qed.
Lemma lem3130338 (x : int) (y : int) (h1 : term925 x y) : term925 x y.
Proof. exact (h1). Qed.
Lemma lem3130339 (x : int) (y : int) (h1 : term925 x y) : False.
Proof. exact (@lem3130337 x y (@lem3130338 x y h1)). Qed.
Lemma lem3130340 (x : int) (h1 : term928 x) : term928 x.
Proof. exact (h1). Qed.
Lemma lem3130341 (x : int) (h1 : term928 x) : False.
Proof. exact (ex_elim (@lem3130340 x h1) (fun y : int => fun h0 : term927 x y => @lem3130339 x y h0)). Qed.
Lemma lem3130342 (h1 : term934) : term934.
Proof. exact (h1). Qed.
Lemma lem3130343 (h1 : term934) : False.
Proof. exact (ex_elim (@lem3130342 h1) (fun x : int => fun h0 : term933 x => @lem3130341 x h0)). Qed.
Lemma lem3130344 : term952.
Proof. exact (fun h0 : term934 => @lem3130343 h0). Qed.
Lemma lem3130346 (p : Prop) (q : Prop) : term191 p q.
Proof. exact (EQ_MP (@lem1032627 p q) (@lem1032730 p q)). Qed.
Lemma lem3130347 (q : Prop) : term953 q.
Proof. exact (@lem3130346 term934 q). Qed.
Lemma lem3130350 (q : Prop) : term954 q.
Proof. exact (@lem3130347 q (@lem3130344)). Qed.
Lemma lem3130351 : term955.
Proof. exact (@lem3130350 term919). Qed.
Lemma lem3130352 : term919.
Proof. exact (@lem3130351 (@lem3130248)). Qed.
Lemma lem3130353 (x : int) : term930 x.
Proof. exact (@lem3130352 x). Qed.
Lemma lem3130354 (x : int) : (term930 x) = (term917 x).
Proof. exact (eq_refl (term930 x)). Qed.
Lemma lem3130355 (x : int) : term917 x.
Proof. exact (EQ_MP (@lem3130354 x) (@lem3130353 x)). Qed.
Lemma lem3130356 (x : int) (y : int) : term923 x y.
Proof. exact (@lem3130355 x y). Qed.
Lemma lem3130357 (x : int) (y : int) : (term923 x y) = ((term915 x y) = term10).
Proof. exact (eq_refl (term923 x y)). Qed.
Lemma lem3130358 (x : int) (y : int) : (term915 x y) = term10.
Proof. exact (EQ_MP (@lem3130357 x y) (@lem3130356 x y)). Qed.
Lemma lem3130359 (x : int) (y : int) : term914 x y.
Proof. exact (ex_intro (term913 x y) (term16 x) (@lem3130358 x y)). Qed.
Lemma lem3130360 (x : int) (y : int) : term906 x y.
Proof. exact (EQ_MP (@lem3130201 x y) (@lem3130359 x y)). Qed.
Lemma lem3130362 (x : int) (y : int) : term906 x y.
Proof. exact (EQ_MP (@lem3130144 x y) (@lem3130360 x y)). Qed.
Lemma lem3130366 (x : int) (y : int) : term896 x y.
Proof. exact (EQ_MP (@lem3130127 x y) (@lem3130362 x y)). Qed.
Lemma lem3130369 (x : int) (y : int) : term831 x y.
Proof. exact (EQ_MP (@lem3129967 x y) (@lem3130366 x y)). Qed.
Lemma lem3130370 (x : int) (y : int) : term834 x y.
Proof. exact (fun h0 : term956 x y => @lem3130369 x y). Qed.
Lemma lem3130371 (x : int) (y : int) : term836 x y.
Proof. exact (EQ_MP (@lem3129618 x y) (@lem3129953 x y)). Qed.
Lemma lem3130372 (x : int) (y : int) : term839 x y.
Proof. exact (fun h0 : term828 x y => @lem3130371 x y). Qed.
Lemma lem3130373 (x : int) (y : int) : term842 x y.
Proof. exact (conj (@lem3130372 x y) (@lem3130370 x y)). Qed.
Lemma lem3130374 (x : int) (y : int) : term820 x y.
Proof. exact (EQ_MP (@lem3129572 x y) (@lem3130373 x y)). Qed.
Lemma lem3130375 (x : int) (y : int) : term818 x y.
Proof. exact (EQ_MP (@lem3129554 x y) (@lem3130374 x y)). Qed.
Lemma lem3130376 (x : int) (y : int) : term815 x y.
Proof. exact (EQ_MP (@lem3129548 x y) (@lem3130375 x y)). Qed.
Lemma lem3130377 (x : int) (y : int) (h1 : (term463 x y) = (term459 x y)) : term464 x y.
Proof. exact (EQ_MP (@lem3129544 x y h1) (@lem3130376 x y)). Qed.
Lemma lem3130378 (x : int) (y : int) : term957 x y.
Proof. exact (fun h0 : (term463 x y) = (term459 x y) => @lem3130377 x y h0). Qed.
Lemma lem3130379 (y : int) (x : int) (h1 : term457 y x) : term958 x y.
Proof. exact (conj (@lem3129530 y x h1) (@lem3130378 x y)). Qed.
Lemma lem3130380 (y : int) (x : int) (h1 : term457 y x) : term959 x y.
Proof. exact (@lem3126098 x y (@lem3130379 y x h1)). Qed.
Lemma lem3130381 (y : int) (x : int) (h1 : term457 y x) : term464 x y.
Proof. exact (@lem3130380 y x h1 (@lem3126095 x y)). Qed.
Lemma lem3130382 (y : int) (x : int) (h1 : term457 y x) : term960 x y.
Proof. exact (ex_intro (term961 x y) (term962 x y) (@lem3130381 y x h1)). Qed.
Lemma lem3130383 (y : int) (x : int) (h1 : term457 y x) : (term457 y x) = (term960 x y).
Proof. exact (prop_ext (fun h2 : term457 y x => @lem3130382 y x h1) (fun h2 : term960 x y => @lem3126092 y x h1)). Qed.
Lemma lem3130384 (y : int) (x : int) (h1 : term457 y x) : term960 x y.
Proof. exact (EQ_MP (@lem3130383 y x h1) (@lem3126092 y x h1)). Qed.
Lemma lem3130385 (x : int) (y : int) : term963 x y.
Proof. exact (fun h0 : term457 y x => @lem3130384 y x h0). Qed.
Lemma lem3130390 (x : int) : term964 x.
Proof. exact (fun y : int => @lem3130385 x y). Qed.
Lemma lem3130395 : term965.
Proof. exact (fun x : int => @lem3130390 x). Qed.
