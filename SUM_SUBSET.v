Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_SUBSET_term_abbrevs.
Require Import FINITE_DIFF_spec.
Require Import FINITE_INTER_spec.
Require Import REAL_LE_RNEG_spec.
Require Import SUM_NEG_spec.
Require Import SUM_POS_LE_spec.
Require Import SUM_UNION_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm1338512_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm137_spec.
Require Import thm1386578_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988297_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7169058 {A : Type'} (f : A -> real) (h1 : term0 A f) : term0 A f.
Proof. exact (h1). Qed.
Lemma lem7169059 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term0 A f) : term1 A f s.
Proof. exact (@lem7169058 A f h1 s). Qed.
Lemma lem7169060 {A : Type'} (s : A -> Prop) (f : A -> real) : (term1 A f s) = (term2 A s f).
Proof. exact (eq_refl (term1 A f s)). Qed.
Lemma lem7169061 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term0 A f) : term2 A s f.
Proof. exact (EQ_MP (@lem7169060 A s f) (@lem7169059 A s f h1)). Qed.
Lemma lem7169062 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term3 A s f) : term3 A s f.
Proof. exact (h1). Qed.
Lemma lem7169063 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term3 A s f) (h2 : term0 A f) : term4 A s f.
Proof. exact (@lem7169061 A s f h2 (@lem7169062 A s f h1)). Qed.
Lemma lem7169064 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term3 A s f) : term5 A s f.
Proof. exact (fun h0 : term0 A f => @lem7169063 A s f h1 h0). Qed.
Lemma lem7169065 {A : Type'} (f : A -> real) (h1 : term0 A f) : term0 A f.
Proof. exact (h1). Qed.
Lemma lem7169066 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term3 A s f) (h2 : term0 A f) : term4 A s f.
Proof. exact (@lem7169064 A s f h1 (@lem7169065 A f h2)). Qed.
Lemma lem7169067 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term0 A f) : term2 A s f.
Proof. exact (fun h0 : term3 A s f => @lem7169066 A s f h0 h1). Qed.
Lemma lem7169068 {A : Type'} (f : A -> real) (h1 : term0 A f) : term0 A f.
Proof. exact (fun s : A -> Prop => @lem7169067 A s f h1). Qed.
Lemma lem7169069 {A : Type'} (f : A -> real) : term6 A f.
Proof. exact (fun h0 : term0 A f => @lem7169068 A f h0). Qed.
Lemma lem7169070 {A : Type'} (f : A -> real) : term0 A f.
Proof. exact (@lem7169069 A f (@lem7085797 A f)). Qed.
Lemma lem7169071 {A : Type'} (f : A -> real) (s : A -> Prop) : term1 A f s.
Proof. exact (@lem7169070 A f s). Qed.
Lemma lem7169072 {A : Type'} (s : A -> Prop) (f : A -> real) : (term1 A f s) = (term2 A s f).
Proof. exact (eq_refl (term1 A f s)). Qed.
Lemma lem7169076 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) (h1 : (term7 _132004 s f) = (term8 _132004 s f)) : (term7 _132004 s f) = (term8 _132004 s f).
Proof. exact (h1). Qed.
Lemma lem7169077 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) (h1 : (term7 _132004 s f) = (term8 _132004 s f)) : (term8 _132004 s f) = (term7 _132004 s f).
Proof. exact (SYM (@lem7169076 _132004 s f h1)). Qed.
Lemma lem7169078 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) (h1 : (term8 _132004 s f) = (term7 _132004 s f)) : (term8 _132004 s f) = (term7 _132004 s f).
Proof. exact (h1). Qed.
Lemma lem7169079 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) (h1 : (term8 _132004 s f) = (term7 _132004 s f)) : (term7 _132004 s f) = (term8 _132004 s f).
Proof. exact (SYM (@lem7169078 _132004 s f h1)). Qed.
Lemma lem7169080 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : ((term7 _132004 s f) = (term8 _132004 s f)) = ((term8 _132004 s f) = (term7 _132004 s f)).
Proof. exact (prop_ext (fun h1 : (term7 _132004 s f) = (term8 _132004 s f) => @lem7169077 _132004 s f h1) (fun h1 : (term8 _132004 s f) = (term7 _132004 s f) => @lem7169079 _132004 s f h1)). Qed.
Lemma lem7169081 {_132004 : Type'} (f : _132004 -> real) : (term9 _132004 f) = (term10 _132004 f).
Proof. exact (fun_ext (fun s : _132004 -> Prop => @lem7169080 _132004 s f)). Qed.
Lemma lem7169082 {_132004 : Type'} : (@all (_132004 -> Prop)) = (@all (_132004 -> Prop)).
Proof. exact (eq_refl (@all (_132004 -> Prop))). Qed.
Lemma lem7169083 {_132004 : Type'} (f : _132004 -> real) : (term11 _132004 f) = (term12 _132004 f).
Proof. exact (MK_COMB (@lem7169082 _132004) (@lem7169081 _132004 f)). Qed.
Lemma lem7169084 {_132004 : Type'} : (term13 _132004) = (term14 _132004).
Proof. exact (fun_ext (fun f : _132004 -> real => @lem7169083 _132004 f)). Qed.
Lemma lem7169085 {_132004 : Type'} : (@all (_132004 -> real)) = (@all (_132004 -> real)).
Proof. exact (eq_refl (@all (_132004 -> real))). Qed.
Lemma lem7169086 {_132004 : Type'} : (term15 _132004) = (term16 _132004).
Proof. exact (MK_COMB (@lem7169085 _132004) (@lem7169084 _132004)). Qed.
Lemma lem7169087 {_132004 : Type'} : term16 _132004.
Proof. exact (EQ_MP (@lem7169086 _132004) (@lem7070827 _132004)). Qed.
Lemma lem7169119 (x : real) (a : real) (y : real) : (term17 x a y) = (term18 x a y).
Proof. exact (@lem17362 (term19 x y) (term20 x a y)). Qed.
Lemma lem7169120 (x : real) : (term21 x) = (term22 x).
Proof. exact (@lem1988287 (real_neg x) term23). Qed.
Lemma lem7169121 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7169128 (x : real) : (real_neg x) = (term24 x).
Proof. exact (@lem1982785 x). Qed.
Lemma lem7169129 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7169130 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem7169129) (@lem7169128 x)). Qed.
Lemma lem7169131 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem7169130 x) (@lem7169121)). Qed.
Lemma lem7169132 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1982792 (term24 x) term23). Qed.
Lemma lem7169134 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169135 : term23 = term31.
Proof. exact (@lem7169134 (NUMERAL 0)). Qed.
Lemma lem7169137 (x : nat) : (term32 x) = (term33 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7169138 : term34 = term35.
Proof. exact (@lem7169137 term36). Qed.
Lemma lem7169139 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7169140 : term37 = term38.
Proof. exact (MK_COMB (@lem7169139) (@lem7169138)). Qed.
Lemma lem7169141 : term39 = term40.
Proof. exact (MK_COMB (@lem7169140) (@lem7169135)). Qed.
Lemma lem7169142 : term40 = term41.
Proof. exact (@lem1981613 term34 term23 term42 term42). Qed.
Lemma lem7169144 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7169145 : term45 = term46.
Proof. exact (@lem7169144 term36 term36). Qed.
Lemma lem7169146 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169147 : term48 = term36.
Proof. exact (EQ_MP (@lem7169146) (@lem940073)). Qed.
Lemma lem7169148 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169149 : term46 = term42.
Proof. exact (MK_COMB (@lem7169148) (@lem7169147)). Qed.
Lemma lem7169150 : term45 = term42.
Proof. exact (TRANS (@lem7169145) (@lem7169149)). Qed.
Lemma lem7169152 (x : nat) : (term49 x) = term23.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7169153 : term39 = term23.
Proof. exact (@lem7169152 term36). Qed.
Lemma lem7169154 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7169155 : term50 = term51.
Proof. exact (MK_COMB (@lem7169154) (@lem7169153)). Qed.
Lemma lem7169156 : term41 = term31.
Proof. exact (MK_COMB (@lem7169155) (@lem7169150)). Qed.
Lemma lem7169157 : term40 = term31.
Proof. exact (TRANS (@lem7169142) (@lem7169156)). Qed.
Lemma lem7169158 : term39 = term31.
Proof. exact (TRANS (@lem7169141) (@lem7169157)). Qed.
Lemma lem7169160 (x : real) : (term52 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7169161 : term31 = term23.
Proof. exact (@lem7169160 term23). Qed.
Lemma lem7169162 : term39 = term23.
Proof. exact (TRANS (@lem7169158) (@lem7169161)). Qed.
Lemma lem7169163 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem7169164 (x : real) : (term29 x) = (term54 x).
Proof. exact (MK_COMB (@lem7169163 x) (@lem7169162)). Qed.
Lemma lem7169165 (x : real) : (term54 x) = (term24 x).
Proof. exact (@lem1982723 (term24 x)). Qed.
Lemma lem7169166 (x : real) : (term29 x) = (term24 x).
Proof. exact (TRANS (@lem7169164 x) (@lem7169165 x)). Qed.
Lemma lem7169167 (x : real) : (term28 x) = (term24 x).
Proof. exact (TRANS (@lem7169132 x) (@lem7169166 x)). Qed.
Lemma lem7169168 (x : real) : (term27 x) = (term24 x).
Proof. exact (TRANS (@lem7169131 x) (@lem7169167 x)). Qed.
Lemma lem7169169 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7169170 (x : real) : (term55 x) = (term56 x).
Proof. exact (MK_COMB (@lem7169169) (@lem7169168 x)). Qed.
Lemma lem7169171 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7169172 (x : real) : (term22 x) = (term57 x).
Proof. exact (MK_COMB (@lem7169170 x) (@lem7169171)). Qed.
Lemma lem7169173 (x : real) : (term21 x) = (term57 x).
Proof. exact (TRANS (@lem7169120 x) (@lem7169172 x)). Qed.
Lemma lem7169174 (y : real) : (term58 y) = (term59 y).
Proof. exact (@lem1988287 y term23). Qed.
Lemma lem7169180 (y : real) : (term60 y) = (term61 y).
Proof. exact (@lem1982792 y term23). Qed.
Lemma lem7169182 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169183 : term23 = term31.
Proof. exact (@lem7169182 (NUMERAL 0)). Qed.
Lemma lem7169185 (x : nat) : (term32 x) = (term33 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7169186 : term34 = term35.
Proof. exact (@lem7169185 term36). Qed.
Lemma lem7169187 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7169188 : term37 = term38.
Proof. exact (MK_COMB (@lem7169187) (@lem7169186)). Qed.
Lemma lem7169189 : term39 = term40.
Proof. exact (MK_COMB (@lem7169188) (@lem7169183)). Qed.
Lemma lem7169190 : term40 = term41.
Proof. exact (@lem1981613 term34 term23 term42 term42). Qed.
Lemma lem7169192 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7169193 : term45 = term46.
Proof. exact (@lem7169192 term36 term36). Qed.
Lemma lem7169194 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169195 : term48 = term36.
Proof. exact (EQ_MP (@lem7169194) (@lem940073)). Qed.
Lemma lem7169196 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169197 : term46 = term42.
Proof. exact (MK_COMB (@lem7169196) (@lem7169195)). Qed.
Lemma lem7169198 : term45 = term42.
Proof. exact (TRANS (@lem7169193) (@lem7169197)). Qed.
Lemma lem7169200 (x : nat) : (term49 x) = term23.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7169201 : term39 = term23.
Proof. exact (@lem7169200 term36). Qed.
Lemma lem7169202 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7169203 : term50 = term51.
Proof. exact (MK_COMB (@lem7169202) (@lem7169201)). Qed.
Lemma lem7169204 : term41 = term31.
Proof. exact (MK_COMB (@lem7169203) (@lem7169198)). Qed.
Lemma lem7169205 : term40 = term31.
Proof. exact (TRANS (@lem7169190) (@lem7169204)). Qed.
Lemma lem7169206 : term39 = term31.
Proof. exact (TRANS (@lem7169189) (@lem7169205)). Qed.
Lemma lem7169208 (x : real) : (term52 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7169209 : term31 = term23.
Proof. exact (@lem7169208 term23). Qed.
Lemma lem7169210 : term39 = term23.
Proof. exact (TRANS (@lem7169206) (@lem7169209)). Qed.
Lemma lem7169211 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem7169212 (y : real) : (term61 y) = (term62 y).
Proof. exact (MK_COMB (@lem7169211 y) (@lem7169210)). Qed.
Lemma lem7169213 (y : real) : (term62 y) = y.
Proof. exact (@lem1982723 y). Qed.
Lemma lem7169214 (y : real) : (term61 y) = y.
Proof. exact (TRANS (@lem7169212 y) (@lem7169213 y)). Qed.
Lemma lem7169216 (y : real) : (term60 y) = y.
Proof. exact (TRANS (@lem7169180 y) (@lem7169214 y)). Qed.
Lemma lem7169217 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7169218 (y : real) : (term63 y) = (real_ge y).
Proof. exact (MK_COMB (@lem7169217) (@lem7169216 y)). Qed.
Lemma lem7169219 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7169220 (y : real) : (term59 y) = (term64 y).
Proof. exact (MK_COMB (@lem7169218 y) (@lem7169219)). Qed.
Lemma lem7169221 (y : real) : (term58 y) = (term64 y).
Proof. exact (TRANS (@lem7169174 y) (@lem7169220 y)). Qed.
Lemma lem7169222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7169223 (x : real) : (term65 x) = (term66 x).
Proof. exact (MK_COMB (@lem7169222) (@lem7169173 x)). Qed.
Lemma lem7169224 (x : real) (y : real) : (term19 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem7169223 x) (@lem7169221 y)). Qed.
Lemma lem7169225 (x : real) (a : real) (y : real) : (term68 x a y) = (term69 x a y).
Proof. exact (@lem1988297 (real_add a x) (real_add a y)). Qed.
Lemma lem7169243 (x : real) (a : real) (y : real) : (term70 x a y) = (term71 x a y).
Proof. exact (@lem1982792 (real_add a x) (real_add a y)). Qed.
Lemma lem7169250 (a : real) (y : real) : (term72 a y) = (term73 a y).
Proof. exact (@lem1982781 a term34 y). Qed.
Lemma lem7169251 (a : real) (x : real) : (term74 a x) = (term74 a x).
Proof. exact (eq_refl (term74 a x)). Qed.
Lemma lem7169252 (x : real) (a : real) (y : real) : (term71 x a y) = (term75 x a y).
Proof. exact (MK_COMB (@lem7169251 a x) (@lem7169250 a y)). Qed.
Lemma lem7169253 (a : real) (x : real) (y : real) : (term75 x a y) = (term76 a x y).
Proof. exact (@lem1982753 a (term24 a) x (term24 y)). Qed.
Lemma lem7169254 (a : real) : (term77 a) = (term78 a).
Proof. exact (@lem1982715 term34 a). Qed.
Lemma lem7169256 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169257 : term42 = term79.
Proof. exact (@lem7169256 term36). Qed.
Lemma lem7169259 (x : nat) : (term32 x) = (term33 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7169260 : term34 = term35.
Proof. exact (@lem7169259 term36). Qed.
Lemma lem7169261 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7169262 : term80 = term81.
Proof. exact (MK_COMB (@lem7169261) (@lem7169260)). Qed.
Lemma lem7169263 : term82 = term83.
Proof. exact (MK_COMB (@lem7169262) (@lem7169257)). Qed.
Lemma lem7169264 : term84.
Proof. exact (@lem1981473 term34 term42 term42 term42 term23 term42). Qed.
Lemma lem7169266 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169267 : term86 = term87.
Proof. exact (@lem7169266 (NUMERAL 0) term36). Qed.
Lemma lem7169268 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169269 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169270 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169269 h1) (fun h1 : term87 = True => @lem7169268)). Qed.
Lemma lem7169271 : term87 = True.
Proof. exact (EQ_MP (@lem7169270) (@lem7169268)). Qed.
Lemma lem7169272 : term86 = True.
Proof. exact (TRANS (@lem7169267) (@lem7169271)). Qed.
Lemma lem7169273 : True = term86.
Proof. exact (SYM (@lem7169272)). Qed.
Lemma lem7169274 : term86.
Proof. exact (EQ_MP (@lem7169273) (@lem0)). Qed.
Lemma lem7169275 : term89.
Proof. exact (@lem7169264 (@lem7169274)). Qed.
Lemma lem7169277 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169278 : term86 = term87.
Proof. exact (@lem7169277 (NUMERAL 0) term36). Qed.
Lemma lem7169279 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169280 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169281 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169280 h1) (fun h1 : term87 = True => @lem7169279)). Qed.
Lemma lem7169282 : term87 = True.
Proof. exact (EQ_MP (@lem7169281) (@lem7169279)). Qed.
Lemma lem7169283 : term86 = True.
Proof. exact (TRANS (@lem7169278) (@lem7169282)). Qed.
Lemma lem7169284 : True = term86.
Proof. exact (SYM (@lem7169283)). Qed.
Lemma lem7169285 : term86.
Proof. exact (EQ_MP (@lem7169284) (@lem0)). Qed.
Lemma lem7169286 : term90.
Proof. exact (@lem7169275 (@lem7169285)). Qed.
Lemma lem7169288 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169289 : term86 = term87.
Proof. exact (@lem7169288 (NUMERAL 0) term36). Qed.
Lemma lem7169290 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169291 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169292 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169291 h1) (fun h1 : term87 = True => @lem7169290)). Qed.
Lemma lem7169293 : term87 = True.
Proof. exact (EQ_MP (@lem7169292) (@lem7169290)). Qed.
Lemma lem7169294 : term86 = True.
Proof. exact (TRANS (@lem7169289) (@lem7169293)). Qed.
Lemma lem7169295 : True = term86.
Proof. exact (SYM (@lem7169294)). Qed.
Lemma lem7169296 : term86.
Proof. exact (EQ_MP (@lem7169295) (@lem0)). Qed.
Lemma lem7169297 : term91.
Proof. exact (@lem7169286 (@lem7169296)). Qed.
Lemma lem7169299 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7169300 : term45 = term46.
Proof. exact (@lem7169299 term36 term36). Qed.
Lemma lem7169301 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169302 : term48 = term36.
Proof. exact (EQ_MP (@lem7169301) (@lem940073)). Qed.
Lemma lem7169303 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169304 : term46 = term42.
Proof. exact (MK_COMB (@lem7169303) (@lem7169302)). Qed.
Lemma lem7169305 : term45 = term42.
Proof. exact (TRANS (@lem7169300) (@lem7169304)). Qed.
Lemma lem7169307 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7169308 : term94 = term95.
Proof. exact (@lem7169307 term36 term36). Qed.
Lemma lem7169309 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169310 : term48 = term36.
Proof. exact (EQ_MP (@lem7169309) (@lem940073)). Qed.
Lemma lem7169311 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169312 : term46 = term42.
Proof. exact (MK_COMB (@lem7169311) (@lem7169310)). Qed.
Lemma lem7169313 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7169314 : term95 = term34.
Proof. exact (MK_COMB (@lem7169313) (@lem7169312)). Qed.
Lemma lem7169315 : term94 = term34.
Proof. exact (TRANS (@lem7169308) (@lem7169314)). Qed.
Lemma lem7169316 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7169317 : term96 = term80.
Proof. exact (MK_COMB (@lem7169316) (@lem7169315)). Qed.
Lemma lem7169318 : term97 = term82.
Proof. exact (MK_COMB (@lem7169317) (@lem7169305)). Qed.
Lemma lem7169320 (m : nat) : (term98 m) = term23.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7169321 : term82 = term23.
Proof. exact (@lem7169320 term36). Qed.
Lemma lem7169322 : term97 = term23.
Proof. exact (TRANS (@lem7169318) (@lem7169321)). Qed.
Lemma lem7169323 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7169324 : term99 = term100.
Proof. exact (MK_COMB (@lem7169323) (@lem7169322)). Qed.
Lemma lem7169325 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem7169326 : term101 = term102.
Proof. exact (MK_COMB (@lem7169324) (@lem7169325)). Qed.
Lemma lem7169328 (x : nat) : (term103 x) = term23.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7169329 : term102 = term23.
Proof. exact (@lem7169328 term36). Qed.
Lemma lem7169330 : term101 = term23.
Proof. exact (TRANS (@lem7169326) (@lem7169329)). Qed.
Lemma lem7169332 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7169333 : term45 = term46.
Proof. exact (@lem7169332 term36 term36). Qed.
Lemma lem7169334 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169335 : term48 = term36.
Proof. exact (EQ_MP (@lem7169334) (@lem940073)). Qed.
Lemma lem7169336 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169337 : term46 = term42.
Proof. exact (MK_COMB (@lem7169336) (@lem7169335)). Qed.
Lemma lem7169338 : term45 = term42.
Proof. exact (TRANS (@lem7169333) (@lem7169337)). Qed.
Lemma lem7169339 : term100 = term100.
Proof. exact (eq_refl term100). Qed.
Lemma lem7169340 : term104 = term102.
Proof. exact (MK_COMB (@lem7169339) (@lem7169338)). Qed.
Lemma lem7169342 (x : nat) : (term103 x) = term23.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7169343 : term102 = term23.
Proof. exact (@lem7169342 term36). Qed.
Lemma lem7169344 : term104 = term23.
Proof. exact (TRANS (@lem7169340) (@lem7169343)). Qed.
Lemma lem7169345 : term23 = term104.
Proof. exact (SYM (@lem7169344)). Qed.
Lemma lem7169346 : term101 = term104.
Proof. exact (TRANS (@lem7169330) (@lem7169345)). Qed.
Lemma lem7169347 : term83 = term31.
Proof. exact (@lem7169297 (@lem7169346)). Qed.
Lemma lem7169348 : term82 = term31.
Proof. exact (TRANS (@lem7169263) (@lem7169347)). Qed.
Lemma lem7169350 (x : real) : (term52 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7169351 : term31 = term23.
Proof. exact (@lem7169350 term23). Qed.
Lemma lem7169352 : term82 = term23.
Proof. exact (TRANS (@lem7169348) (@lem7169351)). Qed.
Lemma lem7169353 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7169354 : term105 = term100.
Proof. exact (MK_COMB (@lem7169353) (@lem7169352)). Qed.
Lemma lem7169355 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7169356 (a : real) : (term78 a) = (term106 a).
Proof. exact (MK_COMB (@lem7169354) (@lem7169355 a)). Qed.
Lemma lem7169357 (a : real) : (term77 a) = (term106 a).
Proof. exact (TRANS (@lem7169254 a) (@lem7169356 a)). Qed.
Lemma lem7169358 (a : real) : (term106 a) = term23.
Proof. exact (@lem1982719 a). Qed.
Lemma lem7169359 (a : real) : (term77 a) = term23.
Proof. exact (TRANS (@lem7169357 a) (@lem7169358 a)). Qed.
Lemma lem7169360 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7169361 (a : real) : (term107 a) = term108.
Proof. exact (MK_COMB (@lem7169360) (@lem7169359 a)). Qed.
Lemma lem7169362 (x : real) (y : real) : (term109 x y) = (term109 x y).
Proof. exact (eq_refl (term109 x y)). Qed.
Lemma lem7169363 (a : real) (x : real) (y : real) : (term76 a x y) = (term110 x y).
Proof. exact (MK_COMB (@lem7169361 a) (@lem7169362 x y)). Qed.
Lemma lem7169364 (a : real) (x : real) (y : real) : (term75 x a y) = (term110 x y).
Proof. exact (TRANS (@lem7169253 a x y) (@lem7169363 a x y)). Qed.
Lemma lem7169365 (x : real) (y : real) : (term110 x y) = (term109 x y).
Proof. exact (@lem1982721 (term109 x y)). Qed.
Lemma lem7169366 (a : real) (x : real) (y : real) : (term75 x a y) = (term109 x y).
Proof. exact (TRANS (@lem7169364 a x y) (@lem7169365 x y)). Qed.
Lemma lem7169367 (a : real) (x : real) (y : real) : (term71 x a y) = (term109 x y).
Proof. exact (TRANS (@lem7169252 x a y) (@lem7169366 a x y)). Qed.
Lemma lem7169369 (a : real) (x : real) (y : real) : (term70 x a y) = (term109 x y).
Proof. exact (TRANS (@lem7169243 x a y) (@lem7169367 a x y)). Qed.
Lemma lem7169370 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7169371 (a : real) (x : real) (y : real) : (term111 x a y) = (term112 x y).
Proof. exact (MK_COMB (@lem7169370) (@lem7169369 a x y)). Qed.
Lemma lem7169372 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7169373 (a : real) (x : real) (y : real) : (term69 x a y) = (term113 x y).
Proof. exact (MK_COMB (@lem7169371 a x y) (@lem7169372)). Qed.
Lemma lem7169374 (a : real) (x : real) (y : real) : (term68 x a y) = (term113 x y).
Proof. exact (TRANS (@lem7169225 x a y) (@lem7169373 a x y)). Qed.
Lemma lem7169375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7169376 (x : real) (y : real) : (term114 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem7169375) (@lem7169224 x y)). Qed.
Lemma lem7169377 (a : real) (x : real) (y : real) : (term18 x a y) = (term116 x y).
Proof. exact (MK_COMB (@lem7169376 x y) (@lem7169374 a x y)). Qed.
Lemma lem7169398 (a : real) (x : real) (y : real) : (term17 x a y) = (term116 x y).
Proof. exact (TRANS (@lem7169119 x a y) (@lem7169377 a x y)). Qed.
Lemma lem7169402 (x : real) (y : real) (h1 : term116 x y) : term116 x y.
Proof. exact (h1). Qed.
Lemma lem7169403 (x : real) (y : real) (h1 : term116 x y) : term113 x y.
Proof. exact (proj2 (@lem7169402 x y h1)). Qed.
Lemma lem7169404 (x : real) (y : real) (h1 : term116 x y) : term67 x y.
Proof. exact (proj1 (@lem7169402 x y h1)). Qed.
Lemma lem7169405 (x : real) (y : real) (h1 : term116 x y) : term64 y.
Proof. exact (proj2 (@lem7169404 x y h1)). Qed.
Lemma lem7169406 (x : real) (y : real) (h1 : term116 x y) : term57 x.
Proof. exact (proj1 (@lem7169404 x y h1)). Qed.
Lemma lem7169408 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7169409 : term117 = term86.
Proof. exact (@lem7169408 term23 term42). Qed.
Lemma lem7169411 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169412 : term42 = term79.
Proof. exact (@lem7169411 term36). Qed.
Lemma lem7169414 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169415 : term23 = term31.
Proof. exact (@lem7169414 (NUMERAL 0)). Qed.
Lemma lem7169416 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7169417 : term118 = term119.
Proof. exact (MK_COMB (@lem7169416) (@lem7169415)). Qed.
Lemma lem7169418 : term86 = term120.
Proof. exact (MK_COMB (@lem7169417) (@lem7169412)). Qed.
Lemma lem7169419 : term121.
Proof. exact (@lem1980255 term23 term42 term42 term42). Qed.
Lemma lem7169421 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169422 : term86 = term87.
Proof. exact (@lem7169421 (NUMERAL 0) term36). Qed.
Lemma lem7169423 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169424 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169425 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169424 h1) (fun h1 : term87 = True => @lem7169423)). Qed.
Lemma lem7169426 : term87 = True.
Proof. exact (EQ_MP (@lem7169425) (@lem7169423)). Qed.
Lemma lem7169427 : term86 = True.
Proof. exact (TRANS (@lem7169422) (@lem7169426)). Qed.
Lemma lem7169428 : True = term86.
Proof. exact (SYM (@lem7169427)). Qed.
Lemma lem7169429 : term86.
Proof. exact (EQ_MP (@lem7169428) (@lem0)). Qed.
Lemma lem7169430 : term122.
Proof. exact (@lem7169419 (@lem7169429)). Qed.
Lemma lem7169432 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169433 : term86 = term87.
Proof. exact (@lem7169432 (NUMERAL 0) term36). Qed.
Lemma lem7169434 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169435 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169436 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169435 h1) (fun h1 : term87 = True => @lem7169434)). Qed.
Lemma lem7169437 : term87 = True.
Proof. exact (EQ_MP (@lem7169436) (@lem7169434)). Qed.
Lemma lem7169438 : term86 = True.
Proof. exact (TRANS (@lem7169433) (@lem7169437)). Qed.
Lemma lem7169439 : True = term86.
Proof. exact (SYM (@lem7169438)). Qed.
Lemma lem7169440 : term86.
Proof. exact (EQ_MP (@lem7169439) (@lem0)). Qed.
Lemma lem7169441 : term120 = term123.
Proof. exact (@lem7169430 (@lem7169440)). Qed.
Lemma lem7169443 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7169444 : term45 = term46.
Proof. exact (@lem7169443 term36 term36). Qed.
Lemma lem7169445 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169446 : term48 = term36.
Proof. exact (EQ_MP (@lem7169445) (@lem940073)). Qed.
Lemma lem7169447 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169448 : term46 = term42.
Proof. exact (MK_COMB (@lem7169447) (@lem7169446)). Qed.
Lemma lem7169449 : term45 = term42.
Proof. exact (TRANS (@lem7169444) (@lem7169448)). Qed.
Lemma lem7169451 (x : nat) : (term103 x) = term23.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7169452 : term102 = term23.
Proof. exact (@lem7169451 term36). Qed.
Lemma lem7169453 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7169454 : term124 = term118.
Proof. exact (MK_COMB (@lem7169453) (@lem7169452)). Qed.
Lemma lem7169455 : term123 = term86.
Proof. exact (MK_COMB (@lem7169454) (@lem7169449)). Qed.
Lemma lem7169457 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169458 : term86 = term87.
Proof. exact (@lem7169457 (NUMERAL 0) term36). Qed.
Lemma lem7169459 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169460 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169461 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169460 h1) (fun h1 : term87 = True => @lem7169459)). Qed.
Lemma lem7169462 : term87 = True.
Proof. exact (EQ_MP (@lem7169461) (@lem7169459)). Qed.
Lemma lem7169463 : term86 = True.
Proof. exact (TRANS (@lem7169458) (@lem7169462)). Qed.
Lemma lem7169464 : term123 = True.
Proof. exact (TRANS (@lem7169455) (@lem7169463)). Qed.
Lemma lem7169465 : term120 = True.
Proof. exact (TRANS (@lem7169441) (@lem7169464)). Qed.
Lemma lem7169466 : term86 = True.
Proof. exact (TRANS (@lem7169418) (@lem7169465)). Qed.
Lemma lem7169467 : term117 = True.
Proof. exact (TRANS (@lem7169409) (@lem7169466)). Qed.
Lemma lem7169468 : True = term117.
Proof. exact (SYM (@lem7169467)). Qed.
Lemma lem7169469 : term117.
Proof. exact (EQ_MP (@lem7169468) (@lem0)). Qed.
Lemma lem7169470 (x : real) (y : real) (h1 : term116 x y) : term125 x.
Proof. exact (conj (@lem7169469) (@lem7169406 x y h1)). Qed.
Lemma lem7169472 (x : real) (y : real) : term126 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7169473 (x : real) : term127 x.
Proof. exact (@lem7169472 term42 (term24 x)). Qed.
Lemma lem7169474 (x : real) (y : real) (h1 : term116 x y) : term128 x.
Proof. exact (@lem7169473 x (@lem7169470 x y h1)). Qed.
Lemma lem7169475 (x : real) : (term129 x) = (term24 x).
Proof. exact (@lem1982733 (term24 x)). Qed.
Lemma lem7169476 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7169477 (x : real) : (term130 x) = (term56 x).
Proof. exact (MK_COMB (@lem7169476) (@lem7169475 x)). Qed.
Lemma lem7169478 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7169479 (x : real) : (term128 x) = (term57 x).
Proof. exact (MK_COMB (@lem7169477 x) (@lem7169478)). Qed.
Lemma lem7169480 (x : real) (y : real) (h1 : term116 x y) : term57 x.
Proof. exact (EQ_MP (@lem7169479 x) (@lem7169474 x y h1)). Qed.
Lemma lem7169482 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7169483 : term117 = term86.
Proof. exact (@lem7169482 term23 term42). Qed.
Lemma lem7169485 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169486 : term42 = term79.
Proof. exact (@lem7169485 term36). Qed.
Lemma lem7169488 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169489 : term23 = term31.
Proof. exact (@lem7169488 (NUMERAL 0)). Qed.
Lemma lem7169490 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7169491 : term118 = term119.
Proof. exact (MK_COMB (@lem7169490) (@lem7169489)). Qed.
Lemma lem7169492 : term86 = term120.
Proof. exact (MK_COMB (@lem7169491) (@lem7169486)). Qed.
Lemma lem7169493 : term121.
Proof. exact (@lem1980255 term23 term42 term42 term42). Qed.
Lemma lem7169495 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169496 : term86 = term87.
Proof. exact (@lem7169495 (NUMERAL 0) term36). Qed.
Lemma lem7169497 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169498 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169499 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169498 h1) (fun h1 : term87 = True => @lem7169497)). Qed.
Lemma lem7169500 : term87 = True.
Proof. exact (EQ_MP (@lem7169499) (@lem7169497)). Qed.
Lemma lem7169501 : term86 = True.
Proof. exact (TRANS (@lem7169496) (@lem7169500)). Qed.
Lemma lem7169502 : True = term86.
Proof. exact (SYM (@lem7169501)). Qed.
Lemma lem7169503 : term86.
Proof. exact (EQ_MP (@lem7169502) (@lem0)). Qed.
Lemma lem7169504 : term122.
Proof. exact (@lem7169493 (@lem7169503)). Qed.
Lemma lem7169506 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169507 : term86 = term87.
Proof. exact (@lem7169506 (NUMERAL 0) term36). Qed.
Lemma lem7169508 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169509 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169510 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169509 h1) (fun h1 : term87 = True => @lem7169508)). Qed.
Lemma lem7169511 : term87 = True.
Proof. exact (EQ_MP (@lem7169510) (@lem7169508)). Qed.
Lemma lem7169512 : term86 = True.
Proof. exact (TRANS (@lem7169507) (@lem7169511)). Qed.
Lemma lem7169513 : True = term86.
Proof. exact (SYM (@lem7169512)). Qed.
Lemma lem7169514 : term86.
Proof. exact (EQ_MP (@lem7169513) (@lem0)). Qed.
Lemma lem7169515 : term120 = term123.
Proof. exact (@lem7169504 (@lem7169514)). Qed.
Lemma lem7169517 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7169518 : term45 = term46.
Proof. exact (@lem7169517 term36 term36). Qed.
Lemma lem7169519 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169520 : term48 = term36.
Proof. exact (EQ_MP (@lem7169519) (@lem940073)). Qed.
Lemma lem7169521 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169522 : term46 = term42.
Proof. exact (MK_COMB (@lem7169521) (@lem7169520)). Qed.
Lemma lem7169523 : term45 = term42.
Proof. exact (TRANS (@lem7169518) (@lem7169522)). Qed.
Lemma lem7169525 (x : nat) : (term103 x) = term23.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7169526 : term102 = term23.
Proof. exact (@lem7169525 term36). Qed.
Lemma lem7169527 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7169528 : term124 = term118.
Proof. exact (MK_COMB (@lem7169527) (@lem7169526)). Qed.
Lemma lem7169529 : term123 = term86.
Proof. exact (MK_COMB (@lem7169528) (@lem7169523)). Qed.
Lemma lem7169531 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169532 : term86 = term87.
Proof. exact (@lem7169531 (NUMERAL 0) term36). Qed.
Lemma lem7169533 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169534 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169535 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169534 h1) (fun h1 : term87 = True => @lem7169533)). Qed.
Lemma lem7169536 : term87 = True.
Proof. exact (EQ_MP (@lem7169535) (@lem7169533)). Qed.
Lemma lem7169537 : term86 = True.
Proof. exact (TRANS (@lem7169532) (@lem7169536)). Qed.
Lemma lem7169538 : term123 = True.
Proof. exact (TRANS (@lem7169529) (@lem7169537)). Qed.
Lemma lem7169539 : term120 = True.
Proof. exact (TRANS (@lem7169515) (@lem7169538)). Qed.
Lemma lem7169540 : term86 = True.
Proof. exact (TRANS (@lem7169492) (@lem7169539)). Qed.
Lemma lem7169541 : term117 = True.
Proof. exact (TRANS (@lem7169483) (@lem7169540)). Qed.
Lemma lem7169542 : True = term117.
Proof. exact (SYM (@lem7169541)). Qed.
Lemma lem7169543 : term117.
Proof. exact (EQ_MP (@lem7169542) (@lem0)). Qed.
Lemma lem7169544 (x : real) (y : real) (h1 : term116 x y) : term131 y.
Proof. exact (conj (@lem7169543) (@lem7169405 x y h1)). Qed.
Lemma lem7169546 (x : real) (y : real) : term126 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7169547 (y : real) : term132 y.
Proof. exact (@lem7169546 term42 y). Qed.
Lemma lem7169548 (x : real) (y : real) (h1 : term116 x y) : term133 y.
Proof. exact (@lem7169547 y (@lem7169544 x y h1)). Qed.
Lemma lem7169549 (y : real) : (term134 y) = y.
Proof. exact (@lem1982733 y). Qed.
Lemma lem7169550 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7169551 (y : real) : (term135 y) = (real_ge y).
Proof. exact (MK_COMB (@lem7169550) (@lem7169549 y)). Qed.
Lemma lem7169552 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7169553 (y : real) : (term133 y) = (term64 y).
Proof. exact (MK_COMB (@lem7169551 y) (@lem7169552)). Qed.
Lemma lem7169554 (x : real) (y : real) (h1 : term116 x y) : term64 y.
Proof. exact (EQ_MP (@lem7169553 y) (@lem7169548 x y h1)). Qed.
Lemma lem7169556 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7169557 : term117 = term86.
Proof. exact (@lem7169556 term23 term42). Qed.
Lemma lem7169559 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169560 : term42 = term79.
Proof. exact (@lem7169559 term36). Qed.
Lemma lem7169562 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169563 : term23 = term31.
Proof. exact (@lem7169562 (NUMERAL 0)). Qed.
Lemma lem7169564 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7169565 : term118 = term119.
Proof. exact (MK_COMB (@lem7169564) (@lem7169563)). Qed.
Lemma lem7169566 : term86 = term120.
Proof. exact (MK_COMB (@lem7169565) (@lem7169560)). Qed.
Lemma lem7169567 : term121.
Proof. exact (@lem1980255 term23 term42 term42 term42). Qed.
Lemma lem7169569 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169570 : term86 = term87.
Proof. exact (@lem7169569 (NUMERAL 0) term36). Qed.
Lemma lem7169571 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169572 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169573 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169572 h1) (fun h1 : term87 = True => @lem7169571)). Qed.
Lemma lem7169574 : term87 = True.
Proof. exact (EQ_MP (@lem7169573) (@lem7169571)). Qed.
Lemma lem7169575 : term86 = True.
Proof. exact (TRANS (@lem7169570) (@lem7169574)). Qed.
Lemma lem7169576 : True = term86.
Proof. exact (SYM (@lem7169575)). Qed.
Lemma lem7169577 : term86.
Proof. exact (EQ_MP (@lem7169576) (@lem0)). Qed.
Lemma lem7169578 : term122.
Proof. exact (@lem7169567 (@lem7169577)). Qed.
Lemma lem7169580 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169581 : term86 = term87.
Proof. exact (@lem7169580 (NUMERAL 0) term36). Qed.
Lemma lem7169582 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169583 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169584 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169583 h1) (fun h1 : term87 = True => @lem7169582)). Qed.
Lemma lem7169585 : term87 = True.
Proof. exact (EQ_MP (@lem7169584) (@lem7169582)). Qed.
Lemma lem7169586 : term86 = True.
Proof. exact (TRANS (@lem7169581) (@lem7169585)). Qed.
Lemma lem7169587 : True = term86.
Proof. exact (SYM (@lem7169586)). Qed.
Lemma lem7169588 : term86.
Proof. exact (EQ_MP (@lem7169587) (@lem0)). Qed.
Lemma lem7169589 : term120 = term123.
Proof. exact (@lem7169578 (@lem7169588)). Qed.
Lemma lem7169591 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7169592 : term45 = term46.
Proof. exact (@lem7169591 term36 term36). Qed.
Lemma lem7169593 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169594 : term48 = term36.
Proof. exact (EQ_MP (@lem7169593) (@lem940073)). Qed.
Lemma lem7169595 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169596 : term46 = term42.
Proof. exact (MK_COMB (@lem7169595) (@lem7169594)). Qed.
Lemma lem7169597 : term45 = term42.
Proof. exact (TRANS (@lem7169592) (@lem7169596)). Qed.
Lemma lem7169599 (x : nat) : (term103 x) = term23.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7169600 : term102 = term23.
Proof. exact (@lem7169599 term36). Qed.
Lemma lem7169601 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7169602 : term124 = term118.
Proof. exact (MK_COMB (@lem7169601) (@lem7169600)). Qed.
Lemma lem7169603 : term123 = term86.
Proof. exact (MK_COMB (@lem7169602) (@lem7169597)). Qed.
Lemma lem7169605 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169606 : term86 = term87.
Proof. exact (@lem7169605 (NUMERAL 0) term36). Qed.
Lemma lem7169607 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169608 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169609 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169608 h1) (fun h1 : term87 = True => @lem7169607)). Qed.
Lemma lem7169610 : term87 = True.
Proof. exact (EQ_MP (@lem7169609) (@lem7169607)). Qed.
Lemma lem7169611 : term86 = True.
Proof. exact (TRANS (@lem7169606) (@lem7169610)). Qed.
Lemma lem7169612 : term123 = True.
Proof. exact (TRANS (@lem7169603) (@lem7169611)). Qed.
Lemma lem7169613 : term120 = True.
Proof. exact (TRANS (@lem7169589) (@lem7169612)). Qed.
Lemma lem7169614 : term86 = True.
Proof. exact (TRANS (@lem7169566) (@lem7169613)). Qed.
Lemma lem7169615 : term117 = True.
Proof. exact (TRANS (@lem7169557) (@lem7169614)). Qed.
Lemma lem7169616 : True = term117.
Proof. exact (SYM (@lem7169615)). Qed.
Lemma lem7169617 : term117.
Proof. exact (EQ_MP (@lem7169616) (@lem0)). Qed.
Lemma lem7169618 (x : real) (y : real) (h1 : term116 x y) : term136 x y.
Proof. exact (conj (@lem7169617) (@lem7169403 x y h1)). Qed.
Lemma lem7169620 (x : real) (y : real) : term137 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7169621 (x : real) (y : real) : term138 x y.
Proof. exact (@lem7169620 term42 (term109 x y)). Qed.
Lemma lem7169622 (x : real) (y : real) (h1 : term116 x y) : term139 x y.
Proof. exact (@lem7169621 x y (@lem7169618 x y h1)). Qed.
Lemma lem7169623 (x : real) (y : real) : (term140 x y) = (term109 x y).
Proof. exact (@lem1982733 (term109 x y)). Qed.
Lemma lem7169624 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7169625 (x : real) (y : real) : (term141 x y) = (term112 x y).
Proof. exact (MK_COMB (@lem7169624) (@lem7169623 x y)). Qed.
Lemma lem7169626 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7169627 (x : real) (y : real) : (term139 x y) = (term113 x y).
Proof. exact (MK_COMB (@lem7169625 x y) (@lem7169626)). Qed.
Lemma lem7169628 (x : real) (y : real) (h1 : term116 x y) : term113 x y.
Proof. exact (EQ_MP (@lem7169627 x y) (@lem7169622 x y h1)). Qed.
Lemma lem7169629 (x : real) (y : real) (h1 : term116 x y) : term142 x y.
Proof. exact (conj (@lem7169628 x y h1) (@lem7169554 x y h1)). Qed.
Lemma lem7169631 (x : real) (y : real) : term143 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem7169632 (x : real) (y : real) : term144 x y.
Proof. exact (@lem7169631 (term109 x y) y). Qed.
Lemma lem7169633 (x : real) (y : real) (h1 : term116 x y) : term145 x y.
Proof. exact (@lem7169632 x y (@lem7169629 x y h1)). Qed.
Lemma lem7169634 (x : real) (y : real) : (term146 x y) = (term147 x y).
Proof. exact (@lem1982755 x (term24 y) y). Qed.
Lemma lem7169635 (y : real) : (term148 y) = (term78 y).
Proof. exact (@lem1982713 term34 y). Qed.
Lemma lem7169637 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169638 : term42 = term79.
Proof. exact (@lem7169637 term36). Qed.
Lemma lem7169640 (x : nat) : (term32 x) = (term33 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7169641 : term34 = term35.
Proof. exact (@lem7169640 term36). Qed.
Lemma lem7169642 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7169643 : term80 = term81.
Proof. exact (MK_COMB (@lem7169642) (@lem7169641)). Qed.
Lemma lem7169644 : term82 = term83.
Proof. exact (MK_COMB (@lem7169643) (@lem7169638)). Qed.
Lemma lem7169645 : term84.
Proof. exact (@lem1981473 term34 term42 term42 term42 term23 term42). Qed.
Lemma lem7169647 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169648 : term86 = term87.
Proof. exact (@lem7169647 (NUMERAL 0) term36). Qed.
Lemma lem7169649 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169650 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169651 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169650 h1) (fun h1 : term87 = True => @lem7169649)). Qed.
Lemma lem7169652 : term87 = True.
Proof. exact (EQ_MP (@lem7169651) (@lem7169649)). Qed.
Lemma lem7169653 : term86 = True.
Proof. exact (TRANS (@lem7169648) (@lem7169652)). Qed.
Lemma lem7169654 : True = term86.
Proof. exact (SYM (@lem7169653)). Qed.
Lemma lem7169655 : term86.
Proof. exact (EQ_MP (@lem7169654) (@lem0)). Qed.
Lemma lem7169656 : term89.
Proof. exact (@lem7169645 (@lem7169655)). Qed.
Lemma lem7169658 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169659 : term86 = term87.
Proof. exact (@lem7169658 (NUMERAL 0) term36). Qed.
Lemma lem7169660 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169661 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169662 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169661 h1) (fun h1 : term87 = True => @lem7169660)). Qed.
Lemma lem7169663 : term87 = True.
Proof. exact (EQ_MP (@lem7169662) (@lem7169660)). Qed.
Lemma lem7169664 : term86 = True.
Proof. exact (TRANS (@lem7169659) (@lem7169663)). Qed.
Lemma lem7169665 : True = term86.
Proof. exact (SYM (@lem7169664)). Qed.
Lemma lem7169666 : term86.
Proof. exact (EQ_MP (@lem7169665) (@lem0)). Qed.
Lemma lem7169667 : term90.
Proof. exact (@lem7169656 (@lem7169666)). Qed.
Lemma lem7169669 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169670 : term86 = term87.
Proof. exact (@lem7169669 (NUMERAL 0) term36). Qed.
Lemma lem7169671 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169672 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169673 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169672 h1) (fun h1 : term87 = True => @lem7169671)). Qed.
Lemma lem7169674 : term87 = True.
Proof. exact (EQ_MP (@lem7169673) (@lem7169671)). Qed.
Lemma lem7169675 : term86 = True.
Proof. exact (TRANS (@lem7169670) (@lem7169674)). Qed.
Lemma lem7169676 : True = term86.
Proof. exact (SYM (@lem7169675)). Qed.
Lemma lem7169677 : term86.
Proof. exact (EQ_MP (@lem7169676) (@lem0)). Qed.
Lemma lem7169678 : term91.
Proof. exact (@lem7169667 (@lem7169677)). Qed.
Lemma lem7169680 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7169681 : term45 = term46.
Proof. exact (@lem7169680 term36 term36). Qed.
Lemma lem7169682 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169683 : term48 = term36.
Proof. exact (EQ_MP (@lem7169682) (@lem940073)). Qed.
Lemma lem7169684 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169685 : term46 = term42.
Proof. exact (MK_COMB (@lem7169684) (@lem7169683)). Qed.
Lemma lem7169686 : term45 = term42.
Proof. exact (TRANS (@lem7169681) (@lem7169685)). Qed.
Lemma lem7169688 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7169689 : term94 = term95.
Proof. exact (@lem7169688 term36 term36). Qed.
Lemma lem7169690 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169691 : term48 = term36.
Proof. exact (EQ_MP (@lem7169690) (@lem940073)). Qed.
Lemma lem7169692 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169693 : term46 = term42.
Proof. exact (MK_COMB (@lem7169692) (@lem7169691)). Qed.
Lemma lem7169694 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7169695 : term95 = term34.
Proof. exact (MK_COMB (@lem7169694) (@lem7169693)). Qed.
Lemma lem7169696 : term94 = term34.
Proof. exact (TRANS (@lem7169689) (@lem7169695)). Qed.
Lemma lem7169697 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7169698 : term96 = term80.
Proof. exact (MK_COMB (@lem7169697) (@lem7169696)). Qed.
Lemma lem7169699 : term97 = term82.
Proof. exact (MK_COMB (@lem7169698) (@lem7169686)). Qed.
Lemma lem7169701 (m : nat) : (term98 m) = term23.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7169702 : term82 = term23.
Proof. exact (@lem7169701 term36). Qed.
Lemma lem7169703 : term97 = term23.
Proof. exact (TRANS (@lem7169699) (@lem7169702)). Qed.
Lemma lem7169704 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7169705 : term99 = term100.
Proof. exact (MK_COMB (@lem7169704) (@lem7169703)). Qed.
Lemma lem7169706 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem7169707 : term101 = term102.
Proof. exact (MK_COMB (@lem7169705) (@lem7169706)). Qed.
Lemma lem7169709 (x : nat) : (term103 x) = term23.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7169710 : term102 = term23.
Proof. exact (@lem7169709 term36). Qed.
Lemma lem7169711 : term101 = term23.
Proof. exact (TRANS (@lem7169707) (@lem7169710)). Qed.
Lemma lem7169713 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7169714 : term45 = term46.
Proof. exact (@lem7169713 term36 term36). Qed.
Lemma lem7169715 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169716 : term48 = term36.
Proof. exact (EQ_MP (@lem7169715) (@lem940073)). Qed.
Lemma lem7169717 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169718 : term46 = term42.
Proof. exact (MK_COMB (@lem7169717) (@lem7169716)). Qed.
Lemma lem7169719 : term45 = term42.
Proof. exact (TRANS (@lem7169714) (@lem7169718)). Qed.
Lemma lem7169720 : term100 = term100.
Proof. exact (eq_refl term100). Qed.
Lemma lem7169721 : term104 = term102.
Proof. exact (MK_COMB (@lem7169720) (@lem7169719)). Qed.
Lemma lem7169723 (x : nat) : (term103 x) = term23.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7169724 : term102 = term23.
Proof. exact (@lem7169723 term36). Qed.
Lemma lem7169725 : term104 = term23.
Proof. exact (TRANS (@lem7169721) (@lem7169724)). Qed.
Lemma lem7169726 : term23 = term104.
Proof. exact (SYM (@lem7169725)). Qed.
Lemma lem7169727 : term101 = term104.
Proof. exact (TRANS (@lem7169711) (@lem7169726)). Qed.
Lemma lem7169728 : term83 = term31.
Proof. exact (@lem7169678 (@lem7169727)). Qed.
Lemma lem7169729 : term82 = term31.
Proof. exact (TRANS (@lem7169644) (@lem7169728)). Qed.
Lemma lem7169731 (x : real) : (term52 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7169732 : term31 = term23.
Proof. exact (@lem7169731 term23). Qed.
Lemma lem7169733 : term82 = term23.
Proof. exact (TRANS (@lem7169729) (@lem7169732)). Qed.
Lemma lem7169734 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7169735 : term105 = term100.
Proof. exact (MK_COMB (@lem7169734) (@lem7169733)). Qed.
Lemma lem7169736 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7169737 (y : real) : (term78 y) = (term106 y).
Proof. exact (MK_COMB (@lem7169735) (@lem7169736 y)). Qed.
Lemma lem7169738 (y : real) : (term148 y) = (term106 y).
Proof. exact (TRANS (@lem7169635 y) (@lem7169737 y)). Qed.
Lemma lem7169739 (y : real) : (term106 y) = term23.
Proof. exact (@lem1982719 y). Qed.
Lemma lem7169740 (y : real) : (term148 y) = term23.
Proof. exact (TRANS (@lem7169738 y) (@lem7169739 y)). Qed.
Lemma lem7169741 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem7169742 (y : real) (x : real) : (term147 x y) = (term62 x).
Proof. exact (MK_COMB (@lem7169741 x) (@lem7169740 y)). Qed.
Lemma lem7169743 (y : real) (x : real) : (term146 x y) = (term62 x).
Proof. exact (TRANS (@lem7169634 x y) (@lem7169742 y x)). Qed.
Lemma lem7169744 (x : real) : (term62 x) = x.
Proof. exact (@lem1982723 x). Qed.
Lemma lem7169745 (y : real) (x : real) : (term146 x y) = x.
Proof. exact (TRANS (@lem7169743 y x) (@lem7169744 x)). Qed.
Lemma lem7169746 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7169747 (y : real) (x : real) : (term149 x y) = (real_gt x).
Proof. exact (MK_COMB (@lem7169746) (@lem7169745 y x)). Qed.
Lemma lem7169748 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7169749 (y : real) (x : real) : (term145 x y) = (term150 x).
Proof. exact (MK_COMB (@lem7169747 y x) (@lem7169748)). Qed.
Lemma lem7169750 (x : real) (y : real) (h1 : term116 x y) : term150 x.
Proof. exact (EQ_MP (@lem7169749 y x) (@lem7169633 x y h1)). Qed.
Lemma lem7169752 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7169753 : term117 = term86.
Proof. exact (@lem7169752 term23 term42). Qed.
Lemma lem7169755 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169756 : term42 = term79.
Proof. exact (@lem7169755 term36). Qed.
Lemma lem7169758 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169759 : term23 = term31.
Proof. exact (@lem7169758 (NUMERAL 0)). Qed.
Lemma lem7169760 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7169761 : term118 = term119.
Proof. exact (MK_COMB (@lem7169760) (@lem7169759)). Qed.
Lemma lem7169762 : term86 = term120.
Proof. exact (MK_COMB (@lem7169761) (@lem7169756)). Qed.
Lemma lem7169763 : term121.
Proof. exact (@lem1980255 term23 term42 term42 term42). Qed.
Lemma lem7169765 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169766 : term86 = term87.
Proof. exact (@lem7169765 (NUMERAL 0) term36). Qed.
Lemma lem7169767 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169768 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169769 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169768 h1) (fun h1 : term87 = True => @lem7169767)). Qed.
Lemma lem7169770 : term87 = True.
Proof. exact (EQ_MP (@lem7169769) (@lem7169767)). Qed.
Lemma lem7169771 : term86 = True.
Proof. exact (TRANS (@lem7169766) (@lem7169770)). Qed.
Lemma lem7169772 : True = term86.
Proof. exact (SYM (@lem7169771)). Qed.
Lemma lem7169773 : term86.
Proof. exact (EQ_MP (@lem7169772) (@lem0)). Qed.
Lemma lem7169774 : term122.
Proof. exact (@lem7169763 (@lem7169773)). Qed.
Lemma lem7169776 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169777 : term86 = term87.
Proof. exact (@lem7169776 (NUMERAL 0) term36). Qed.
Lemma lem7169778 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169779 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169780 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169779 h1) (fun h1 : term87 = True => @lem7169778)). Qed.
Lemma lem7169781 : term87 = True.
Proof. exact (EQ_MP (@lem7169780) (@lem7169778)). Qed.
Lemma lem7169782 : term86 = True.
Proof. exact (TRANS (@lem7169777) (@lem7169781)). Qed.
Lemma lem7169783 : True = term86.
Proof. exact (SYM (@lem7169782)). Qed.
Lemma lem7169784 : term86.
Proof. exact (EQ_MP (@lem7169783) (@lem0)). Qed.
Lemma lem7169785 : term120 = term123.
Proof. exact (@lem7169774 (@lem7169784)). Qed.
Lemma lem7169787 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7169788 : term45 = term46.
Proof. exact (@lem7169787 term36 term36). Qed.
Lemma lem7169789 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169790 : term48 = term36.
Proof. exact (EQ_MP (@lem7169789) (@lem940073)). Qed.
Lemma lem7169791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169792 : term46 = term42.
Proof. exact (MK_COMB (@lem7169791) (@lem7169790)). Qed.
Lemma lem7169793 : term45 = term42.
Proof. exact (TRANS (@lem7169788) (@lem7169792)). Qed.
Lemma lem7169795 (x : nat) : (term103 x) = term23.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7169796 : term102 = term23.
Proof. exact (@lem7169795 term36). Qed.
Lemma lem7169797 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7169798 : term124 = term118.
Proof. exact (MK_COMB (@lem7169797) (@lem7169796)). Qed.
Lemma lem7169799 : term123 = term86.
Proof. exact (MK_COMB (@lem7169798) (@lem7169793)). Qed.
Lemma lem7169801 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169802 : term86 = term87.
Proof. exact (@lem7169801 (NUMERAL 0) term36). Qed.
Lemma lem7169803 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169804 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169805 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169804 h1) (fun h1 : term87 = True => @lem7169803)). Qed.
Lemma lem7169806 : term87 = True.
Proof. exact (EQ_MP (@lem7169805) (@lem7169803)). Qed.
Lemma lem7169807 : term86 = True.
Proof. exact (TRANS (@lem7169802) (@lem7169806)). Qed.
Lemma lem7169808 : term123 = True.
Proof. exact (TRANS (@lem7169799) (@lem7169807)). Qed.
Lemma lem7169809 : term120 = True.
Proof. exact (TRANS (@lem7169785) (@lem7169808)). Qed.
Lemma lem7169810 : term86 = True.
Proof. exact (TRANS (@lem7169762) (@lem7169809)). Qed.
Lemma lem7169811 : term117 = True.
Proof. exact (TRANS (@lem7169753) (@lem7169810)). Qed.
Lemma lem7169812 : True = term117.
Proof. exact (SYM (@lem7169811)). Qed.
Lemma lem7169813 : term117.
Proof. exact (EQ_MP (@lem7169812) (@lem0)). Qed.
Lemma lem7169814 (x : real) (y : real) (h1 : term116 x y) : term151 x.
Proof. exact (conj (@lem7169813) (@lem7169750 x y h1)). Qed.
Lemma lem7169816 (x : real) (y : real) : term137 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7169817 (x : real) : term152 x.
Proof. exact (@lem7169816 term42 x). Qed.
Lemma lem7169818 (x : real) (y : real) (h1 : term116 x y) : term153 x.
Proof. exact (@lem7169817 x (@lem7169814 x y h1)). Qed.
Lemma lem7169819 (x : real) : (term134 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem7169820 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7169821 (x : real) : (term154 x) = (real_gt x).
Proof. exact (MK_COMB (@lem7169820) (@lem7169819 x)). Qed.
Lemma lem7169822 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7169823 (x : real) : (term153 x) = (term150 x).
Proof. exact (MK_COMB (@lem7169821 x) (@lem7169822)). Qed.
Lemma lem7169824 (x : real) (y : real) (h1 : term116 x y) : term150 x.
Proof. exact (EQ_MP (@lem7169823 x) (@lem7169818 x y h1)). Qed.
Lemma lem7169825 (x : real) (y : real) (h1 : term116 x y) : term155 x.
Proof. exact (conj (@lem7169824 x y h1) (@lem7169480 x y h1)). Qed.
Lemma lem7169827 (x : real) (y : real) : term143 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem7169828 (x : real) : term156 x.
Proof. exact (@lem7169827 x (term24 x)). Qed.
Lemma lem7169829 (x : real) (y : real) (h1 : term116 x y) : term157 x.
Proof. exact (@lem7169828 x (@lem7169825 x y h1)). Qed.
Lemma lem7169830 (x : real) : (term77 x) = (term78 x).
Proof. exact (@lem1982715 term34 x). Qed.
Lemma lem7169832 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169833 : term42 = term79.
Proof. exact (@lem7169832 term36). Qed.
Lemma lem7169835 (x : nat) : (term32 x) = (term33 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7169836 : term34 = term35.
Proof. exact (@lem7169835 term36). Qed.
Lemma lem7169837 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7169838 : term80 = term81.
Proof. exact (MK_COMB (@lem7169837) (@lem7169836)). Qed.
Lemma lem7169839 : term82 = term83.
Proof. exact (MK_COMB (@lem7169838) (@lem7169833)). Qed.
Lemma lem7169840 : term84.
Proof. exact (@lem1981473 term34 term42 term42 term42 term23 term42). Qed.
Lemma lem7169842 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169843 : term86 = term87.
Proof. exact (@lem7169842 (NUMERAL 0) term36). Qed.
Lemma lem7169844 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169845 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169846 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169845 h1) (fun h1 : term87 = True => @lem7169844)). Qed.
Lemma lem7169847 : term87 = True.
Proof. exact (EQ_MP (@lem7169846) (@lem7169844)). Qed.
Lemma lem7169848 : term86 = True.
Proof. exact (TRANS (@lem7169843) (@lem7169847)). Qed.
Lemma lem7169849 : True = term86.
Proof. exact (SYM (@lem7169848)). Qed.
Lemma lem7169850 : term86.
Proof. exact (EQ_MP (@lem7169849) (@lem0)). Qed.
Lemma lem7169851 : term89.
Proof. exact (@lem7169840 (@lem7169850)). Qed.
Lemma lem7169853 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169854 : term86 = term87.
Proof. exact (@lem7169853 (NUMERAL 0) term36). Qed.
Lemma lem7169855 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169856 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169857 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169856 h1) (fun h1 : term87 = True => @lem7169855)). Qed.
Lemma lem7169858 : term87 = True.
Proof. exact (EQ_MP (@lem7169857) (@lem7169855)). Qed.
Lemma lem7169859 : term86 = True.
Proof. exact (TRANS (@lem7169854) (@lem7169858)). Qed.
Lemma lem7169860 : True = term86.
Proof. exact (SYM (@lem7169859)). Qed.
Lemma lem7169861 : term86.
Proof. exact (EQ_MP (@lem7169860) (@lem0)). Qed.
Lemma lem7169862 : term90.
Proof. exact (@lem7169851 (@lem7169861)). Qed.
Lemma lem7169864 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169865 : term86 = term87.
Proof. exact (@lem7169864 (NUMERAL 0) term36). Qed.
Lemma lem7169866 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169867 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169868 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169867 h1) (fun h1 : term87 = True => @lem7169866)). Qed.
Lemma lem7169869 : term87 = True.
Proof. exact (EQ_MP (@lem7169868) (@lem7169866)). Qed.
Lemma lem7169870 : term86 = True.
Proof. exact (TRANS (@lem7169865) (@lem7169869)). Qed.
Lemma lem7169871 : True = term86.
Proof. exact (SYM (@lem7169870)). Qed.
Lemma lem7169872 : term86.
Proof. exact (EQ_MP (@lem7169871) (@lem0)). Qed.
Lemma lem7169873 : term91.
Proof. exact (@lem7169862 (@lem7169872)). Qed.
Lemma lem7169875 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7169876 : term45 = term46.
Proof. exact (@lem7169875 term36 term36). Qed.
Lemma lem7169877 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169878 : term48 = term36.
Proof. exact (EQ_MP (@lem7169877) (@lem940073)). Qed.
Lemma lem7169879 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169880 : term46 = term42.
Proof. exact (MK_COMB (@lem7169879) (@lem7169878)). Qed.
Lemma lem7169881 : term45 = term42.
Proof. exact (TRANS (@lem7169876) (@lem7169880)). Qed.
Lemma lem7169883 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7169884 : term94 = term95.
Proof. exact (@lem7169883 term36 term36). Qed.
Lemma lem7169885 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169886 : term48 = term36.
Proof. exact (EQ_MP (@lem7169885) (@lem940073)). Qed.
Lemma lem7169887 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169888 : term46 = term42.
Proof. exact (MK_COMB (@lem7169887) (@lem7169886)). Qed.
Lemma lem7169889 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7169890 : term95 = term34.
Proof. exact (MK_COMB (@lem7169889) (@lem7169888)). Qed.
Lemma lem7169891 : term94 = term34.
Proof. exact (TRANS (@lem7169884) (@lem7169890)). Qed.
Lemma lem7169892 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7169893 : term96 = term80.
Proof. exact (MK_COMB (@lem7169892) (@lem7169891)). Qed.
Lemma lem7169894 : term97 = term82.
Proof. exact (MK_COMB (@lem7169893) (@lem7169881)). Qed.
Lemma lem7169896 (m : nat) : (term98 m) = term23.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7169897 : term82 = term23.
Proof. exact (@lem7169896 term36). Qed.
Lemma lem7169898 : term97 = term23.
Proof. exact (TRANS (@lem7169894) (@lem7169897)). Qed.
Lemma lem7169899 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7169900 : term99 = term100.
Proof. exact (MK_COMB (@lem7169899) (@lem7169898)). Qed.
Lemma lem7169901 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem7169902 : term101 = term102.
Proof. exact (MK_COMB (@lem7169900) (@lem7169901)). Qed.
Lemma lem7169904 (x : nat) : (term103 x) = term23.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7169905 : term102 = term23.
Proof. exact (@lem7169904 term36). Qed.
Lemma lem7169906 : term101 = term23.
Proof. exact (TRANS (@lem7169902) (@lem7169905)). Qed.
Lemma lem7169908 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7169909 : term45 = term46.
Proof. exact (@lem7169908 term36 term36). Qed.
Lemma lem7169910 : (term47 = (BIT1 0)) = (term48 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7169911 : term48 = term36.
Proof. exact (EQ_MP (@lem7169910) (@lem940073)). Qed.
Lemma lem7169912 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7169913 : term46 = term42.
Proof. exact (MK_COMB (@lem7169912) (@lem7169911)). Qed.
Lemma lem7169914 : term45 = term42.
Proof. exact (TRANS (@lem7169909) (@lem7169913)). Qed.
Lemma lem7169915 : term100 = term100.
Proof. exact (eq_refl term100). Qed.
Lemma lem7169916 : term104 = term102.
Proof. exact (MK_COMB (@lem7169915) (@lem7169914)). Qed.
Lemma lem7169918 (x : nat) : (term103 x) = term23.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7169919 : term102 = term23.
Proof. exact (@lem7169918 term36). Qed.
Lemma lem7169920 : term104 = term23.
Proof. exact (TRANS (@lem7169916) (@lem7169919)). Qed.
Lemma lem7169921 : term23 = term104.
Proof. exact (SYM (@lem7169920)). Qed.
Lemma lem7169922 : term101 = term104.
Proof. exact (TRANS (@lem7169906) (@lem7169921)). Qed.
Lemma lem7169923 : term83 = term31.
Proof. exact (@lem7169873 (@lem7169922)). Qed.
Lemma lem7169924 : term82 = term31.
Proof. exact (TRANS (@lem7169839) (@lem7169923)). Qed.
Lemma lem7169926 (x : real) : (term52 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7169927 : term31 = term23.
Proof. exact (@lem7169926 term23). Qed.
Lemma lem7169928 : term82 = term23.
Proof. exact (TRANS (@lem7169924) (@lem7169927)). Qed.
Lemma lem7169929 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7169930 : term105 = term100.
Proof. exact (MK_COMB (@lem7169929) (@lem7169928)). Qed.
Lemma lem7169931 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7169932 (x : real) : (term78 x) = (term106 x).
Proof. exact (MK_COMB (@lem7169930) (@lem7169931 x)). Qed.
Lemma lem7169933 (x : real) : (term77 x) = (term106 x).
Proof. exact (TRANS (@lem7169830 x) (@lem7169932 x)). Qed.
Lemma lem7169934 (x : real) : (term106 x) = term23.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7169935 (x : real) : (term77 x) = term23.
Proof. exact (TRANS (@lem7169933 x) (@lem7169934 x)). Qed.
Lemma lem7169936 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7169937 (x : real) : (term158 x) = term159.
Proof. exact (MK_COMB (@lem7169936) (@lem7169935 x)). Qed.
Lemma lem7169938 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7169939 (x : real) : (term157 x) = term160.
Proof. exact (MK_COMB (@lem7169937 x) (@lem7169938)). Qed.
Lemma lem7169940 (x : real) (y : real) (h1 : term116 x y) : term160.
Proof. exact (EQ_MP (@lem7169939 x) (@lem7169829 x y h1)). Qed.
Lemma lem7169942 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7169943 : term160 = term161.
Proof. exact (@lem7169942 term23 term23). Qed.
Lemma lem7169945 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169946 : term23 = term31.
Proof. exact (@lem7169945 (NUMERAL 0)). Qed.
Lemma lem7169948 (x : nat) : (real_of_num x) = (term30 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7169949 : term23 = term31.
Proof. exact (@lem7169948 (NUMERAL 0)). Qed.
Lemma lem7169950 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7169951 : term118 = term119.
Proof. exact (MK_COMB (@lem7169950) (@lem7169949)). Qed.
Lemma lem7169952 : term161 = term162.
Proof. exact (MK_COMB (@lem7169951) (@lem7169946)). Qed.
Lemma lem7169953 : term163.
Proof. exact (@lem1980255 term23 term42 term23 term42). Qed.
Lemma lem7169955 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169956 : term86 = term87.
Proof. exact (@lem7169955 (NUMERAL 0) term36). Qed.
Lemma lem7169957 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169958 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169959 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169958 h1) (fun h1 : term87 = True => @lem7169957)). Qed.
Lemma lem7169960 : term87 = True.
Proof. exact (EQ_MP (@lem7169959) (@lem7169957)). Qed.
Lemma lem7169961 : term86 = True.
Proof. exact (TRANS (@lem7169956) (@lem7169960)). Qed.
Lemma lem7169962 : True = term86.
Proof. exact (SYM (@lem7169961)). Qed.
Lemma lem7169963 : term86.
Proof. exact (EQ_MP (@lem7169962) (@lem0)). Qed.
Lemma lem7169964 : term164.
Proof. exact (@lem7169953 (@lem7169963)). Qed.
Lemma lem7169966 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169967 : term86 = term87.
Proof. exact (@lem7169966 (NUMERAL 0) term36). Qed.
Lemma lem7169968 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7169969 (h1 : term88 = (BIT1 0)) : term87 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7169970 : (term88 = (BIT1 0)) = (term87 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem7169969 h1) (fun h1 : term87 = True => @lem7169968)). Qed.
Lemma lem7169971 : term87 = True.
Proof. exact (EQ_MP (@lem7169970) (@lem7169968)). Qed.
Lemma lem7169972 : term86 = True.
Proof. exact (TRANS (@lem7169967) (@lem7169971)). Qed.
Lemma lem7169973 : True = term86.
Proof. exact (SYM (@lem7169972)). Qed.
Lemma lem7169974 : term86.
Proof. exact (EQ_MP (@lem7169973) (@lem0)). Qed.
Lemma lem7169975 : term162 = term165.
Proof. exact (@lem7169964 (@lem7169974)). Qed.
Lemma lem7169977 (x : nat) : (term103 x) = term23.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7169978 : term102 = term23.
Proof. exact (@lem7169977 term36). Qed.
Lemma lem7169980 (x : nat) : (term103 x) = term23.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7169981 : term102 = term23.
Proof. exact (@lem7169980 term36). Qed.
Lemma lem7169982 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7169983 : term124 = term118.
Proof. exact (MK_COMB (@lem7169982) (@lem7169981)). Qed.
Lemma lem7169984 : term165 = term161.
Proof. exact (MK_COMB (@lem7169983) (@lem7169978)). Qed.
Lemma lem7169986 (m : nat) (n : nat) : (term85 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7169987 : term161 = term166.
Proof. exact (@lem7169986 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7169988 : term166 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7169989 : term161 = False.
Proof. exact (TRANS (@lem7169987) (@lem7169988)). Qed.
Lemma lem7169990 : term165 = False.
Proof. exact (TRANS (@lem7169984) (@lem7169989)). Qed.
Lemma lem7169991 : term162 = False.
Proof. exact (TRANS (@lem7169975) (@lem7169990)). Qed.
Lemma lem7169992 : term161 = False.
Proof. exact (TRANS (@lem7169952) (@lem7169991)). Qed.
Lemma lem7169993 : term160 = False.
Proof. exact (TRANS (@lem7169943) (@lem7169992)). Qed.
Lemma lem7169994 (x : real) (y : real) (h1 : term116 x y) : False.
Proof. exact (EQ_MP (@lem7169993) (@lem7169940 x y h1)). Qed.
Lemma lem7169996 (x : real) (y : real) (h1 : term116 x y) : term116 x y.
Proof. exact (h1). Qed.
Lemma lem7169997 (x : real) (y : real) (h1 : term116 x y) : (term116 x y) = False.
Proof. exact (prop_ext (fun h2 : term116 x y => @lem7169994 x y h1) (fun h2 : False => @lem7169996 x y h1)). Qed.
Lemma lem7169998 (x : real) (y : real) (h1 : term116 x y) : False.
Proof. exact (EQ_MP (@lem7169997 x y h1) (@lem7169996 x y h1)). Qed.
Lemma lem7169999 (x : real) (a : real) (y : real) (h1 : term17 x a y) : term17 x a y.
Proof. exact (h1). Qed.
Lemma lem7170000 (x : real) (a : real) (y : real) (h1 : term17 x a y) : term116 x y.
Proof. exact (EQ_MP (@lem7169398 a x y) (@lem7169999 x a y h1)). Qed.
Lemma lem7170001 (x : real) (a : real) (y : real) (h1 : term17 x a y) : (term116 x y) = False.
Proof. exact (prop_ext (fun h2 : term116 x y => @lem7169998 x y h2) (fun h2 : False => @lem7170000 x a y h1)). Qed.
Lemma lem7170002 (x : real) (a : real) (y : real) (h1 : term17 x a y) : False.
Proof. exact (EQ_MP (@lem7170001 x a y h1) (@lem7170000 x a y h1)). Qed.
Lemma lem7170003 (x : real) (a : real) (y : real) : term167 x a y.
Proof. exact (fun h0 : term17 x a y => @lem7170002 x a y h0). Qed.
Lemma lem7170004 (x : real) (a : real) (y : real) : term168 x a y.
Proof. exact (@lem1386578 (term169 x a y)). Qed.
Lemma lem7170007 (x : real) (a : real) (y : real) : term169 x a y.
Proof. exact (@lem7170004 x a y (@lem7170003 x a y)). Qed.
Lemma lem7170008 (x : real) (a : real) (y : real) (h1 : term169 x a y) : term169 x a y.
Proof. exact (h1). Qed.
Lemma lem7170009 (x : real) (y : real) (h1 : term19 x y) : term19 x y.
Proof. exact (h1). Qed.
Lemma lem7170010 (x : real) (a : real) (y : real) (h1 : term19 x y) (h2 : term169 x a y) : term20 x a y.
Proof. exact (@lem7170008 x a y h2 (@lem7170009 x y h1)). Qed.
Lemma lem7170011 (a : real) (x : real) (y : real) (h1 : term19 x y) : term170 x a y.
Proof. exact (fun h0 : term169 x a y => @lem7170010 x a y h1 h0). Qed.
Lemma lem7170012 (x : real) (a : real) (y : real) (h1 : term169 x a y) : term169 x a y.
Proof. exact (h1). Qed.
Lemma lem7170013 (x : real) (a : real) (y : real) (h1 : term19 x y) (h2 : term169 x a y) : term20 x a y.
Proof. exact (@lem7170011 a x y h1 (@lem7170012 x a y h2)). Qed.
Lemma lem7170014 (x : real) (a : real) (y : real) (h1 : term169 x a y) : term169 x a y.
Proof. exact (fun h0 : term19 x y => @lem7170013 x a y h0 h1). Qed.
Lemma lem7170015 (x : real) (a : real) (y : real) : term171 x a y.
Proof. exact (fun h0 : term169 x a y => @lem7170014 x a y h0). Qed.
Lemma lem7170040 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term172 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7170041 {_134537 : Type'} (s : _134537 -> Prop) (t : _134537 -> Prop) : (s = t) = (term172 _134537 s t).
Proof. exact (@lem7170040 _134537 s t). Qed.
Lemma lem7170042 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : ((term173 _134537 v u) = v) = (term174 _134537 u v).
Proof. exact (@lem7170041 _134537 (term173 _134537 v u) v). Qed.
Lemma lem7170051 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term174 _134537 u v) = ((term173 _134537 v u) = v).
Proof. exact (SYM (@lem7170042 _134537 u v)). Qed.
Lemma lem7170059 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term175 A x s t) = (term176 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem7170060 {_134537 : Type'} (s : _134537 -> Prop) (x : _134537) (t : _134537 -> Prop) : (term175 _134537 x s t) = (term176 _134537 s x t).
Proof. exact (@lem7170059 _134537 s x t). Qed.
Lemma lem7170061 {_134537 : Type'} (x : _134537) (v : _134537 -> Prop) (u : _134537 -> Prop) : (term177 _134537 x v u) = (term178 _134537 x v u).
Proof. exact (@lem7170060 _134537 (@INTER _134537 u v) x (@DIFF _134537 v u)). Qed.
Lemma lem7170065 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term179 A x s t) = (term180 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem7170066 {_134537 : Type'} (s : _134537 -> Prop) (x : _134537) (t : _134537 -> Prop) : (term179 _134537 x s t) = (term180 _134537 s x t).
Proof. exact (@lem7170065 _134537 s x t). Qed.
Lemma lem7170067 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (v : _134537 -> Prop) : (term179 _134537 x u v) = (term180 _134537 u x v).
Proof. exact (@lem7170066 _134537 u x v). Qed.
Lemma lem7170071 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7170072 {_134537 : Type'} (P : _134537 -> Prop) (x : _134537) : (@IN _134537 x P) = (P x).
Proof. exact (@lem7170071 _134537 P x). Qed.
Lemma lem7170073 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) : (@IN _134537 x u) = (u x).
Proof. exact (@lem7170072 _134537 u x). Qed.
Lemma lem7170074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7170075 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) : (term181 _134537 x u) = (term182 _134537 u x).
Proof. exact (MK_COMB (@lem7170074) (@lem7170073 _134537 u x)). Qed.
Lemma lem7170077 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7170078 {_134537 : Type'} (P : _134537 -> Prop) (x : _134537) : (@IN _134537 x P) = (P x).
Proof. exact (@lem7170077 _134537 P x). Qed.
Lemma lem7170079 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (@IN _134537 x v) = (v x).
Proof. exact (@lem7170078 _134537 v x). Qed.
Lemma lem7170080 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : (term180 _134537 u x v) = (term183 _134537 u v x).
Proof. exact (MK_COMB (@lem7170075 _134537 u x) (@lem7170079 _134537 v x)). Qed.
Lemma lem7170083 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : (term179 _134537 x u v) = (term183 _134537 u v x).
Proof. exact (TRANS (@lem7170067 _134537 u x v) (@lem7170080 _134537 u v x)). Qed.
Lemma lem7170084 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7170085 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : (term184 _134537 x u v) = (term185 _134537 u v x).
Proof. exact (MK_COMB (@lem7170084) (@lem7170083 _134537 u v x)). Qed.
Lemma lem7170087 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term186 A x s t) = (term187 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem7170088 {_134537 : Type'} (s : _134537 -> Prop) (x : _134537) (t : _134537 -> Prop) : (term186 _134537 x s t) = (term187 _134537 s x t).
Proof. exact (@lem7170087 _134537 s x t). Qed.
Lemma lem7170089 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) (u : _134537 -> Prop) : (term186 _134537 x v u) = (term187 _134537 v x u).
Proof. exact (@lem7170088 _134537 v x u). Qed.
Lemma lem7170093 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7170094 {_134537 : Type'} (P : _134537 -> Prop) (x : _134537) : (@IN _134537 x P) = (P x).
Proof. exact (@lem7170093 _134537 P x). Qed.
Lemma lem7170095 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (@IN _134537 x v) = (v x).
Proof. exact (@lem7170094 _134537 v x). Qed.
Lemma lem7170096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7170097 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (term181 _134537 x v) = (term182 _134537 v x).
Proof. exact (MK_COMB (@lem7170096) (@lem7170095 _134537 v x)). Qed.
Lemma lem7170099 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7170100 {_134537 : Type'} (P : _134537 -> Prop) (x : _134537) : (@IN _134537 x P) = (P x).
Proof. exact (@lem7170099 _134537 P x). Qed.
Lemma lem7170101 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) : (@IN _134537 x u) = (u x).
Proof. exact (@lem7170100 _134537 u x). Qed.
Lemma lem7170102 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7170103 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) : (term188 _134537 x u) = (term189 _134537 u x).
Proof. exact (MK_COMB (@lem7170102) (@lem7170101 _134537 u x)). Qed.
Lemma lem7170104 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) : (term187 _134537 v x u) = (term190 _134537 v u x).
Proof. exact (MK_COMB (@lem7170097 _134537 v x) (@lem7170103 _134537 u x)). Qed.
Lemma lem7170107 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) : (term186 _134537 x v u) = (term190 _134537 v u x).
Proof. exact (TRANS (@lem7170089 _134537 v x u) (@lem7170104 _134537 v u x)). Qed.
Lemma lem7170108 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) : (term178 _134537 x v u) = (term191 _134537 v u x).
Proof. exact (MK_COMB (@lem7170085 _134537 u v x) (@lem7170107 _134537 v u x)). Qed.
Lemma lem7170111 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) : (term177 _134537 x v u) = (term191 _134537 v u x).
Proof. exact (TRANS (@lem7170061 _134537 x v u) (@lem7170108 _134537 v u x)). Qed.
Lemma lem7170112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7170113 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) : (term192 _134537 x v u) = (term193 _134537 v u x).
Proof. exact (MK_COMB (@lem7170112) (@lem7170111 _134537 v u x)). Qed.
Lemma lem7170115 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7170116 {_134537 : Type'} (P : _134537 -> Prop) (x : _134537) : (@IN _134537 x P) = (P x).
Proof. exact (@lem7170115 _134537 P x). Qed.
Lemma lem7170117 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (@IN _134537 x v) = (v x).
Proof. exact (@lem7170116 _134537 v x). Qed.
Lemma lem7170118 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : ((term177 _134537 x v u) = (@IN _134537 x v)) = ((term191 _134537 v u x) = (v x)).
Proof. exact (MK_COMB (@lem7170113 _134537 v u x) (@lem7170117 _134537 v x)). Qed.
Lemma lem7170121 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term194 _134537 u v) = (term195 _134537 u v).
Proof. exact (fun_ext (fun x : _134537 => @lem7170118 _134537 u v x)). Qed.
Lemma lem7170122 {_134537 : Type'} : (@all _134537) = (@all _134537).
Proof. exact (eq_refl (@all _134537)). Qed.
Lemma lem7170123 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term174 _134537 u v) = (term196 _134537 u v).
Proof. exact (MK_COMB (@lem7170122 _134537) (@lem7170121 _134537 u v)). Qed.
Lemma lem7170128 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term196 _134537 u v) = (term174 _134537 u v).
Proof. exact (SYM (@lem7170123 _134537 u v)). Qed.
Lemma lem7170130 (p : Prop) : p = (term197 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7170131 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term196 _134537 u v) = (term198 _134537 u v).
Proof. exact (@lem7170130 (term196 _134537 u v)). Qed.
Lemma lem7170132 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term198 _134537 u v) = (term196 _134537 u v).
Proof. exact (SYM (@lem7170131 _134537 u v)). Qed.
Lemma lem7170133 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (h1 : term199 _134537 u v) : term199 _134537 u v.
Proof. exact (h1). Qed.
Lemma lem7170136 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (h1 : term198 _134537 u v) : term198 _134537 u v.
Proof. exact (h1). Qed.
Lemma lem7170137 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : term200 _134537 u v.
Proof. exact (fun h0 : term198 _134537 u v => @lem7170136 _134537 u v h0). Qed.
Lemma lem7170138 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (h1 : term200 _134537 u v) : term200 _134537 u v.
Proof. exact (h1). Qed.
Lemma lem7170139 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (h1 : term198 _134537 u v) : term198 _134537 u v.
Proof. exact (h1). Qed.
Lemma lem7170140 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (h1 : term198 _134537 u v) (h2 : term200 _134537 u v) : term198 _134537 u v.
Proof. exact (@lem7170138 _134537 u v h2 (@lem7170139 _134537 u v h1)). Qed.
Lemma lem7170141 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (h1 : term198 _134537 u v) : term201 _134537 u v.
Proof. exact (fun h0 : term200 _134537 u v => @lem7170140 _134537 u v h1 h0). Qed.
Lemma lem7170142 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (h1 : term200 _134537 u v) : term200 _134537 u v.
Proof. exact (h1). Qed.
Lemma lem7170143 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (h1 : term198 _134537 u v) (h2 : term200 _134537 u v) : term198 _134537 u v.
Proof. exact (@lem7170141 _134537 u v h1 (@lem7170142 _134537 u v h2)). Qed.
Lemma lem7170144 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (h1 : term200 _134537 u v) : term200 _134537 u v.
Proof. exact (fun h0 : term198 _134537 u v => @lem7170143 _134537 u v h0 h1). Qed.
Lemma lem7170145 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : term202 _134537 u v.
Proof. exact (fun h0 : term200 _134537 u v => @lem7170144 _134537 u v h0). Qed.
Lemma lem7170148 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : term200 _134537 u v.
Proof. exact (@lem7170145 _134537 u v (@lem7170137 _134537 u v)). Qed.
Lemma lem7170149 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : term200 _134537 u v.
Proof. exact (@lem7170148 _134537 u v). Qed.
Lemma lem7170159 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7170160 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term198 _134537 u v) = (term203 _134537 u v).
Proof. exact (@lem7170159 (term199 _134537 u v)). Qed.
Lemma lem7170162 (t : Prop) : (term204 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7170163 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term203 _134537 u v) = (term196 _134537 u v).
Proof. exact (@lem7170162 (term196 _134537 u v)). Qed.
Lemma lem7170168 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term198 _134537 u v) = (term196 _134537 u v).
Proof. exact (TRANS (@lem7170160 _134537 u v) (@lem7170163 _134537 u v)). Qed.
Lemma lem7170175 {_134537 : Type'} (v : _134537 -> Prop) : (term205 _134537 v) = (term206 _134537 v).
Proof. exact (fun_ext (fun u : _134537 -> Prop => @lem7170168 _134537 u v)). Qed.
Lemma lem7170176 {_134537 : Type'} : (@all (_134537 -> Prop)) = (@all (_134537 -> Prop)).
Proof. exact (eq_refl (@all (_134537 -> Prop))). Qed.
Lemma lem7170177 {_134537 : Type'} (v : _134537 -> Prop) : (term207 _134537 v) = (term208 _134537 v).
Proof. exact (MK_COMB (@lem7170176 _134537) (@lem7170175 _134537 v)). Qed.
Lemma lem7170182 {_134537 : Type'} : (term209 _134537) = (term210 _134537).
Proof. exact (fun_ext (fun v : _134537 -> Prop => @lem7170177 _134537 v)). Qed.
Lemma lem7170183 {_134537 : Type'} : (@all (_134537 -> Prop)) = (@all (_134537 -> Prop)).
Proof. exact (eq_refl (@all (_134537 -> Prop))). Qed.
Lemma lem7170192 {_134537 : Type'} : (term211 _134537) = (term212 _134537).
Proof. exact (MK_COMB (@lem7170183 _134537) (@lem7170182 _134537)). Qed.
Lemma lem7170211 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : ((term191 _134537 v u x) = (v x)) = ((term191 _134537 v u x) = (v x)).
Proof. exact (eq_refl ((term191 _134537 v u x) = (v x))). Qed.
Lemma lem7170212 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term195 _134537 u v) = (term195 _134537 u v).
Proof. exact (fun_ext (fun x : _134537 => @lem7170211 _134537 u v x)). Qed.
Lemma lem7170213 {_134537 : Type'} : (@all _134537) = (@all _134537).
Proof. exact (eq_refl (@all _134537)). Qed.
Lemma lem7170214 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term196 _134537 u v) = (term196 _134537 u v).
Proof. exact (MK_COMB (@lem7170213 _134537) (@lem7170212 _134537 u v)). Qed.
Lemma lem7170215 {_134537 : Type'} (v : _134537 -> Prop) : (term206 _134537 v) = (term206 _134537 v).
Proof. exact (fun_ext (fun u : _134537 -> Prop => @lem7170214 _134537 u v)). Qed.
Lemma lem7170216 {_134537 : Type'} : (@all (_134537 -> Prop)) = (@all (_134537 -> Prop)).
Proof. exact (eq_refl (@all (_134537 -> Prop))). Qed.
Lemma lem7170217 {_134537 : Type'} (v : _134537 -> Prop) : (term208 _134537 v) = (term208 _134537 v).
Proof. exact (MK_COMB (@lem7170216 _134537) (@lem7170215 _134537 v)). Qed.
Lemma lem7170218 {_134537 : Type'} : (term210 _134537) = (term210 _134537).
Proof. exact (fun_ext (fun v : _134537 -> Prop => @lem7170217 _134537 v)). Qed.
Lemma lem7170219 {_134537 : Type'} : (@all (_134537 -> Prop)) = (@all (_134537 -> Prop)).
Proof. exact (eq_refl (@all (_134537 -> Prop))). Qed.
Lemma lem7170220 {_134537 : Type'} : (term212 _134537) = (term212 _134537).
Proof. exact (MK_COMB (@lem7170219 _134537) (@lem7170218 _134537)). Qed.
Lemma lem7170247 {_134537 : Type'} : (term211 _134537) = (term212 _134537).
Proof. exact (TRANS (@lem7170192 _134537) (@lem7170220 _134537)). Qed.
Lemma lem7170248 {_134537 : Type'} : (term212 _134537) = (term211 _134537).
Proof. exact (SYM (@lem7170247 _134537)). Qed.
Lemma lem7170250 (p : Prop) : p = (term197 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7170251 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : ((term191 _134537 v u x) = (v x)) = (term213 _134537 u v x).
Proof. exact (@lem7170250 ((term191 _134537 v u x) = (v x))). Qed.
Lemma lem7170252 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : (term213 _134537 u v x) = ((term191 _134537 v u x) = (v x)).
Proof. exact (SYM (@lem7170251 _134537 u v x)). Qed.
Lemma lem7170253 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term214 _134537 u v x) : term214 _134537 u v x.
Proof. exact (h1). Qed.
Lemma lem7170262 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : (term215 _134537 u v x) = (term216 _134537 u v x).
Proof. exact (@lem17045 (u x) (v x)). Qed.
Lemma lem7170271 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) : (term217 _134537 u x) = (u x).
Proof. exact (@lem16933 (u x)). Qed.
Lemma lem7170273 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (term218 _134537 v x) = (term218 _134537 v x).
Proof. exact (eq_refl (term218 _134537 v x)). Qed.
Lemma lem7170274 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) : (term219 _134537 v u x) = (term220 _134537 v u x).
Proof. exact (MK_COMB (@lem7170273 _134537 v x) (@lem7170271 _134537 u x)). Qed.
Lemma lem7170275 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) : (term221 _134537 v u x) = (term219 _134537 v u x).
Proof. exact (@lem17045 (v x) (term189 _134537 u x)). Qed.
Lemma lem7170276 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) : (term221 _134537 v u x) = (term220 _134537 v u x).
Proof. exact (TRANS (@lem7170275 _134537 v u x) (@lem7170274 _134537 v u x)). Qed.
Lemma lem7170280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7170281 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : (term222 _134537 u v x) = (term223 _134537 u v x).
Proof. exact (MK_COMB (@lem7170280) (@lem7170262 _134537 u v x)). Qed.
Lemma lem7170282 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) : (term224 _134537 v u x) = (term225 _134537 v u x).
Proof. exact (MK_COMB (@lem7170281 _134537 u v x) (@lem7170276 _134537 v u x)). Qed.
Lemma lem7170283 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) : (term226 _134537 v u x) = (term224 _134537 v u x).
Proof. exact (@lem17160 (term183 _134537 u v x) (term190 _134537 v u x)). Qed.
Lemma lem7170284 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) : (term226 _134537 v u x) = (term225 _134537 v u x).
Proof. exact (TRANS (@lem7170283 _134537 v u x) (@lem7170282 _134537 v u x)). Qed.
Lemma lem7170289 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (v x) = (v x).
Proof. exact (eq_refl (v x)). Qed.
Lemma lem7170290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7170291 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) : (term227 _134537 v u x) = (term228 _134537 v u x).
Proof. exact (MK_COMB (@lem7170290) (@lem7170284 _134537 v u x)). Qed.
Lemma lem7170292 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : (term229 _134537 u v x) = (term230 _134537 u v x).
Proof. exact (MK_COMB (@lem7170291 _134537 v u x) (@lem7170289 _134537 v x)). Qed.
Lemma lem7170297 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : (term231 _134537 u v x) = (term231 _134537 u v x).
Proof. exact (eq_refl (term231 _134537 u v x)). Qed.
Lemma lem7170298 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : (term232 _134537 u v x) = (term233 _134537 u v x).
Proof. exact (MK_COMB (@lem7170297 _134537 u v x) (@lem7170292 _134537 u v x)). Qed.
Lemma lem7170299 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : (term214 _134537 u v x) = (term232 _134537 u v x).
Proof. exact (@lem17646 (term191 _134537 v u x) (v x)). Qed.
Lemma lem7170304 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : (term214 _134537 u v x) = (term233 _134537 u v x).
Proof. exact (TRANS (@lem7170299 _134537 u v x) (@lem7170298 _134537 u v x)). Qed.
Lemma lem7170373 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term214 _134537 u v x) : term233 _134537 u v x.
Proof. exact (EQ_MP (@lem7170304 _134537 u v x) (@lem7170253 _134537 u v x h1)). Qed.
Lemma lem7170374 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term234 _134537 u v x) : term234 _134537 u v x.
Proof. exact (h1). Qed.
Lemma lem7170375 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : term230 _134537 u v x.
Proof. exact (h1). Qed.
Lemma lem7170377 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term234 _134537 u v x) : term191 _134537 v u x.
Proof. exact (proj1 (@lem7170374 _134537 u v x h1)). Qed.
Lemma lem7170378 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term183 _134537 u v x) : term183 _134537 u v x.
Proof. exact (h1). Qed.
Lemma lem7170379 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) (h1 : term190 _134537 v u x) : term190 _134537 v u x.
Proof. exact (h1). Qed.
Lemma lem7170385 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : term225 _134537 v u x.
Proof. exact (proj1 (@lem7170375 _134537 u v x h1)). Qed.
Lemma lem7170386 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : term220 _134537 v u x.
Proof. exact (proj2 (@lem7170385 _134537 u v x h1)). Qed.
Lemma lem7170387 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : term216 _134537 u v x.
Proof. exact (proj1 (@lem7170385 _134537 u v x h1)). Qed.
Lemma lem7170425 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) : term189 _134537 v x.
Proof. exact (h1). Qed.
Lemma lem7170437 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) : term189 _134537 v x.
Proof. exact (h1). Qed.
Lemma lem7170441 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) : term189 _134537 v x.
Proof. exact (h1). Qed.
Lemma lem7170449 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7170453 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) : term189 _134537 u x.
Proof. exact (h1). Qed.
Lemma lem7170465 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) : term189 _134537 v x.
Proof. exact (h1). Qed.
Lemma lem7170467 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term234 _134537 u v x) : term189 _134537 v x.
Proof. exact (proj2 (@lem7170374 _134537 u v x h1)). Qed.
Lemma lem7170473 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term234 _134537 u v x) : term189 _134537 v x.
Proof. exact (proj2 (@lem7170374 _134537 u v x h1)). Qed.
Lemma lem7170481 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) : term189 _134537 v x.
Proof. exact (h1). Qed.
Lemma lem7170487 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) : term189 _134537 v x.
Proof. exact (h1). Qed.
Lemma lem7170489 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) : term189 _134537 v x.
Proof. exact (h1). Qed.
Lemma lem7170493 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7170495 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) : term189 _134537 u x.
Proof. exact (h1). Qed.
Lemma lem7170501 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) : term189 _134537 v x.
Proof. exact (h1). Qed.
Lemma lem7170503 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term183 _134537 u v x) : v x.
Proof. exact (proj2 (@lem7170378 _134537 u v x h1)). Qed.
Lemma lem7170504 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term183 _134537 u v x) : term235 _134537 v x.
Proof. exact (fun h0 : term189 _134537 v x => @lem7170503 _134537 u v x h1). Qed.
Lemma lem7170506 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7170507 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (term235 _134537 v x) = (v x).
Proof. exact (@lem7170506 (v x)). Qed.
Lemma lem7170508 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term183 _134537 u v x) : v x.
Proof. exact (EQ_MP (@lem7170507 _134537 v x) (@lem7170504 _134537 u v x h1)). Qed.
Lemma lem7170511 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7170513 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (term189 _134537 v x) = (term237 _134537 v x).
Proof. exact (@lem7170511 (v x)). Qed.
Lemma lem7170516 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term234 _134537 u v x) : term237 _134537 v x.
Proof. exact (EQ_MP (@lem7170513 _134537 v x) (@lem7170467 _134537 u v x h1)). Qed.
Lemma lem7170519 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term183 _134537 u v x) (h2 : term234 _134537 u v x) : False.
Proof. exact (@lem7170516 _134537 u v x h2 (@lem7170508 _134537 u v x h1)). Qed.
Lemma lem7170520 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term183 _134537 u v x) (h2 : term234 _134537 u v x) : term238.
Proof. exact (fun h0 : ~ False => @lem7170519 _134537 u v x h1 h2). Qed.
Lemma lem7170522 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7170523 : term238 = False.
Proof. exact (@lem7170522 False). Qed.
Lemma lem7170524 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term183 _134537 u v x) (h2 : term234 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170523) (@lem7170520 _134537 u v x h1 h2)). Qed.
Lemma lem7170526 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) (h1 : term190 _134537 v u x) : v x.
Proof. exact (proj1 (@lem7170379 _134537 v u x h1)). Qed.
Lemma lem7170527 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) (h1 : term190 _134537 v u x) : term235 _134537 v x.
Proof. exact (fun h0 : term189 _134537 v x => @lem7170526 _134537 v u x h1). Qed.
Lemma lem7170529 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7170530 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (term235 _134537 v x) = (v x).
Proof. exact (@lem7170529 (v x)). Qed.
Lemma lem7170531 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) (x : _134537) (h1 : term190 _134537 v u x) : v x.
Proof. exact (EQ_MP (@lem7170530 _134537 v x) (@lem7170527 _134537 v u x h1)). Qed.
Lemma lem7170534 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7170536 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (term189 _134537 v x) = (term237 _134537 v x).
Proof. exact (@lem7170534 (v x)). Qed.
Lemma lem7170539 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term234 _134537 u v x) : term237 _134537 v x.
Proof. exact (EQ_MP (@lem7170536 _134537 v x) (@lem7170473 _134537 u v x h1)). Qed.
Lemma lem7170542 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term190 _134537 v u x) (h2 : term234 _134537 u v x) : False.
Proof. exact (@lem7170539 _134537 u v x h2 (@lem7170531 _134537 v u x h1)). Qed.
Lemma lem7170543 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term190 _134537 v u x) (h2 : term234 _134537 u v x) : term238.
Proof. exact (fun h0 : ~ False => @lem7170542 _134537 u v x h1 h2). Qed.
Lemma lem7170545 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7170546 : term238 = False.
Proof. exact (@lem7170545 False). Qed.
Lemma lem7170547 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term190 _134537 v u x) (h2 : term234 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170546) (@lem7170543 _134537 u v x h1 h2)). Qed.
Lemma lem7170549 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : v x.
Proof. exact (proj2 (@lem7170375 _134537 u v x h1)). Qed.
Lemma lem7170550 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : term235 _134537 v x.
Proof. exact (fun h0 : term189 _134537 v x => @lem7170549 _134537 u v x h1). Qed.
Lemma lem7170552 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7170553 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (term235 _134537 v x) = (v x).
Proof. exact (@lem7170552 (v x)). Qed.
Lemma lem7170554 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : v x.
Proof. exact (EQ_MP (@lem7170553 _134537 v x) (@lem7170550 _134537 u v x h1)). Qed.
Lemma lem7170557 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7170559 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (term189 _134537 v x) = (term237 _134537 v x).
Proof. exact (@lem7170557 (v x)). Qed.
Lemma lem7170562 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) : term237 _134537 v x.
Proof. exact (EQ_MP (@lem7170559 _134537 v x) (@lem7170481 _134537 v x h1)). Qed.
Lemma lem7170565 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (@lem7170562 _134537 v x h1 (@lem7170554 _134537 u v x h2)). Qed.
Lemma lem7170566 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : term238.
Proof. exact (fun h0 : ~ False => @lem7170565 _134537 u v x h1 h2). Qed.
Lemma lem7170568 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7170569 : term238 = False.
Proof. exact (@lem7170568 False). Qed.
Lemma lem7170570 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170569) (@lem7170566 _134537 u v x h1 h2)). Qed.
Lemma lem7170572 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : v x.
Proof. exact (proj2 (@lem7170375 _134537 u v x h1)). Qed.
Lemma lem7170573 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : term235 _134537 v x.
Proof. exact (fun h0 : term189 _134537 v x => @lem7170572 _134537 u v x h1). Qed.
Lemma lem7170575 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7170576 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (term235 _134537 v x) = (v x).
Proof. exact (@lem7170575 (v x)). Qed.
Lemma lem7170577 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : v x.
Proof. exact (EQ_MP (@lem7170576 _134537 v x) (@lem7170573 _134537 u v x h1)). Qed.
Lemma lem7170580 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7170582 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (term189 _134537 v x) = (term237 _134537 v x).
Proof. exact (@lem7170580 (v x)). Qed.
Lemma lem7170585 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) : term237 _134537 v x.
Proof. exact (EQ_MP (@lem7170582 _134537 v x) (@lem7170487 _134537 v x h1)). Qed.
Lemma lem7170588 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (@lem7170585 _134537 v x h1 (@lem7170577 _134537 u v x h2)). Qed.
Lemma lem7170589 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : term238.
Proof. exact (fun h0 : ~ False => @lem7170588 _134537 u v x h1 h2). Qed.
Lemma lem7170591 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7170592 : term238 = False.
Proof. exact (@lem7170591 False). Qed.
Lemma lem7170593 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170592) (@lem7170589 _134537 u v x h1 h2)). Qed.
Lemma lem7170595 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem7170596 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : u x) : term235 _134537 u x.
Proof. exact (fun h0 : term189 _134537 u x => @lem7170595 _134537 u x h1). Qed.
Lemma lem7170598 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7170599 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) : (term235 _134537 u x) = (u x).
Proof. exact (@lem7170598 (u x)). Qed.
Lemma lem7170600 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem7170599 _134537 u x) (@lem7170596 _134537 u x h1)). Qed.
Lemma lem7170603 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7170605 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) : (term189 _134537 u x) = (term237 _134537 u x).
Proof. exact (@lem7170603 (u x)). Qed.
Lemma lem7170608 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) : term237 _134537 u x.
Proof. exact (EQ_MP (@lem7170605 _134537 u x) (@lem7170495 _134537 u x h1)). Qed.
Lemma lem7170611 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : False.
Proof. exact (@lem7170608 _134537 u x h1 (@lem7170600 _134537 u x h2)). Qed.
Lemma lem7170612 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : term238.
Proof. exact (fun h0 : ~ False => @lem7170611 _134537 u x h1 h2). Qed.
Lemma lem7170614 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7170615 : term238 = False.
Proof. exact (@lem7170614 False). Qed.
Lemma lem7170616 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7170615) (@lem7170612 _134537 u x h1 h2)). Qed.
Lemma lem7170618 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : v x.
Proof. exact (proj2 (@lem7170375 _134537 u v x h1)). Qed.
Lemma lem7170619 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : term235 _134537 v x.
Proof. exact (fun h0 : term189 _134537 v x => @lem7170618 _134537 u v x h1). Qed.
Lemma lem7170621 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7170622 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (term235 _134537 v x) = (v x).
Proof. exact (@lem7170621 (v x)). Qed.
Lemma lem7170623 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : v x.
Proof. exact (EQ_MP (@lem7170622 _134537 v x) (@lem7170619 _134537 u v x h1)). Qed.
Lemma lem7170626 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7170628 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) : (term189 _134537 v x) = (term237 _134537 v x).
Proof. exact (@lem7170626 (v x)). Qed.
Lemma lem7170631 {_134537 : Type'} (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) : term237 _134537 v x.
Proof. exact (EQ_MP (@lem7170628 _134537 v x) (@lem7170501 _134537 v x h1)). Qed.
Lemma lem7170634 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (@lem7170631 _134537 v x h1 (@lem7170623 _134537 u v x h2)). Qed.
Lemma lem7170635 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : term238.
Proof. exact (fun h0 : ~ False => @lem7170634 _134537 u v x h1 h2). Qed.
Lemma lem7170637 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7170638 : term238 = False.
Proof. exact (@lem7170637 False). Qed.
Lemma lem7170639 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170638) (@lem7170635 _134537 u v x h1 h2)). Qed.
Lemma lem7170640 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : (term189 _134537 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 v x => @lem7170639 _134537 u v x h1 h2) (fun h3 : False => @lem7170501 _134537 v x h1)). Qed.
Lemma lem7170641 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170640 _134537 u v x h1 h2) (@lem7170501 _134537 v x h1)). Qed.
Lemma lem7170642 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : (term189 _134537 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 u x => @lem7170616 _134537 u x h1 h2) (fun h3 : False => @lem7170495 _134537 u x h1)). Qed.
Lemma lem7170643 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7170642 _134537 u x h1 h2) (@lem7170495 _134537 u x h1)). Qed.
Lemma lem7170644 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7170643 _134537 u x h1 h2) (fun h3 : False => @lem7170493 _134537 u x h2)). Qed.
Lemma lem7170645 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7170644 _134537 u x h1 h2) (@lem7170493 _134537 u x h2)). Qed.
Lemma lem7170646 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : (term189 _134537 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 v x => @lem7170593 _134537 u v x h1 h2) (fun h3 : False => @lem7170489 _134537 v x h1)). Qed.
Lemma lem7170647 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170646 _134537 u v x h1 h2) (@lem7170489 _134537 v x h1)). Qed.
Lemma lem7170648 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : (term189 _134537 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 v x => @lem7170647 _134537 u v x h1 h2) (fun h3 : False => @lem7170487 _134537 v x h1)). Qed.
Lemma lem7170649 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170648 _134537 u v x h1 h2) (@lem7170487 _134537 v x h1)). Qed.
Lemma lem7170650 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : (term189 _134537 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 v x => @lem7170570 _134537 u v x h1 h2) (fun h3 : False => @lem7170481 _134537 v x h1)). Qed.
Lemma lem7170651 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170650 _134537 u v x h1 h2) (@lem7170481 _134537 v x h1)). Qed.
Lemma lem7170652 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : (term189 _134537 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 v x => @lem7170641 _134537 u v x h1 h2) (fun h3 : False => @lem7170465 _134537 v x h1)). Qed.
Lemma lem7170653 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170652 _134537 u v x h1 h2) (@lem7170465 _134537 v x h1)). Qed.
Lemma lem7170654 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : (term189 _134537 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 u x => @lem7170645 _134537 u x h1 h2) (fun h3 : False => @lem7170453 _134537 u x h1)). Qed.
Lemma lem7170655 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7170654 _134537 u x h1 h2) (@lem7170453 _134537 u x h1)). Qed.
Lemma lem7170656 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7170655 _134537 u x h1 h2) (fun h3 : False => @lem7170449 _134537 u x h2)). Qed.
Lemma lem7170657 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7170656 _134537 u x h1 h2) (@lem7170449 _134537 u x h2)). Qed.
Lemma lem7170658 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : (term189 _134537 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 v x => @lem7170649 _134537 u v x h1 h2) (fun h3 : False => @lem7170441 _134537 v x h1)). Qed.
Lemma lem7170659 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170658 _134537 u v x h1 h2) (@lem7170441 _134537 v x h1)). Qed.
Lemma lem7170660 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : (term189 _134537 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 v x => @lem7170659 _134537 u v x h1 h2) (fun h3 : False => @lem7170437 _134537 v x h1)). Qed.
Lemma lem7170661 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170660 _134537 u v x h1 h2) (@lem7170437 _134537 v x h1)). Qed.
Lemma lem7170662 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : (term189 _134537 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 v x => @lem7170651 _134537 u v x h1 h2) (fun h3 : False => @lem7170425 _134537 v x h1)). Qed.
Lemma lem7170663 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170662 _134537 u v x h1 h2) (@lem7170425 _134537 v x h1)). Qed.
Lemma lem7170664 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : (term189 _134537 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 v x => @lem7170653 _134537 u v x h1 h2) (fun h3 : False => @lem7170465 _134537 v x h1)). Qed.
Lemma lem7170665 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170664 _134537 u v x h1 h2) (@lem7170465 _134537 v x h1)). Qed.
Lemma lem7170666 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : (term189 _134537 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 u x => @lem7170657 _134537 u x h1 h2) (fun h3 : False => @lem7170453 _134537 u x h1)). Qed.
Lemma lem7170667 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7170666 _134537 u x h1 h2) (@lem7170453 _134537 u x h1)). Qed.
Lemma lem7170668 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem7170667 _134537 u x h1 h2) (fun h3 : False => @lem7170449 _134537 u x h2)). Qed.
Lemma lem7170669 {_134537 : Type'} (u : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem7170668 _134537 u x h1 h2) (@lem7170449 _134537 u x h2)). Qed.
Lemma lem7170670 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : (term189 _134537 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 v x => @lem7170661 _134537 u v x h1 h2) (fun h3 : False => @lem7170441 _134537 v x h1)). Qed.
Lemma lem7170671 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170670 _134537 u v x h1 h2) (@lem7170441 _134537 v x h1)). Qed.
Lemma lem7170672 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : (term189 _134537 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 v x => @lem7170671 _134537 u v x h1 h2) (fun h3 : False => @lem7170437 _134537 v x h1)). Qed.
Lemma lem7170673 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170672 _134537 u v x h1 h2) (@lem7170437 _134537 v x h1)). Qed.
Lemma lem7170674 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : (term189 _134537 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134537 v x => @lem7170663 _134537 u v x h1 h2) (fun h3 : False => @lem7170425 _134537 v x h1)). Qed.
Lemma lem7170675 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170674 _134537 u v x h1 h2) (@lem7170425 _134537 v x h1)). Qed.
Lemma lem7170676 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : u x) (h2 : term230 _134537 u v x) : False.
Proof. exact (or_elim (@lem7170387 _134537 u v x h2) (fun h0 : term189 _134537 u x => @lem7170669 _134537 u x h0 h1) (fun h0 : term189 _134537 v x => @lem7170665 _134537 u v x h0 h2)). Qed.
Lemma lem7170677 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term189 _134537 v x) (h2 : term230 _134537 u v x) : False.
Proof. exact (or_elim (@lem7170387 _134537 u v x h2) (fun h0 : term189 _134537 u x => @lem7170675 _134537 u v x h1 h2) (fun h0 : term189 _134537 v x => @lem7170673 _134537 u v x h1 h2)). Qed.
Lemma lem7170678 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term230 _134537 u v x) : False.
Proof. exact (or_elim (@lem7170386 _134537 u v x h1) (fun h0 : term189 _134537 v x => @lem7170677 _134537 u v x h0 h1) (fun h0 : u x => @lem7170676 _134537 u v x h0 h1)). Qed.
Lemma lem7170679 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term234 _134537 u v x) : False.
Proof. exact (or_elim (@lem7170377 _134537 u v x h1) (fun h0 : term183 _134537 u v x => @lem7170524 _134537 u v x h0 h1) (fun h0 : term190 _134537 v u x => @lem7170547 _134537 u v x h0 h1)). Qed.
Lemma lem7170680 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term214 _134537 u v x) : False.
Proof. exact (or_elim (@lem7170373 _134537 u v x h1) (fun h0 : term234 _134537 u v x => @lem7170679 _134537 u v x h0) (fun h0 : term230 _134537 u v x => @lem7170678 _134537 u v x h0)). Qed.
Lemma lem7170681 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term214 _134537 u v x) : (term214 _134537 u v x) = False.
Proof. exact (prop_ext (fun h2 : term214 _134537 u v x => @lem7170680 _134537 u v x h1) (fun h2 : False => @lem7170253 _134537 u v x h1)). Qed.
Lemma lem7170682 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) (h1 : term214 _134537 u v x) : False.
Proof. exact (EQ_MP (@lem7170681 _134537 u v x h1) (@lem7170253 _134537 u v x h1)). Qed.
Lemma lem7170683 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : term213 _134537 u v x.
Proof. exact (fun h0 : term214 _134537 u v x => @lem7170682 _134537 u v x h0). Qed.
Lemma lem7170684 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (x : _134537) : (term191 _134537 v u x) = (v x).
Proof. exact (EQ_MP (@lem7170252 _134537 u v x) (@lem7170683 _134537 u v x)). Qed.
Lemma lem7170689 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : term196 _134537 u v.
Proof. exact (fun x : _134537 => @lem7170684 _134537 u v x). Qed.
Lemma lem7170694 {_134537 : Type'} (v : _134537 -> Prop) : term208 _134537 v.
Proof. exact (fun u : _134537 -> Prop => @lem7170689 _134537 u v). Qed.
Lemma lem7170699 {_134537 : Type'} : term212 _134537.
Proof. exact (fun v : _134537 -> Prop => @lem7170694 _134537 v). Qed.
Lemma lem7170700 {_134537 : Type'} : term211 _134537.
Proof. exact (EQ_MP (@lem7170248 _134537) (@lem7170699 _134537)). Qed.
Lemma lem7170701 {_134537 : Type'} (v : _134537 -> Prop) : term239 _134537 v.
Proof. exact (@lem7170700 _134537 v). Qed.
Lemma lem7170702 {_134537 : Type'} (v : _134537 -> Prop) : (term239 _134537 v) = (term207 _134537 v).
Proof. exact (eq_refl (term239 _134537 v)). Qed.
Lemma lem7170703 {_134537 : Type'} (v : _134537 -> Prop) : term207 _134537 v.
Proof. exact (EQ_MP (@lem7170702 _134537 v) (@lem7170701 _134537 v)). Qed.
Lemma lem7170704 {_134537 : Type'} (v : _134537 -> Prop) (u : _134537 -> Prop) : term240 _134537 v u.
Proof. exact (@lem7170703 _134537 v u). Qed.
Lemma lem7170705 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term240 _134537 v u) = (term198 _134537 u v).
Proof. exact (eq_refl (term240 _134537 v u)). Qed.
Lemma lem7170706 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : term198 _134537 u v.
Proof. exact (EQ_MP (@lem7170705 _134537 u v) (@lem7170704 _134537 v u)). Qed.
Lemma lem7170708 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : term198 _134537 u v.
Proof. exact (@lem7170149 _134537 u v (@lem7170706 _134537 u v)). Qed.
Lemma lem7170709 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (h1 : term199 _134537 u v) : False.
Proof. exact (@lem7170708 _134537 u v (@lem7170133 _134537 u v h1)). Qed.
Lemma lem7170710 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (h1 : term199 _134537 u v) : (term199 _134537 u v) = False.
Proof. exact (prop_ext (fun h2 : term199 _134537 u v => @lem7170709 _134537 u v h1) (fun h2 : False => @lem7170133 _134537 u v h1)). Qed.
Lemma lem7170711 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) (h1 : term199 _134537 u v) : False.
Proof. exact (EQ_MP (@lem7170710 _134537 u v h1) (@lem7170133 _134537 u v h1)). Qed.
Lemma lem7170712 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : term198 _134537 u v.
Proof. exact (fun h0 : term199 _134537 u v => @lem7170711 _134537 u v h0). Qed.
Lemma lem7170713 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : term196 _134537 u v.
Proof. exact (EQ_MP (@lem7170132 _134537 u v) (@lem7170712 _134537 u v)). Qed.
Lemma lem7170714 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : term174 _134537 u v.
Proof. exact (EQ_MP (@lem7170128 _134537 u v) (@lem7170713 _134537 u v)). Qed.
Lemma lem7170729 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term172 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7170730 {_134550 : Type'} (s : _134550 -> Prop) (t : _134550 -> Prop) : (s = t) = (term172 _134550 s t).
Proof. exact (@lem7170729 _134550 s t). Qed.
Lemma lem7170731 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : ((term241 _134550 u v) = u) = (term242 _134550 v u).
Proof. exact (@lem7170730 _134550 (term241 _134550 u v) u). Qed.
Lemma lem7170740 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term242 _134550 v u) = ((term241 _134550 u v) = u).
Proof. exact (SYM (@lem7170731 _134550 v u)). Qed.
Lemma lem7170748 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term175 A x s t) = (term176 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem7170749 {_134550 : Type'} (s : _134550 -> Prop) (x : _134550) (t : _134550 -> Prop) : (term175 _134550 x s t) = (term176 _134550 s x t).
Proof. exact (@lem7170748 _134550 s x t). Qed.
Lemma lem7170750 {_134550 : Type'} (x : _134550) (u : _134550 -> Prop) (v : _134550 -> Prop) : (term243 _134550 x u v) = (term244 _134550 x u v).
Proof. exact (@lem7170749 _134550 (@INTER _134550 u v) x (@DIFF _134550 u v)). Qed.
Lemma lem7170754 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term179 A x s t) = (term180 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem7170755 {_134550 : Type'} (s : _134550 -> Prop) (x : _134550) (t : _134550 -> Prop) : (term179 _134550 x s t) = (term180 _134550 s x t).
Proof. exact (@lem7170754 _134550 s x t). Qed.
Lemma lem7170756 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (v : _134550 -> Prop) : (term179 _134550 x u v) = (term180 _134550 u x v).
Proof. exact (@lem7170755 _134550 u x v). Qed.
Lemma lem7170760 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7170761 {_134550 : Type'} (P : _134550 -> Prop) (x : _134550) : (@IN _134550 x P) = (P x).
Proof. exact (@lem7170760 _134550 P x). Qed.
Lemma lem7170762 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (@IN _134550 x u) = (u x).
Proof. exact (@lem7170761 _134550 u x). Qed.
Lemma lem7170763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7170764 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term181 _134550 x u) = (term182 _134550 u x).
Proof. exact (MK_COMB (@lem7170763) (@lem7170762 _134550 u x)). Qed.
Lemma lem7170766 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7170767 {_134550 : Type'} (P : _134550 -> Prop) (x : _134550) : (@IN _134550 x P) = (P x).
Proof. exact (@lem7170766 _134550 P x). Qed.
Lemma lem7170768 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) : (@IN _134550 x v) = (v x).
Proof. exact (@lem7170767 _134550 v x). Qed.
Lemma lem7170769 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term180 _134550 u x v) = (term183 _134550 u v x).
Proof. exact (MK_COMB (@lem7170764 _134550 u x) (@lem7170768 _134550 v x)). Qed.
Lemma lem7170772 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term179 _134550 x u v) = (term183 _134550 u v x).
Proof. exact (TRANS (@lem7170756 _134550 u x v) (@lem7170769 _134550 u v x)). Qed.
Lemma lem7170773 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7170774 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term184 _134550 x u v) = (term185 _134550 u v x).
Proof. exact (MK_COMB (@lem7170773) (@lem7170772 _134550 u v x)). Qed.
Lemma lem7170776 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term186 A x s t) = (term187 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem7170777 {_134550 : Type'} (s : _134550 -> Prop) (x : _134550) (t : _134550 -> Prop) : (term186 _134550 x s t) = (term187 _134550 s x t).
Proof. exact (@lem7170776 _134550 s x t). Qed.
Lemma lem7170778 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (v : _134550 -> Prop) : (term186 _134550 x u v) = (term187 _134550 u x v).
Proof. exact (@lem7170777 _134550 u x v). Qed.
Lemma lem7170782 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7170783 {_134550 : Type'} (P : _134550 -> Prop) (x : _134550) : (@IN _134550 x P) = (P x).
Proof. exact (@lem7170782 _134550 P x). Qed.
Lemma lem7170784 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (@IN _134550 x u) = (u x).
Proof. exact (@lem7170783 _134550 u x). Qed.
Lemma lem7170785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7170786 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term181 _134550 x u) = (term182 _134550 u x).
Proof. exact (MK_COMB (@lem7170785) (@lem7170784 _134550 u x)). Qed.
Lemma lem7170788 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7170789 {_134550 : Type'} (P : _134550 -> Prop) (x : _134550) : (@IN _134550 x P) = (P x).
Proof. exact (@lem7170788 _134550 P x). Qed.
Lemma lem7170790 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) : (@IN _134550 x v) = (v x).
Proof. exact (@lem7170789 _134550 v x). Qed.
Lemma lem7170791 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7170792 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) : (term188 _134550 x v) = (term189 _134550 v x).
Proof. exact (MK_COMB (@lem7170791) (@lem7170790 _134550 v x)). Qed.
Lemma lem7170793 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term187 _134550 u x v) = (term190 _134550 u v x).
Proof. exact (MK_COMB (@lem7170786 _134550 u x) (@lem7170792 _134550 v x)). Qed.
Lemma lem7170796 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term186 _134550 x u v) = (term190 _134550 u v x).
Proof. exact (TRANS (@lem7170778 _134550 u x v) (@lem7170793 _134550 u v x)). Qed.
Lemma lem7170797 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term244 _134550 x u v) = (term245 _134550 u v x).
Proof. exact (MK_COMB (@lem7170774 _134550 u v x) (@lem7170796 _134550 u v x)). Qed.
Lemma lem7170800 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term243 _134550 x u v) = (term245 _134550 u v x).
Proof. exact (TRANS (@lem7170750 _134550 x u v) (@lem7170797 _134550 u v x)). Qed.
Lemma lem7170801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7170802 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term246 _134550 x u v) = (term247 _134550 u v x).
Proof. exact (MK_COMB (@lem7170801) (@lem7170800 _134550 u v x)). Qed.
Lemma lem7170804 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7170805 {_134550 : Type'} (P : _134550 -> Prop) (x : _134550) : (@IN _134550 x P) = (P x).
Proof. exact (@lem7170804 _134550 P x). Qed.
Lemma lem7170806 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (@IN _134550 x u) = (u x).
Proof. exact (@lem7170805 _134550 u x). Qed.
Lemma lem7170807 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) : ((term243 _134550 x u v) = (@IN _134550 x u)) = ((term245 _134550 u v x) = (u x)).
Proof. exact (MK_COMB (@lem7170802 _134550 u v x) (@lem7170806 _134550 u x)). Qed.
Lemma lem7170810 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term248 _134550 v u) = (term249 _134550 v u).
Proof. exact (fun_ext (fun x : _134550 => @lem7170807 _134550 v u x)). Qed.
Lemma lem7170811 {_134550 : Type'} : (@all _134550) = (@all _134550).
Proof. exact (eq_refl (@all _134550)). Qed.
Lemma lem7170812 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term242 _134550 v u) = (term250 _134550 v u).
Proof. exact (MK_COMB (@lem7170811 _134550) (@lem7170810 _134550 v u)). Qed.
Lemma lem7170817 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term250 _134550 v u) = (term242 _134550 v u).
Proof. exact (SYM (@lem7170812 _134550 v u)). Qed.
Lemma lem7170819 (p : Prop) : p = (term197 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7170820 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term250 _134550 v u) = (term251 _134550 v u).
Proof. exact (@lem7170819 (term250 _134550 v u)). Qed.
Lemma lem7170821 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term251 _134550 v u) = (term250 _134550 v u).
Proof. exact (SYM (@lem7170820 _134550 v u)). Qed.
Lemma lem7170822 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (h1 : term252 _134550 v u) : term252 _134550 v u.
Proof. exact (h1). Qed.
Lemma lem7170825 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (h1 : term251 _134550 v u) : term251 _134550 v u.
Proof. exact (h1). Qed.
Lemma lem7170826 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : term253 _134550 v u.
Proof. exact (fun h0 : term251 _134550 v u => @lem7170825 _134550 v u h0). Qed.
Lemma lem7170827 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (h1 : term253 _134550 v u) : term253 _134550 v u.
Proof. exact (h1). Qed.
Lemma lem7170828 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (h1 : term251 _134550 v u) : term251 _134550 v u.
Proof. exact (h1). Qed.
Lemma lem7170829 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (h1 : term251 _134550 v u) (h2 : term253 _134550 v u) : term251 _134550 v u.
Proof. exact (@lem7170827 _134550 v u h2 (@lem7170828 _134550 v u h1)). Qed.
Lemma lem7170830 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (h1 : term251 _134550 v u) : term254 _134550 v u.
Proof. exact (fun h0 : term253 _134550 v u => @lem7170829 _134550 v u h1 h0). Qed.
Lemma lem7170831 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (h1 : term253 _134550 v u) : term253 _134550 v u.
Proof. exact (h1). Qed.
Lemma lem7170832 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (h1 : term251 _134550 v u) (h2 : term253 _134550 v u) : term251 _134550 v u.
Proof. exact (@lem7170830 _134550 v u h1 (@lem7170831 _134550 v u h2)). Qed.
Lemma lem7170833 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (h1 : term253 _134550 v u) : term253 _134550 v u.
Proof. exact (fun h0 : term251 _134550 v u => @lem7170832 _134550 v u h0 h1). Qed.
Lemma lem7170834 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : term255 _134550 v u.
Proof. exact (fun h0 : term253 _134550 v u => @lem7170833 _134550 v u h0). Qed.
Lemma lem7170837 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : term253 _134550 v u.
Proof. exact (@lem7170834 _134550 v u (@lem7170826 _134550 v u)). Qed.
Lemma lem7170838 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : term253 _134550 v u.
Proof. exact (@lem7170837 _134550 v u). Qed.
Lemma lem7170848 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7170849 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term251 _134550 v u) = (term256 _134550 v u).
Proof. exact (@lem7170848 (term252 _134550 v u)). Qed.
Lemma lem7170851 (t : Prop) : (term204 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7170852 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term256 _134550 v u) = (term250 _134550 v u).
Proof. exact (@lem7170851 (term250 _134550 v u)). Qed.
Lemma lem7170857 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term251 _134550 v u) = (term250 _134550 v u).
Proof. exact (TRANS (@lem7170849 _134550 v u) (@lem7170852 _134550 v u)). Qed.
Lemma lem7170864 {_134550 : Type'} (u : _134550 -> Prop) : (term257 _134550 u) = (term258 _134550 u).
Proof. exact (fun_ext (fun v : _134550 -> Prop => @lem7170857 _134550 v u)). Qed.
Lemma lem7170865 {_134550 : Type'} : (@all (_134550 -> Prop)) = (@all (_134550 -> Prop)).
Proof. exact (eq_refl (@all (_134550 -> Prop))). Qed.
Lemma lem7170866 {_134550 : Type'} (u : _134550 -> Prop) : (term259 _134550 u) = (term260 _134550 u).
Proof. exact (MK_COMB (@lem7170865 _134550) (@lem7170864 _134550 u)). Qed.
Lemma lem7170871 {_134550 : Type'} : (term261 _134550) = (term262 _134550).
Proof. exact (fun_ext (fun u : _134550 -> Prop => @lem7170866 _134550 u)). Qed.
Lemma lem7170872 {_134550 : Type'} : (@all (_134550 -> Prop)) = (@all (_134550 -> Prop)).
Proof. exact (eq_refl (@all (_134550 -> Prop))). Qed.
Lemma lem7170881 {_134550 : Type'} : (term263 _134550) = (term264 _134550).
Proof. exact (MK_COMB (@lem7170872 _134550) (@lem7170871 _134550)). Qed.
Lemma lem7170900 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) : ((term245 _134550 u v x) = (u x)) = ((term245 _134550 u v x) = (u x)).
Proof. exact (eq_refl ((term245 _134550 u v x) = (u x))). Qed.
Lemma lem7170901 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term249 _134550 v u) = (term249 _134550 v u).
Proof. exact (fun_ext (fun x : _134550 => @lem7170900 _134550 v u x)). Qed.
Lemma lem7170902 {_134550 : Type'} : (@all _134550) = (@all _134550).
Proof. exact (eq_refl (@all _134550)). Qed.
Lemma lem7170903 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term250 _134550 v u) = (term250 _134550 v u).
Proof. exact (MK_COMB (@lem7170902 _134550) (@lem7170901 _134550 v u)). Qed.
Lemma lem7170904 {_134550 : Type'} (u : _134550 -> Prop) : (term258 _134550 u) = (term258 _134550 u).
Proof. exact (fun_ext (fun v : _134550 -> Prop => @lem7170903 _134550 v u)). Qed.
Lemma lem7170905 {_134550 : Type'} : (@all (_134550 -> Prop)) = (@all (_134550 -> Prop)).
Proof. exact (eq_refl (@all (_134550 -> Prop))). Qed.
Lemma lem7170906 {_134550 : Type'} (u : _134550 -> Prop) : (term260 _134550 u) = (term260 _134550 u).
Proof. exact (MK_COMB (@lem7170905 _134550) (@lem7170904 _134550 u)). Qed.
Lemma lem7170907 {_134550 : Type'} : (term262 _134550) = (term262 _134550).
Proof. exact (fun_ext (fun u : _134550 -> Prop => @lem7170906 _134550 u)). Qed.
Lemma lem7170908 {_134550 : Type'} : (@all (_134550 -> Prop)) = (@all (_134550 -> Prop)).
Proof. exact (eq_refl (@all (_134550 -> Prop))). Qed.
Lemma lem7170909 {_134550 : Type'} : (term264 _134550) = (term264 _134550).
Proof. exact (MK_COMB (@lem7170908 _134550) (@lem7170907 _134550)). Qed.
Lemma lem7170936 {_134550 : Type'} : (term263 _134550) = (term264 _134550).
Proof. exact (TRANS (@lem7170881 _134550) (@lem7170909 _134550)). Qed.
Lemma lem7170937 {_134550 : Type'} : (term264 _134550) = (term263 _134550).
Proof. exact (SYM (@lem7170936 _134550)). Qed.
Lemma lem7170939 (p : Prop) : p = (term197 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7170940 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) : ((term245 _134550 u v x) = (u x)) = (term265 _134550 v u x).
Proof. exact (@lem7170939 ((term245 _134550 u v x) = (u x))). Qed.
Lemma lem7170941 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) : (term265 _134550 v u x) = ((term245 _134550 u v x) = (u x)).
Proof. exact (SYM (@lem7170940 _134550 v u x)). Qed.
Lemma lem7170942 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term266 _134550 v u x) : term266 _134550 v u x.
Proof. exact (h1). Qed.
Lemma lem7170951 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term215 _134550 u v x) = (term216 _134550 u v x).
Proof. exact (@lem17045 (u x) (v x)). Qed.
Lemma lem7170960 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) : (term217 _134550 v x) = (v x).
Proof. exact (@lem16933 (v x)). Qed.
Lemma lem7170962 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term218 _134550 u x) = (term218 _134550 u x).
Proof. exact (eq_refl (term218 _134550 u x)). Qed.
Lemma lem7170963 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term219 _134550 u v x) = (term220 _134550 u v x).
Proof. exact (MK_COMB (@lem7170962 _134550 u x) (@lem7170960 _134550 v x)). Qed.
Lemma lem7170964 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term221 _134550 u v x) = (term219 _134550 u v x).
Proof. exact (@lem17045 (u x) (term189 _134550 v x)). Qed.
Lemma lem7170965 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term221 _134550 u v x) = (term220 _134550 u v x).
Proof. exact (TRANS (@lem7170964 _134550 u v x) (@lem7170963 _134550 u v x)). Qed.
Lemma lem7170969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7170970 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term222 _134550 u v x) = (term223 _134550 u v x).
Proof. exact (MK_COMB (@lem7170969) (@lem7170951 _134550 u v x)). Qed.
Lemma lem7170971 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term267 _134550 u v x) = (term268 _134550 u v x).
Proof. exact (MK_COMB (@lem7170970 _134550 u v x) (@lem7170965 _134550 u v x)). Qed.
Lemma lem7170972 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term269 _134550 u v x) = (term267 _134550 u v x).
Proof. exact (@lem17160 (term183 _134550 u v x) (term190 _134550 u v x)). Qed.
Lemma lem7170973 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term269 _134550 u v x) = (term268 _134550 u v x).
Proof. exact (TRANS (@lem7170972 _134550 u v x) (@lem7170971 _134550 u v x)). Qed.
Lemma lem7170978 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (u x) = (u x).
Proof. exact (eq_refl (u x)). Qed.
Lemma lem7170979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7170980 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) : (term270 _134550 u v x) = (term271 _134550 u v x).
Proof. exact (MK_COMB (@lem7170979) (@lem7170973 _134550 u v x)). Qed.
Lemma lem7170981 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) : (term272 _134550 v u x) = (term273 _134550 v u x).
Proof. exact (MK_COMB (@lem7170980 _134550 u v x) (@lem7170978 _134550 u x)). Qed.
Lemma lem7170986 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) : (term274 _134550 v u x) = (term274 _134550 v u x).
Proof. exact (eq_refl (term274 _134550 v u x)). Qed.
Lemma lem7170987 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) : (term275 _134550 v u x) = (term276 _134550 v u x).
Proof. exact (MK_COMB (@lem7170986 _134550 v u x) (@lem7170981 _134550 v u x)). Qed.
Lemma lem7170988 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) : (term266 _134550 v u x) = (term275 _134550 v u x).
Proof. exact (@lem17646 (term245 _134550 u v x) (u x)). Qed.
Lemma lem7170993 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) : (term266 _134550 v u x) = (term276 _134550 v u x).
Proof. exact (TRANS (@lem7170988 _134550 v u x) (@lem7170987 _134550 v u x)). Qed.
Lemma lem7171062 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term266 _134550 v u x) : term276 _134550 v u x.
Proof. exact (EQ_MP (@lem7170993 _134550 v u x) (@lem7170942 _134550 v u x h1)). Qed.
Lemma lem7171063 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term277 _134550 v u x) : term277 _134550 v u x.
Proof. exact (h1). Qed.
Lemma lem7171064 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : term273 _134550 v u x.
Proof. exact (h1). Qed.
Lemma lem7171066 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term277 _134550 v u x) : term245 _134550 u v x.
Proof. exact (proj1 (@lem7171063 _134550 v u x h1)). Qed.
Lemma lem7171067 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) (h1 : term183 _134550 u v x) : term183 _134550 u v x.
Proof. exact (h1). Qed.
Lemma lem7171068 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) (h1 : term190 _134550 u v x) : term190 _134550 u v x.
Proof. exact (h1). Qed.
Lemma lem7171074 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : term268 _134550 u v x.
Proof. exact (proj1 (@lem7171064 _134550 v u x h1)). Qed.
Lemma lem7171075 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : term220 _134550 u v x.
Proof. exact (proj2 (@lem7171074 _134550 v u x h1)). Qed.
Lemma lem7171076 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : term216 _134550 u v x.
Proof. exact (proj1 (@lem7171074 _134550 v u x h1)). Qed.
Lemma lem7171114 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) : term189 _134550 u x.
Proof. exact (h1). Qed.
Lemma lem7171118 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) : term189 _134550 u x.
Proof. exact (h1). Qed.
Lemma lem7171126 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) : term189 _134550 u x.
Proof. exact (h1). Qed.
Lemma lem7171142 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) : term189 _134550 u x.
Proof. exact (h1). Qed.
Lemma lem7171150 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : v x) : v x.
Proof. exact (h1). Qed.
Lemma lem7171154 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) : term189 _134550 v x.
Proof. exact (h1). Qed.
Lemma lem7171156 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term277 _134550 v u x) : term189 _134550 u x.
Proof. exact (proj2 (@lem7171063 _134550 v u x h1)). Qed.
Lemma lem7171162 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term277 _134550 v u x) : term189 _134550 u x.
Proof. exact (proj2 (@lem7171063 _134550 v u x h1)). Qed.
Lemma lem7171170 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) : term189 _134550 u x.
Proof. exact (h1). Qed.
Lemma lem7171172 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) : term189 _134550 u x.
Proof. exact (h1). Qed.
Lemma lem7171176 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) : term189 _134550 u x.
Proof. exact (h1). Qed.
Lemma lem7171184 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) : term189 _134550 u x.
Proof. exact (h1). Qed.
Lemma lem7171188 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : v x) : v x.
Proof. exact (h1). Qed.
Lemma lem7171190 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) : term189 _134550 v x.
Proof. exact (h1). Qed.
Lemma lem7171192 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) (h1 : term183 _134550 u v x) : u x.
Proof. exact (proj1 (@lem7171067 _134550 u v x h1)). Qed.
Lemma lem7171193 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) (h1 : term183 _134550 u v x) : term235 _134550 u x.
Proof. exact (fun h0 : term189 _134550 u x => @lem7171192 _134550 u v x h1). Qed.
Lemma lem7171195 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7171196 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term235 _134550 u x) = (u x).
Proof. exact (@lem7171195 (u x)). Qed.
Lemma lem7171197 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) (h1 : term183 _134550 u v x) : u x.
Proof. exact (EQ_MP (@lem7171196 _134550 u x) (@lem7171193 _134550 u v x h1)). Qed.
Lemma lem7171200 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7171202 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term189 _134550 u x) = (term237 _134550 u x).
Proof. exact (@lem7171200 (u x)). Qed.
Lemma lem7171205 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term277 _134550 v u x) : term237 _134550 u x.
Proof. exact (EQ_MP (@lem7171202 _134550 u x) (@lem7171156 _134550 v u x h1)). Qed.
Lemma lem7171208 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term183 _134550 u v x) (h2 : term277 _134550 v u x) : False.
Proof. exact (@lem7171205 _134550 v u x h2 (@lem7171197 _134550 u v x h1)). Qed.
Lemma lem7171209 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term183 _134550 u v x) (h2 : term277 _134550 v u x) : term238.
Proof. exact (fun h0 : ~ False => @lem7171208 _134550 v u x h1 h2). Qed.
Lemma lem7171211 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7171212 : term238 = False.
Proof. exact (@lem7171211 False). Qed.
Lemma lem7171213 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term183 _134550 u v x) (h2 : term277 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171212) (@lem7171209 _134550 v u x h1 h2)). Qed.
Lemma lem7171215 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) (h1 : term190 _134550 u v x) : u x.
Proof. exact (proj1 (@lem7171068 _134550 u v x h1)). Qed.
Lemma lem7171216 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) (h1 : term190 _134550 u v x) : term235 _134550 u x.
Proof. exact (fun h0 : term189 _134550 u x => @lem7171215 _134550 u v x h1). Qed.
Lemma lem7171218 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7171219 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term235 _134550 u x) = (u x).
Proof. exact (@lem7171218 (u x)). Qed.
Lemma lem7171220 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) (x : _134550) (h1 : term190 _134550 u v x) : u x.
Proof. exact (EQ_MP (@lem7171219 _134550 u x) (@lem7171216 _134550 u v x h1)). Qed.
Lemma lem7171223 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7171225 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term189 _134550 u x) = (term237 _134550 u x).
Proof. exact (@lem7171223 (u x)). Qed.
Lemma lem7171228 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term277 _134550 v u x) : term237 _134550 u x.
Proof. exact (EQ_MP (@lem7171225 _134550 u x) (@lem7171162 _134550 v u x h1)). Qed.
Lemma lem7171231 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term190 _134550 u v x) (h2 : term277 _134550 v u x) : False.
Proof. exact (@lem7171228 _134550 v u x h2 (@lem7171220 _134550 u v x h1)). Qed.
Lemma lem7171232 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term190 _134550 u v x) (h2 : term277 _134550 v u x) : term238.
Proof. exact (fun h0 : ~ False => @lem7171231 _134550 v u x h1 h2). Qed.
Lemma lem7171234 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7171235 : term238 = False.
Proof. exact (@lem7171234 False). Qed.
Lemma lem7171236 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term190 _134550 u v x) (h2 : term277 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171235) (@lem7171232 _134550 v u x h1 h2)). Qed.
Lemma lem7171238 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : u x.
Proof. exact (proj2 (@lem7171064 _134550 v u x h1)). Qed.
Lemma lem7171239 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : term235 _134550 u x.
Proof. exact (fun h0 : term189 _134550 u x => @lem7171238 _134550 v u x h1). Qed.
Lemma lem7171241 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7171242 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term235 _134550 u x) = (u x).
Proof. exact (@lem7171241 (u x)). Qed.
Lemma lem7171243 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : u x.
Proof. exact (EQ_MP (@lem7171242 _134550 u x) (@lem7171239 _134550 v u x h1)). Qed.
Lemma lem7171246 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7171248 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term189 _134550 u x) = (term237 _134550 u x).
Proof. exact (@lem7171246 (u x)). Qed.
Lemma lem7171251 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) : term237 _134550 u x.
Proof. exact (EQ_MP (@lem7171248 _134550 u x) (@lem7171170 _134550 u x h1)). Qed.
Lemma lem7171254 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (@lem7171251 _134550 u x h1 (@lem7171243 _134550 v u x h2)). Qed.
Lemma lem7171255 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : term238.
Proof. exact (fun h0 : ~ False => @lem7171254 _134550 v u x h1 h2). Qed.
Lemma lem7171257 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7171258 : term238 = False.
Proof. exact (@lem7171257 False). Qed.
Lemma lem7171259 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171258) (@lem7171255 _134550 v u x h1 h2)). Qed.
Lemma lem7171261 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : u x.
Proof. exact (proj2 (@lem7171064 _134550 v u x h1)). Qed.
Lemma lem7171262 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : term235 _134550 u x.
Proof. exact (fun h0 : term189 _134550 u x => @lem7171261 _134550 v u x h1). Qed.
Lemma lem7171264 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7171265 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term235 _134550 u x) = (u x).
Proof. exact (@lem7171264 (u x)). Qed.
Lemma lem7171266 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : u x.
Proof. exact (EQ_MP (@lem7171265 _134550 u x) (@lem7171262 _134550 v u x h1)). Qed.
Lemma lem7171269 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7171271 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term189 _134550 u x) = (term237 _134550 u x).
Proof. exact (@lem7171269 (u x)). Qed.
Lemma lem7171274 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) : term237 _134550 u x.
Proof. exact (EQ_MP (@lem7171271 _134550 u x) (@lem7171176 _134550 u x h1)). Qed.
Lemma lem7171277 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (@lem7171274 _134550 u x h1 (@lem7171266 _134550 v u x h2)). Qed.
Lemma lem7171278 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : term238.
Proof. exact (fun h0 : ~ False => @lem7171277 _134550 v u x h1 h2). Qed.
Lemma lem7171280 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7171281 : term238 = False.
Proof. exact (@lem7171280 False). Qed.
Lemma lem7171282 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171281) (@lem7171278 _134550 v u x h1 h2)). Qed.
Lemma lem7171284 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : u x.
Proof. exact (proj2 (@lem7171064 _134550 v u x h1)). Qed.
Lemma lem7171285 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : term235 _134550 u x.
Proof. exact (fun h0 : term189 _134550 u x => @lem7171284 _134550 v u x h1). Qed.
Lemma lem7171287 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7171288 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term235 _134550 u x) = (u x).
Proof. exact (@lem7171287 (u x)). Qed.
Lemma lem7171289 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : u x.
Proof. exact (EQ_MP (@lem7171288 _134550 u x) (@lem7171285 _134550 v u x h1)). Qed.
Lemma lem7171292 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7171294 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) : (term189 _134550 u x) = (term237 _134550 u x).
Proof. exact (@lem7171292 (u x)). Qed.
Lemma lem7171297 {_134550 : Type'} (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) : term237 _134550 u x.
Proof. exact (EQ_MP (@lem7171294 _134550 u x) (@lem7171184 _134550 u x h1)). Qed.
Lemma lem7171300 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (@lem7171297 _134550 u x h1 (@lem7171289 _134550 v u x h2)). Qed.
Lemma lem7171301 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : term238.
Proof. exact (fun h0 : ~ False => @lem7171300 _134550 v u x h1 h2). Qed.
Lemma lem7171303 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7171304 : term238 = False.
Proof. exact (@lem7171303 False). Qed.
Lemma lem7171305 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171304) (@lem7171301 _134550 v u x h1 h2)). Qed.
Lemma lem7171307 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : v x) : v x.
Proof. exact (h1). Qed.
Lemma lem7171308 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : v x) : term235 _134550 v x.
Proof. exact (fun h0 : term189 _134550 v x => @lem7171307 _134550 v x h1). Qed.
Lemma lem7171310 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7171311 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) : (term235 _134550 v x) = (v x).
Proof. exact (@lem7171310 (v x)). Qed.
Lemma lem7171312 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : v x) : v x.
Proof. exact (EQ_MP (@lem7171311 _134550 v x) (@lem7171308 _134550 v x h1)). Qed.
Lemma lem7171315 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7171317 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) : (term189 _134550 v x) = (term237 _134550 v x).
Proof. exact (@lem7171315 (v x)). Qed.
Lemma lem7171320 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) : term237 _134550 v x.
Proof. exact (EQ_MP (@lem7171317 _134550 v x) (@lem7171190 _134550 v x h1)). Qed.
Lemma lem7171323 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : False.
Proof. exact (@lem7171320 _134550 v x h1 (@lem7171312 _134550 v x h2)). Qed.
Lemma lem7171324 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : term238.
Proof. exact (fun h0 : ~ False => @lem7171323 _134550 v x h1 h2). Qed.
Lemma lem7171326 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7171327 : term238 = False.
Proof. exact (@lem7171326 False). Qed.
Lemma lem7171328 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7171327) (@lem7171324 _134550 v x h1 h2)). Qed.
Lemma lem7171329 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : (term189 _134550 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 v x => @lem7171328 _134550 v x h1 h2) (fun h3 : False => @lem7171190 _134550 v x h1)). Qed.
Lemma lem7171330 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7171329 _134550 v x h1 h2) (@lem7171190 _134550 v x h1)). Qed.
Lemma lem7171331 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : (v x) = False.
Proof. exact (prop_ext (fun h3 : v x => @lem7171330 _134550 v x h1 h2) (fun h3 : False => @lem7171188 _134550 v x h2)). Qed.
Lemma lem7171332 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7171331 _134550 v x h1 h2) (@lem7171188 _134550 v x h2)). Qed.
Lemma lem7171333 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : (term189 _134550 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 u x => @lem7171305 _134550 v u x h1 h2) (fun h3 : False => @lem7171184 _134550 u x h1)). Qed.
Lemma lem7171334 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171333 _134550 v u x h1 h2) (@lem7171184 _134550 u x h1)). Qed.
Lemma lem7171335 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : (term189 _134550 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 u x => @lem7171282 _134550 v u x h1 h2) (fun h3 : False => @lem7171176 _134550 u x h1)). Qed.
Lemma lem7171336 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171335 _134550 v u x h1 h2) (@lem7171176 _134550 u x h1)). Qed.
Lemma lem7171337 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : (term189 _134550 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 u x => @lem7171259 _134550 v u x h1 h2) (fun h3 : False => @lem7171172 _134550 u x h1)). Qed.
Lemma lem7171338 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171337 _134550 v u x h1 h2) (@lem7171172 _134550 u x h1)). Qed.
Lemma lem7171339 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : (term189 _134550 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 u x => @lem7171338 _134550 v u x h1 h2) (fun h3 : False => @lem7171170 _134550 u x h1)). Qed.
Lemma lem7171340 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171339 _134550 v u x h1 h2) (@lem7171170 _134550 u x h1)). Qed.
Lemma lem7171341 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : (term189 _134550 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 v x => @lem7171332 _134550 v x h1 h2) (fun h3 : False => @lem7171154 _134550 v x h1)). Qed.
Lemma lem7171342 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7171341 _134550 v x h1 h2) (@lem7171154 _134550 v x h1)). Qed.
Lemma lem7171343 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : (v x) = False.
Proof. exact (prop_ext (fun h3 : v x => @lem7171342 _134550 v x h1 h2) (fun h3 : False => @lem7171150 _134550 v x h2)). Qed.
Lemma lem7171344 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7171343 _134550 v x h1 h2) (@lem7171150 _134550 v x h2)). Qed.
Lemma lem7171345 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : (term189 _134550 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 u x => @lem7171334 _134550 v u x h1 h2) (fun h3 : False => @lem7171142 _134550 u x h1)). Qed.
Lemma lem7171346 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171345 _134550 v u x h1 h2) (@lem7171142 _134550 u x h1)). Qed.
Lemma lem7171347 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : (term189 _134550 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 u x => @lem7171336 _134550 v u x h1 h2) (fun h3 : False => @lem7171126 _134550 u x h1)). Qed.
Lemma lem7171348 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171347 _134550 v u x h1 h2) (@lem7171126 _134550 u x h1)). Qed.
Lemma lem7171349 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : (term189 _134550 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 u x => @lem7171340 _134550 v u x h1 h2) (fun h3 : False => @lem7171118 _134550 u x h1)). Qed.
Lemma lem7171350 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171349 _134550 v u x h1 h2) (@lem7171118 _134550 u x h1)). Qed.
Lemma lem7171351 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : (term189 _134550 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 u x => @lem7171350 _134550 v u x h1 h2) (fun h3 : False => @lem7171114 _134550 u x h1)). Qed.
Lemma lem7171352 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171351 _134550 v u x h1 h2) (@lem7171114 _134550 u x h1)). Qed.
Lemma lem7171353 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : (term189 _134550 v x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 v x => @lem7171344 _134550 v x h1 h2) (fun h3 : False => @lem7171154 _134550 v x h1)). Qed.
Lemma lem7171354 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7171353 _134550 v x h1 h2) (@lem7171154 _134550 v x h1)). Qed.
Lemma lem7171355 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : (v x) = False.
Proof. exact (prop_ext (fun h3 : v x => @lem7171354 _134550 v x h1 h2) (fun h3 : False => @lem7171150 _134550 v x h2)). Qed.
Lemma lem7171356 {_134550 : Type'} (v : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 v x) (h2 : v x) : False.
Proof. exact (EQ_MP (@lem7171355 _134550 v x h1 h2) (@lem7171150 _134550 v x h2)). Qed.
Lemma lem7171357 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : (term189 _134550 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 u x => @lem7171346 _134550 v u x h1 h2) (fun h3 : False => @lem7171142 _134550 u x h1)). Qed.
Lemma lem7171358 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171357 _134550 v u x h1 h2) (@lem7171142 _134550 u x h1)). Qed.
Lemma lem7171359 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : (term189 _134550 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 u x => @lem7171348 _134550 v u x h1 h2) (fun h3 : False => @lem7171126 _134550 u x h1)). Qed.
Lemma lem7171360 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171359 _134550 v u x h1 h2) (@lem7171126 _134550 u x h1)). Qed.
Lemma lem7171361 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : (term189 _134550 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 u x => @lem7171352 _134550 v u x h1 h2) (fun h3 : False => @lem7171118 _134550 u x h1)). Qed.
Lemma lem7171362 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171361 _134550 v u x h1 h2) (@lem7171118 _134550 u x h1)). Qed.
Lemma lem7171363 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : (term189 _134550 u x) = False.
Proof. exact (prop_ext (fun h3 : term189 _134550 u x => @lem7171362 _134550 v u x h1 h2) (fun h3 : False => @lem7171114 _134550 u x h1)). Qed.
Lemma lem7171364 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171363 _134550 v u x h1 h2) (@lem7171114 _134550 u x h1)). Qed.
Lemma lem7171365 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : v x) (h2 : term273 _134550 v u x) : False.
Proof. exact (or_elim (@lem7171076 _134550 v u x h2) (fun h0 : term189 _134550 u x => @lem7171358 _134550 v u x h0 h2) (fun h0 : term189 _134550 v x => @lem7171356 _134550 v x h0 h1)). Qed.
Lemma lem7171366 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term189 _134550 u x) (h2 : term273 _134550 v u x) : False.
Proof. exact (or_elim (@lem7171076 _134550 v u x h2) (fun h0 : term189 _134550 u x => @lem7171364 _134550 v u x h1 h2) (fun h0 : term189 _134550 v x => @lem7171360 _134550 v u x h1 h2)). Qed.
Lemma lem7171367 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term273 _134550 v u x) : False.
Proof. exact (or_elim (@lem7171075 _134550 v u x h1) (fun h0 : term189 _134550 u x => @lem7171366 _134550 v u x h0 h1) (fun h0 : v x => @lem7171365 _134550 v u x h0 h1)). Qed.
Lemma lem7171368 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term277 _134550 v u x) : False.
Proof. exact (or_elim (@lem7171066 _134550 v u x h1) (fun h0 : term183 _134550 u v x => @lem7171213 _134550 v u x h0 h1) (fun h0 : term190 _134550 u v x => @lem7171236 _134550 v u x h0 h1)). Qed.
Lemma lem7171369 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term266 _134550 v u x) : False.
Proof. exact (or_elim (@lem7171062 _134550 v u x h1) (fun h0 : term277 _134550 v u x => @lem7171368 _134550 v u x h0) (fun h0 : term273 _134550 v u x => @lem7171367 _134550 v u x h0)). Qed.
Lemma lem7171370 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term266 _134550 v u x) : (term266 _134550 v u x) = False.
Proof. exact (prop_ext (fun h2 : term266 _134550 v u x => @lem7171369 _134550 v u x h1) (fun h2 : False => @lem7170942 _134550 v u x h1)). Qed.
Lemma lem7171371 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) (h1 : term266 _134550 v u x) : False.
Proof. exact (EQ_MP (@lem7171370 _134550 v u x h1) (@lem7170942 _134550 v u x h1)). Qed.
Lemma lem7171372 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) : term265 _134550 v u x.
Proof. exact (fun h0 : term266 _134550 v u x => @lem7171371 _134550 v u x h0). Qed.
Lemma lem7171373 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (x : _134550) : (term245 _134550 u v x) = (u x).
Proof. exact (EQ_MP (@lem7170941 _134550 v u x) (@lem7171372 _134550 v u x)). Qed.
Lemma lem7171378 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : term250 _134550 v u.
Proof. exact (fun x : _134550 => @lem7171373 _134550 v u x). Qed.
Lemma lem7171383 {_134550 : Type'} (u : _134550 -> Prop) : term260 _134550 u.
Proof. exact (fun v : _134550 -> Prop => @lem7171378 _134550 v u). Qed.
Lemma lem7171388 {_134550 : Type'} : term264 _134550.
Proof. exact (fun u : _134550 -> Prop => @lem7171383 _134550 u). Qed.
Lemma lem7171389 {_134550 : Type'} : term263 _134550.
Proof. exact (EQ_MP (@lem7170937 _134550) (@lem7171388 _134550)). Qed.
Lemma lem7171390 {_134550 : Type'} (u : _134550 -> Prop) : term278 _134550 u.
Proof. exact (@lem7171389 _134550 u). Qed.
Lemma lem7171391 {_134550 : Type'} (u : _134550 -> Prop) : (term278 _134550 u) = (term259 _134550 u).
Proof. exact (eq_refl (term278 _134550 u)). Qed.
Lemma lem7171392 {_134550 : Type'} (u : _134550 -> Prop) : term259 _134550 u.
Proof. exact (EQ_MP (@lem7171391 _134550 u) (@lem7171390 _134550 u)). Qed.
Lemma lem7171393 {_134550 : Type'} (u : _134550 -> Prop) (v : _134550 -> Prop) : term279 _134550 u v.
Proof. exact (@lem7171392 _134550 u v). Qed.
Lemma lem7171394 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term279 _134550 u v) = (term251 _134550 v u).
Proof. exact (eq_refl (term279 _134550 u v)). Qed.
Lemma lem7171395 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : term251 _134550 v u.
Proof. exact (EQ_MP (@lem7171394 _134550 v u) (@lem7171393 _134550 u v)). Qed.
Lemma lem7171397 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : term251 _134550 v u.
Proof. exact (@lem7170838 _134550 v u (@lem7171395 _134550 v u)). Qed.
Lemma lem7171398 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (h1 : term252 _134550 v u) : False.
Proof. exact (@lem7171397 _134550 v u (@lem7170822 _134550 v u h1)). Qed.
Lemma lem7171399 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (h1 : term252 _134550 v u) : (term252 _134550 v u) = False.
Proof. exact (prop_ext (fun h2 : term252 _134550 v u => @lem7171398 _134550 v u h1) (fun h2 : False => @lem7170822 _134550 v u h1)). Qed.
Lemma lem7171400 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) (h1 : term252 _134550 v u) : False.
Proof. exact (EQ_MP (@lem7171399 _134550 v u h1) (@lem7170822 _134550 v u h1)). Qed.
Lemma lem7171401 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : term251 _134550 v u.
Proof. exact (fun h0 : term252 _134550 v u => @lem7171400 _134550 v u h0). Qed.
Lemma lem7171402 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : term250 _134550 v u.
Proof. exact (EQ_MP (@lem7170821 _134550 v u) (@lem7171401 _134550 v u)). Qed.
Lemma lem7171403 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : term242 _134550 v u.
Proof. exact (EQ_MP (@lem7170817 _134550 v u) (@lem7171402 _134550 v u)). Qed.
Lemma lem7171405 {A : Type'} : term280 A.
Proof. exact (@lem7067826 A). Qed.
Lemma lem7171406 {A : Type'} (f : A -> real) : term281 A f.
Proof. exact (@lem7171405 A f). Qed.
Lemma lem7171407 {A : Type'} (f : A -> real) : (term281 A f) = (term282 A f).
Proof. exact (eq_refl (term281 A f)). Qed.
Lemma lem7171408 {A : Type'} (f : A -> real) : term282 A f.
Proof. exact (EQ_MP (@lem7171407 A f) (@lem7171406 A f)). Qed.
Lemma lem7171409 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) : term283 A f u v.
Proof. exact (@lem7171408 A f (@INTER A u v)). Qed.
Lemma lem7171410 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term283 A f u v) = (term284 A u v f).
Proof. exact (eq_refl (term283 A f u v)). Qed.
Lemma lem7171411 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term284 A u v f.
Proof. exact (EQ_MP (@lem7171410 A u v f) (@lem7171409 A f u v)). Qed.
Lemma lem7171412 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term285 A v u f) : term285 A v u f.
Proof. exact (h1). Qed.
Lemma lem7171413 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term286 A v u f) : term286 A v u f.
Proof. exact (h1). Qed.
Lemma lem7171414 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : @FINITE A u.
Proof. exact (h1). Qed.
Lemma lem7171415 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term287 A v u f) : term287 A v u f.
Proof. exact (h1). Qed.
Lemma lem7171416 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (h1). Qed.
Lemma lem7171417 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : term288 A v u f.
Proof. exact (h1). Qed.
Lemma lem7171418 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : term289 A u v f.
Proof. exact (h1). Qed.
Lemma lem7171419 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term284 A u v f) : term284 A u v f.
Proof. exact (h1). Qed.
Lemma lem7171420 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term284 A u v f) : term290 A f u v.
Proof. exact (@lem7171419 A u v f h1 (@DIFF A u v)). Qed.
Lemma lem7171421 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term290 A f u v) = (term291 A u v f).
Proof. exact (eq_refl (term290 A f u v)). Qed.
Lemma lem7171422 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term284 A u v f) : term291 A u v f.
Proof. exact (EQ_MP (@lem7171421 A u v f) (@lem7171420 A u v f h1)). Qed.
Lemma lem7171423 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term284 A u v f) : term292 A f v u.
Proof. exact (@lem7171419 A u v f h1 (@DIFF A v u)). Qed.
Lemma lem7171424 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term292 A f v u) = (term293 A v u f).
Proof. exact (eq_refl (term292 A f v u)). Qed.
Lemma lem7171425 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term284 A u v f) : term293 A v u f.
Proof. exact (EQ_MP (@lem7171424 A v u f) (@lem7171423 A u v f h1)). Qed.
Lemma lem7171439 {_134550 : Type'} (v : _134550 -> Prop) (u : _134550 -> Prop) : (term241 _134550 u v) = u.
Proof. exact (EQ_MP (@lem7170740 _134550 v u) (@lem7171403 _134550 v u)). Qed.
Lemma lem7171440 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term241 A u v) = u.
Proof. exact (@lem7171439 A v u). Qed.
Lemma lem7171441 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (eq_refl (@sum A)). Qed.
Lemma lem7171442 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term294 A u v) = (@sum A u).
Proof. exact (MK_COMB (@lem7171441 A) (@lem7171440 A v u)). Qed.
Lemma lem7171443 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7171444 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term295 A u v f) = (@sum A u f).
Proof. exact (MK_COMB (@lem7171442 A v u) (@lem7171443 A f)). Qed.
Lemma lem7171445 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7171446 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term296 A u v f) = (term297 A u f).
Proof. exact (MK_COMB (@lem7171445) (@lem7171444 A v u f)). Qed.
Lemma lem7171447 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term298 A u v f) = (term298 A u v f).
Proof. exact (eq_refl (term298 A u v f)). Qed.
Lemma lem7171448 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : ((term295 A u v f) = (term298 A u v f)) = ((@sum A u f) = (term298 A u v f)).
Proof. exact (MK_COMB (@lem7171446 A v u f) (@lem7171447 A u v f)). Qed.
Lemma lem7171451 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term299 A u v) = (term299 A u v).
Proof. exact (eq_refl (term299 A u v)). Qed.
Lemma lem7171452 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term291 A u v f) = (term300 A u v f).
Proof. exact (MK_COMB (@lem7171451 A u v) (@lem7171448 A u v f)). Qed.
Lemma lem7171455 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7171456 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term301 A u v f) = (term302 A u v f).
Proof. exact (MK_COMB (@lem7171455) (@lem7171452 A u v f)). Qed.
Lemma lem7171468 {_134537 : Type'} (u : _134537 -> Prop) (v : _134537 -> Prop) : (term173 _134537 v u) = v.
Proof. exact (EQ_MP (@lem7170051 _134537 u v) (@lem7170714 _134537 u v)). Qed.
Lemma lem7171469 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term173 A v u) = v.
Proof. exact (@lem7171468 A u v). Qed.
Lemma lem7171470 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (eq_refl (@sum A)). Qed.
Lemma lem7171471 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term303 A v u) = (@sum A v).
Proof. exact (MK_COMB (@lem7171470 A) (@lem7171469 A u v)). Qed.
Lemma lem7171472 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7171473 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term304 A v u f) = (@sum A v f).
Proof. exact (MK_COMB (@lem7171471 A u v) (@lem7171472 A f)). Qed.
Lemma lem7171474 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7171475 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term305 A v u f) = (term297 A v f).
Proof. exact (MK_COMB (@lem7171474) (@lem7171473 A u v f)). Qed.
Lemma lem7171476 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term306 A v u f) = (term306 A v u f).
Proof. exact (eq_refl (term306 A v u f)). Qed.
Lemma lem7171477 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term304 A v u f) = (term306 A v u f)) = ((@sum A v f) = (term306 A v u f)).
Proof. exact (MK_COMB (@lem7171475 A u v f) (@lem7171476 A v u f)). Qed.
Lemma lem7171480 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term307 A v u) = (term307 A v u).
Proof. exact (eq_refl (term307 A v u)). Qed.
Lemma lem7171481 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term293 A v u f) = (term308 A v u f).
Proof. exact (MK_COMB (@lem7171480 A v u) (@lem7171477 A v u f)). Qed.
Lemma lem7171484 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7171485 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term309 A v u f) = (term310 A v u f).
Proof. exact (MK_COMB (@lem7171484) (@lem7171481 A v u f)). Qed.
Lemma lem7171486 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term311 A u v f) = (term311 A u v f).
Proof. exact (eq_refl (term311 A u v f)). Qed.
Lemma lem7171487 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term312 A u v f) = (term313 A u v f).
Proof. exact (MK_COMB (@lem7171485 A v u f) (@lem7171486 A u v f)). Qed.
Lemma lem7171490 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term314 A u v f) = (term315 A u v f).
Proof. exact (MK_COMB (@lem7171456 A u v f) (@lem7171487 A u v f)). Qed.
Lemma lem7171493 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term315 A u v f) = (term314 A u v f).
Proof. exact (SYM (@lem7171490 A u v f)). Qed.
Lemma lem7171494 {A : Type'} (s : A -> Prop) : term316 A s.
Proof. exact (@lem3607909 A s). Qed.
Lemma lem7171495 {A : Type'} (s : A -> Prop) : (term316 A s) = (term317 A s).
Proof. exact (eq_refl (term316 A s)). Qed.
Lemma lem7171496 {A : Type'} (s : A -> Prop) : term317 A s.
Proof. exact (EQ_MP (@lem7171495 A s) (@lem7171494 A s)). Qed.
Lemma lem7171497 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term318 A s t.
Proof. exact (@lem7171496 A s t). Qed.
Lemma lem7171498 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term318 A s t) = (term319 A s t).
Proof. exact (eq_refl (term318 A s t)). Qed.
Lemma lem7171499 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term319 A s t.
Proof. exact (EQ_MP (@lem7171498 A s t) (@lem7171497 A s t)). Qed.
Lemma lem7171500 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term320 A s t) : term320 A s t.
Proof. exact (h1). Qed.
Lemma lem7171501 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term320 A s t) : term321 A s t.
Proof. exact (@lem7171499 A s t (@lem7171500 A s t h1)). Qed.
Lemma lem7171502 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term321 A s t) = ((term321 A s t) = True).
Proof. exact (@lem7 (term321 A s t)). Qed.
Lemma lem7171503 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term320 A s t) : (term321 A s t) = True.
Proof. exact (EQ_MP (@lem7171502 A s t) (@lem7171501 A s t h1)). Qed.
Lemma lem7171509 {_97970 : Type'} (s : _97970 -> Prop) : term322 _97970 s.
Proof. exact (@lem3734933 _97970 s). Qed.
Lemma lem7171510 {_97970 : Type'} (s : _97970 -> Prop) : (term322 _97970 s) = (term323 _97970 s).
Proof. exact (eq_refl (term322 _97970 s)). Qed.
Lemma lem7171511 {_97970 : Type'} (s : _97970 -> Prop) : term323 _97970 s.
Proof. exact (EQ_MP (@lem7171510 _97970 s) (@lem7171509 _97970 s)). Qed.
Lemma lem7171512 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term324 _97970 s t.
Proof. exact (@lem7171511 _97970 s t). Qed.
Lemma lem7171513 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term324 _97970 s t) = (term325 _97970 s t).
Proof. exact (eq_refl (term324 _97970 s t)). Qed.
Lemma lem7171514 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term325 _97970 s t.
Proof. exact (EQ_MP (@lem7171513 _97970 s t) (@lem7171512 _97970 s t)). Qed.
Lemma lem7171515 {_97970 : Type'} (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : @FINITE _97970 s.
Proof. exact (h1). Qed.
Lemma lem7171516 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : term326 _97970 s t.
Proof. exact (@lem7171514 _97970 s t (@lem7171515 _97970 s h1)). Qed.
Lemma lem7171517 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term326 _97970 s t) = ((term326 _97970 s t) = True).
Proof. exact (@lem7 (term326 _97970 s t)). Qed.
Lemma lem7171518 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : (term326 _97970 s t) = True.
Proof. exact (EQ_MP (@lem7171517 _97970 s t) (@lem7171516 _97970 t s h1)). Qed.
Lemma lem7171524 {A : Type'} (u : A -> Prop) : (@FINITE A u) = ((@FINITE A u) = True).
Proof. exact (@lem7 (@FINITE A u)). Qed.
Lemma lem7171526 {A : Type'} (v : A -> Prop) : (@FINITE A v) = ((@FINITE A v) = True).
Proof. exact (@lem7 (@FINITE A v)). Qed.
Lemma lem7171555 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term327 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7171556 (p : Prop) (q : Prop) (p' : Prop) : term328 p q p'.
Proof. exact (fun q' : Prop => @lem7171555 p q p' q'). Qed.
Lemma lem7171557 (p : Prop) (q : Prop) : term329 p q.
Proof. exact (fun p' : Prop => @lem7171556 p q p'). Qed.
Lemma lem7171558 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term330 A u v f.
Proof. exact (@lem7171557 (term300 A u v f) (term313 A u v f)). Qed.
Lemma lem7171559 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) : term331 A u v f p'.
Proof. exact (@lem7171558 A u v f p'). Qed.
Lemma lem7171560 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) : (term331 A u v f p') = (term332 A u v f p').
Proof. exact (eq_refl (term331 A u v f p')). Qed.
Lemma lem7171561 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) : term332 A u v f p'.
Proof. exact (EQ_MP (@lem7171560 A u v f p') (@lem7171559 A u v f p')). Qed.
Lemma lem7171562 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term333 A u v f p' q'.
Proof. exact (@lem7171561 A u v f p' q'). Qed.
Lemma lem7171563 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term333 A u v f p' q') = (term334 A u v f p' q').
Proof. exact (eq_refl (term333 A u v f p' q')). Qed.
Lemma lem7171564 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term334 A u v f p' q'.
Proof. exact (EQ_MP (@lem7171563 A u v f p' q') (@lem7171562 A u v f p' q')). Qed.
Lemma lem7171568 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term327 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7171569 (p : Prop) (q : Prop) (p' : Prop) : term328 p q p'.
Proof. exact (fun q' : Prop => @lem7171568 p q p' q'). Qed.
Lemma lem7171570 (p : Prop) (q : Prop) : term329 p q.
Proof. exact (fun p' : Prop => @lem7171569 p q p'). Qed.
Lemma lem7171571 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term335 A u v f.
Proof. exact (@lem7171570 (term336 A u v) ((@sum A u f) = (term298 A u v f))). Qed.
Lemma lem7171572 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) : term337 A u v f p'.
Proof. exact (@lem7171571 A u v f p'). Qed.
Lemma lem7171573 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) : (term337 A u v f p') = (term338 A u v f p').
Proof. exact (eq_refl (term337 A u v f p')). Qed.
Lemma lem7171574 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) : term338 A u v f p'.
Proof. exact (EQ_MP (@lem7171573 A u v f p') (@lem7171572 A u v f p')). Qed.
Lemma lem7171575 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term339 A u v f p' q'.
Proof. exact (@lem7171574 A u v f p' q'). Qed.
Lemma lem7171576 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term339 A u v f p' q') = (term340 A u v f p' q').
Proof. exact (eq_refl (term339 A u v f p' q')). Qed.
Lemma lem7171577 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term340 A u v f p' q'.
Proof. exact (EQ_MP (@lem7171576 A u v f p' q') (@lem7171575 A u v f p' q')). Qed.
Lemma lem7171581 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term341 A s t.
Proof. exact (fun h0 : term320 A s t => @lem7171503 A s t h0). Qed.
Lemma lem7171582 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term341 A s t.
Proof. exact (@lem7171581 A s t). Qed.
Lemma lem7171583 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term341 A u v.
Proof. exact (@lem7171582 A u v). Qed.
Lemma lem7171587 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : (@FINITE A u) = True.
Proof. exact (EQ_MP (@lem7171524 A u) (@lem7171414 A u h1)). Qed.
Lemma lem7171588 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7171589 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : (term342 A u) = (or True).
Proof. exact (MK_COMB (@lem7171588) (@lem7171587 A u h1)). Qed.
Lemma lem7171591 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : (@FINITE A v) = True.
Proof. exact (EQ_MP (@lem7171526 A v) (@lem7171416 A v h1)). Qed.
Lemma lem7171592 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term320 A u v) = (True \/ True).
Proof. exact (MK_COMB (@lem7171589 A u h1) (@lem7171591 A v h2)). Qed.
Lemma lem7171594 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem7171595 : (True \/ True) = True.
Proof. exact (@lem7171594 True). Qed.
Lemma lem7171596 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term320 A u v) = True.
Proof. exact (TRANS (@lem7171592 A u v h1 h2) (@lem7171595)). Qed.
Lemma lem7171597 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : True = (term320 A u v).
Proof. exact (SYM (@lem7171596 A u v h1 h2)). Qed.
Lemma lem7171598 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term320 A u v.
Proof. exact (EQ_MP (@lem7171597 A u v h1 h2) (@lem0)). Qed.
Lemma lem7171599 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term321 A u v) = True.
Proof. exact (@lem7171583 A u v (@lem7171598 A u v h1 h2)). Qed.
Lemma lem7171600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7171601 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term343 A u v) = (and True).
Proof. exact (MK_COMB (@lem7171600) (@lem7171599 A u v h1 h2)). Qed.
Lemma lem7171605 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term344 _97970 s t.
Proof. exact (fun h0 : @FINITE _97970 s => @lem7171518 _97970 t s h0). Qed.
Lemma lem7171606 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term344 A s t.
Proof. exact (@lem7171605 A s t). Qed.
Lemma lem7171607 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term344 A u v.
Proof. exact (@lem7171606 A u v). Qed.
Lemma lem7171609 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : (@FINITE A u) = True.
Proof. exact (EQ_MP (@lem7171524 A u) (@lem7171414 A u h1)). Qed.
Lemma lem7171610 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : True = (@FINITE A u).
Proof. exact (SYM (@lem7171609 A u h1)). Qed.
Lemma lem7171611 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : @FINITE A u.
Proof. exact (EQ_MP (@lem7171610 A u h1) (@lem0)). Qed.
Lemma lem7171612 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : @FINITE A u) : (term326 A u v) = True.
Proof. exact (@lem7171607 A u v (@lem7171611 A u h1)). Qed.
Lemma lem7171613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7171614 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : @FINITE A u) : (term345 A u v) = (and True).
Proof. exact (MK_COMB (@lem7171613) (@lem7171612 A v u h1)). Qed.
Lemma lem7171615 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term346 A u v) = (term346 A u v).
Proof. exact (eq_refl (term346 A u v)). Qed.
Lemma lem7171616 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : @FINITE A u) : (term347 A u v) = (term348 A u v).
Proof. exact (MK_COMB (@lem7171614 A v u h1) (@lem7171615 A u v)). Qed.
Lemma lem7171618 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7171619 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term348 A u v) = (term346 A u v).
Proof. exact (@lem7171618 (term346 A u v)). Qed.
Lemma lem7171620 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : @FINITE A u) : (term347 A u v) = (term346 A u v).
Proof. exact (TRANS (@lem7171616 A v u h1) (@lem7171619 A u v)). Qed.
Lemma lem7171621 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term336 A u v) = (term348 A u v).
Proof. exact (MK_COMB (@lem7171601 A u v h1 h2) (@lem7171620 A v u h1)). Qed.
Lemma lem7171623 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7171624 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term348 A u v) = (term346 A u v).
Proof. exact (@lem7171623 (term346 A u v)). Qed.
Lemma lem7171625 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term336 A u v) = (term346 A u v).
Proof. exact (TRANS (@lem7171621 A u v h1 h2) (@lem7171624 A u v)). Qed.
Lemma lem7171626 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (q' : Prop) : term349 A f u v q'.
Proof. exact (@lem7171577 A u v f (term346 A u v) q'). Qed.
Lemma lem7171627 {A : Type'} (f : A -> real) (q' : Prop) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term350 A f u v q'.
Proof. exact (@lem7171626 A f u v q' (@lem7171625 A u v h1 h2)). Qed.
Lemma lem7171633 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : ((@sum A u f) = (term298 A u v f)) = ((@sum A u f) = (term298 A u v f)).
Proof. exact (eq_refl ((@sum A u f) = (term298 A u v f))). Qed.
Lemma lem7171634 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term351 A u v f.
Proof. exact (fun h0 : term346 A u v => @lem7171633 A u v f). Qed.
Lemma lem7171635 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term352 A u v f.
Proof. exact (@lem7171627 A f ((@sum A u f) = (term298 A u v f)) u v h1 h2). Qed.
Lemma lem7171636 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term300 A u v f) = (term353 A u v f).
Proof. exact (@lem7171635 A f u v h1 h2 (@lem7171634 A u v f)). Qed.
Lemma lem7171664 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (q' : Prop) : term354 A u v f q'.
Proof. exact (@lem7171564 A u v f (term353 A u v f) q'). Qed.
Lemma lem7171665 {A : Type'} (f : A -> real) (q' : Prop) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term355 A u v f q'.
Proof. exact (@lem7171664 A u v f q' (@lem7171636 A f u v h1 h2)). Qed.
Lemma lem7171677 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term327 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7171678 (p : Prop) (q : Prop) (p' : Prop) : term328 p q p'.
Proof. exact (fun q' : Prop => @lem7171677 p q p' q'). Qed.
Lemma lem7171679 (p : Prop) (q : Prop) : term329 p q.
Proof. exact (fun p' : Prop => @lem7171678 p q p'). Qed.
Lemma lem7171680 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term356 A u v f.
Proof. exact (@lem7171679 (term308 A v u f) (term311 A u v f)). Qed.
Lemma lem7171681 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) : term357 A u v f p'.
Proof. exact (@lem7171680 A u v f p'). Qed.
Lemma lem7171682 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) : (term357 A u v f p') = (term358 A u v f p').
Proof. exact (eq_refl (term357 A u v f p')). Qed.
Lemma lem7171683 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) : term358 A u v f p'.
Proof. exact (EQ_MP (@lem7171682 A u v f p') (@lem7171681 A u v f p')). Qed.
Lemma lem7171684 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term359 A u v f p' q'.
Proof. exact (@lem7171683 A u v f p' q'). Qed.
Lemma lem7171685 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term359 A u v f p' q') = (term360 A u v f p' q').
Proof. exact (eq_refl (term359 A u v f p' q')). Qed.
Lemma lem7171686 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term360 A u v f p' q'.
Proof. exact (EQ_MP (@lem7171685 A u v f p' q') (@lem7171684 A u v f p' q')). Qed.
Lemma lem7171690 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term327 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7171691 (p : Prop) (q : Prop) (p' : Prop) : term328 p q p'.
Proof. exact (fun q' : Prop => @lem7171690 p q p' q'). Qed.
Lemma lem7171692 (p : Prop) (q : Prop) : term329 p q.
Proof. exact (fun p' : Prop => @lem7171691 p q p'). Qed.
Lemma lem7171693 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term361 A v u f.
Proof. exact (@lem7171692 (term362 A v u) ((@sum A v f) = (term306 A v u f))). Qed.
Lemma lem7171694 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (p' : Prop) : term363 A v u f p'.
Proof. exact (@lem7171693 A v u f p'). Qed.
Lemma lem7171695 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (p' : Prop) : (term363 A v u f p') = (term364 A v u f p').
Proof. exact (eq_refl (term363 A v u f p')). Qed.
Lemma lem7171696 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (p' : Prop) : term364 A v u f p'.
Proof. exact (EQ_MP (@lem7171695 A v u f p') (@lem7171694 A v u f p')). Qed.
Lemma lem7171697 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term365 A v u f p' q'.
Proof. exact (@lem7171696 A v u f p' q'). Qed.
Lemma lem7171698 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term365 A v u f p' q') = (term366 A v u f p' q').
Proof. exact (eq_refl (term365 A v u f p' q')). Qed.
Lemma lem7171699 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term366 A v u f p' q'.
Proof. exact (EQ_MP (@lem7171698 A v u f p' q') (@lem7171697 A v u f p' q')). Qed.
Lemma lem7171703 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term341 A s t.
Proof. exact (fun h0 : term320 A s t => @lem7171503 A s t h0). Qed.
Lemma lem7171704 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term341 A s t.
Proof. exact (@lem7171703 A s t). Qed.
Lemma lem7171705 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term341 A u v.
Proof. exact (@lem7171704 A u v). Qed.
Lemma lem7171709 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : (@FINITE A u) = True.
Proof. exact (EQ_MP (@lem7171524 A u) (@lem7171414 A u h1)). Qed.
Lemma lem7171710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7171711 {A : Type'} (u : A -> Prop) (h1 : @FINITE A u) : (term342 A u) = (or True).
Proof. exact (MK_COMB (@lem7171710) (@lem7171709 A u h1)). Qed.
Lemma lem7171713 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : (@FINITE A v) = True.
Proof. exact (EQ_MP (@lem7171526 A v) (@lem7171416 A v h1)). Qed.
Lemma lem7171714 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term320 A u v) = (True \/ True).
Proof. exact (MK_COMB (@lem7171711 A u h1) (@lem7171713 A v h2)). Qed.
Lemma lem7171716 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem7171717 : (True \/ True) = True.
Proof. exact (@lem7171716 True). Qed.
Lemma lem7171718 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term320 A u v) = True.
Proof. exact (TRANS (@lem7171714 A u v h1 h2) (@lem7171717)). Qed.
Lemma lem7171719 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : True = (term320 A u v).
Proof. exact (SYM (@lem7171718 A u v h1 h2)). Qed.
Lemma lem7171720 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term320 A u v.
Proof. exact (EQ_MP (@lem7171719 A u v h1 h2) (@lem0)). Qed.
Lemma lem7171721 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term321 A u v) = True.
Proof. exact (@lem7171705 A u v (@lem7171720 A u v h1 h2)). Qed.
Lemma lem7171722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7171723 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term343 A u v) = (and True).
Proof. exact (MK_COMB (@lem7171722) (@lem7171721 A u v h1 h2)). Qed.
Lemma lem7171727 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term344 _97970 s t.
Proof. exact (fun h0 : @FINITE _97970 s => @lem7171518 _97970 t s h0). Qed.
Lemma lem7171728 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term344 A s t.
Proof. exact (@lem7171727 A s t). Qed.
Lemma lem7171729 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term344 A v u.
Proof. exact (@lem7171728 A v u). Qed.
Lemma lem7171731 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : (@FINITE A v) = True.
Proof. exact (EQ_MP (@lem7171526 A v) (@lem7171416 A v h1)). Qed.
Lemma lem7171732 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : True = (@FINITE A v).
Proof. exact (SYM (@lem7171731 A v h1)). Qed.
Lemma lem7171733 {A : Type'} (v : A -> Prop) (h1 : @FINITE A v) : @FINITE A v.
Proof. exact (EQ_MP (@lem7171732 A v h1) (@lem0)). Qed.
Lemma lem7171734 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) : (term326 A v u) = True.
Proof. exact (@lem7171729 A v u (@lem7171733 A v h1)). Qed.
Lemma lem7171735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7171736 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) : (term345 A v u) = (and True).
Proof. exact (MK_COMB (@lem7171735) (@lem7171734 A u v h1)). Qed.
Lemma lem7171737 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term367 A v u) = (term367 A v u).
Proof. exact (eq_refl (term367 A v u)). Qed.
Lemma lem7171738 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) : (term368 A v u) = (term369 A v u).
Proof. exact (MK_COMB (@lem7171736 A u v h1) (@lem7171737 A v u)). Qed.
Lemma lem7171740 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7171741 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term369 A v u) = (term367 A v u).
Proof. exact (@lem7171740 (term367 A v u)). Qed.
Lemma lem7171742 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A v) : (term368 A v u) = (term367 A v u).
Proof. exact (TRANS (@lem7171738 A u v h1) (@lem7171741 A v u)). Qed.
Lemma lem7171743 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term362 A v u) = (term369 A v u).
Proof. exact (MK_COMB (@lem7171723 A u v h1 h2) (@lem7171742 A u v h2)). Qed.
Lemma lem7171745 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7171746 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term369 A v u) = (term367 A v u).
Proof. exact (@lem7171745 (term367 A v u)). Qed.
Lemma lem7171747 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term362 A v u) = (term367 A v u).
Proof. exact (TRANS (@lem7171743 A u v h1 h2) (@lem7171746 A v u)). Qed.
Lemma lem7171748 {A : Type'} (f : A -> real) (v : A -> Prop) (u : A -> Prop) (q' : Prop) : term370 A f v u q'.
Proof. exact (@lem7171699 A v u f (term367 A v u) q'). Qed.
Lemma lem7171749 {A : Type'} (f : A -> real) (q' : Prop) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term371 A f v u q'.
Proof. exact (@lem7171748 A f v u q' (@lem7171747 A u v h1 h2)). Qed.
Lemma lem7171755 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((@sum A v f) = (term306 A v u f)) = ((@sum A v f) = (term306 A v u f)).
Proof. exact (eq_refl ((@sum A v f) = (term306 A v u f))). Qed.
Lemma lem7171756 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term372 A v u f.
Proof. exact (fun h0 : term367 A v u => @lem7171755 A v u f). Qed.
Lemma lem7171757 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term373 A v u f.
Proof. exact (@lem7171749 A f ((@sum A v f) = (term306 A v u f)) u v h1 h2). Qed.
Lemma lem7171758 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term308 A v u f) = (term374 A v u f).
Proof. exact (@lem7171757 A f u v h1 h2 (@lem7171756 A v u f)). Qed.
Lemma lem7171786 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (q' : Prop) : term375 A v u f q'.
Proof. exact (@lem7171686 A u v f (term374 A v u f) q'). Qed.
Lemma lem7171787 {A : Type'} (f : A -> real) (q' : Prop) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term376 A v u f q'.
Proof. exact (@lem7171786 A v u f q' (@lem7171758 A f u v h1 h2)). Qed.
Lemma lem7171804 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term311 A u v f) = (term311 A u v f).
Proof. exact (eq_refl (term311 A u v f)). Qed.
Lemma lem7171805 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term377 A u v f.
Proof. exact (fun h0 : term374 A v u f => @lem7171804 A u v f). Qed.
Lemma lem7171806 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term378 A u v f.
Proof. exact (@lem7171787 A f (term311 A u v f) u v h1 h2). Qed.
Lemma lem7171807 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term313 A u v f) = (term379 A u v f).
Proof. exact (@lem7171806 A f u v h1 h2 (@lem7171805 A u v f)). Qed.
Lemma lem7171902 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term380 A u v f.
Proof. exact (fun h0 : term353 A u v f => @lem7171807 A f u v h1 h2). Qed.
Lemma lem7171903 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : term381 A u v f.
Proof. exact (@lem7171665 A f (term379 A u v f) u v h1 h2). Qed.
Lemma lem7171904 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term315 A u v f) = (term382 A u v f).
Proof. exact (@lem7171903 A f u v h1 h2 (@lem7171902 A f u v h1 h2)). Qed.
Lemma lem7172167 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : @FINITE A u) (h2 : @FINITE A v) : (term382 A u v f) = (term315 A u v f).
Proof. exact (SYM (@lem7171904 A f u v h1 h2)). Qed.
Lemma lem7172169 (p : Prop) (q : Prop) (r : Prop) : term383 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem7172170 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term384 A u v f.
Proof. exact (@lem7172169 (term346 A u v) ((@sum A u f) = (term298 A u v f)) (term379 A u v f)). Qed.
Lemma lem7172172 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem7172173 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem7172172 A s t). Qed.
Lemma lem7172174 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term346 A u v) = ((term385 A u v) = (@EMPTY A)).
Proof. exact (@lem7172173 A (@INTER A u v) (@DIFF A u v)). Qed.
Lemma lem7172178 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term172 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7172179 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term172 A s t).
Proof. exact (@lem7172178 A s t). Qed.
Lemma lem7172180 {A : Type'} (u : A -> Prop) (v : A -> Prop) : ((term385 A u v) = (@EMPTY A)) = (term386 A u v).
Proof. exact (@lem7172179 A (term385 A u v) (@EMPTY A)). Qed.
Lemma lem7172185 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term346 A u v) = (term386 A u v).
Proof. exact (TRANS (@lem7172174 A u v) (@lem7172180 A u v)). Qed.
Lemma lem7172190 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term386 A u v) = (term346 A u v).
Proof. exact (SYM (@lem7172185 A u v)). Qed.
Lemma lem7172198 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term179 A x s t) = (term180 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem7172199 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term179 A x s t) = (term180 A s x t).
Proof. exact (@lem7172198 A s x t). Qed.
Lemma lem7172200 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) : (term387 A x u v) = (term388 A x u v).
Proof. exact (@lem7172199 A (@INTER A u v) x (@DIFF A u v)). Qed.
Lemma lem7172204 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term179 A x s t) = (term180 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem7172205 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term179 A x s t) = (term180 A s x t).
Proof. exact (@lem7172204 A s x t). Qed.
Lemma lem7172206 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term179 A x u v) = (term180 A u x v).
Proof. exact (@lem7172205 A u x v). Qed.
Lemma lem7172210 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7172211 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7172210 A P x). Qed.
Lemma lem7172212 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem7172211 A u x). Qed.
Lemma lem7172213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7172214 {A : Type'} (u : A -> Prop) (x : A) : (term181 A x u) = (term182 A u x).
Proof. exact (MK_COMB (@lem7172213) (@lem7172212 A u x)). Qed.
Lemma lem7172216 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7172217 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7172216 A P x). Qed.
Lemma lem7172218 {A : Type'} (v : A -> Prop) (x : A) : (@IN A x v) = (v x).
Proof. exact (@lem7172217 A v x). Qed.
Lemma lem7172219 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term180 A u x v) = (term183 A u v x).
Proof. exact (MK_COMB (@lem7172214 A u x) (@lem7172218 A v x)). Qed.
Lemma lem7172222 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term179 A x u v) = (term183 A u v x).
Proof. exact (TRANS (@lem7172206 A u x v) (@lem7172219 A u v x)). Qed.
Lemma lem7172223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7172224 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term389 A x u v) = (term390 A u v x).
Proof. exact (MK_COMB (@lem7172223) (@lem7172222 A u v x)). Qed.
Lemma lem7172226 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term186 A x s t) = (term187 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem7172227 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term186 A x s t) = (term187 A s x t).
Proof. exact (@lem7172226 A s x t). Qed.
Lemma lem7172228 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term186 A x u v) = (term187 A u x v).
Proof. exact (@lem7172227 A u x v). Qed.
Lemma lem7172232 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7172233 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7172232 A P x). Qed.
Lemma lem7172234 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem7172233 A u x). Qed.
Lemma lem7172235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7172236 {A : Type'} (u : A -> Prop) (x : A) : (term181 A x u) = (term182 A u x).
Proof. exact (MK_COMB (@lem7172235) (@lem7172234 A u x)). Qed.
Lemma lem7172238 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7172239 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7172238 A P x). Qed.
Lemma lem7172240 {A : Type'} (v : A -> Prop) (x : A) : (@IN A x v) = (v x).
Proof. exact (@lem7172239 A v x). Qed.
Lemma lem7172241 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7172242 {A : Type'} (v : A -> Prop) (x : A) : (term188 A x v) = (term189 A v x).
Proof. exact (MK_COMB (@lem7172241) (@lem7172240 A v x)). Qed.
Lemma lem7172243 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term187 A u x v) = (term190 A u v x).
Proof. exact (MK_COMB (@lem7172236 A u x) (@lem7172242 A v x)). Qed.
Lemma lem7172246 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term186 A x u v) = (term190 A u v x).
Proof. exact (TRANS (@lem7172228 A u x v) (@lem7172243 A u v x)). Qed.
Lemma lem7172247 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term388 A x u v) = (term391 A u v x).
Proof. exact (MK_COMB (@lem7172224 A u v x) (@lem7172246 A u v x)). Qed.
Lemma lem7172250 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term387 A x u v) = (term391 A u v x).
Proof. exact (TRANS (@lem7172200 A x u v) (@lem7172247 A u v x)). Qed.
Lemma lem7172251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7172252 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term392 A x u v) = (term393 A u v x).
Proof. exact (MK_COMB (@lem7172251) (@lem7172250 A u v x)). Qed.
Lemma lem7172254 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem7172255 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7172254 A x). Qed.
Lemma lem7172256 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : ((term387 A x u v) = (@IN A x (@EMPTY A))) = ((term391 A u v x) = False).
Proof. exact (MK_COMB (@lem7172252 A u v x) (@lem7172255 A x)). Qed.
Lemma lem7172258 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem7172259 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : ((term391 A u v x) = False) = (term394 A u v x).
Proof. exact (@lem7172258 (term391 A u v x)). Qed.
Lemma lem7172266 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : ((term387 A x u v) = (@IN A x (@EMPTY A))) = (term394 A u v x).
Proof. exact (TRANS (@lem7172256 A u v x) (@lem7172259 A u v x)). Qed.
Lemma lem7172267 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term395 A u v) = (term396 A u v).
Proof. exact (fun_ext (fun x : A => @lem7172266 A u v x)). Qed.
Lemma lem7172268 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7172269 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term386 A u v) = (term397 A u v).
Proof. exact (MK_COMB (@lem7172268 A) (@lem7172267 A u v)). Qed.
Lemma lem7172274 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term397 A u v) = (term386 A u v).
Proof. exact (SYM (@lem7172269 A u v)). Qed.
Lemma lem7172276 (p : Prop) : p = (term197 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7172277 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term397 A u v) = (term398 A u v).
Proof. exact (@lem7172276 (term397 A u v)). Qed.
Lemma lem7172278 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term398 A u v) = (term397 A u v).
Proof. exact (SYM (@lem7172277 A u v)). Qed.
Lemma lem7172279 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term399 A u v) : term399 A u v.
Proof. exact (h1). Qed.
Lemma lem7172282 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term398 A u v) : term398 A u v.
Proof. exact (h1). Qed.
Lemma lem7172283 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term400 A u v.
Proof. exact (fun h0 : term398 A u v => @lem7172282 A u v h0). Qed.
Lemma lem7172284 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term400 A u v) : term400 A u v.
Proof. exact (h1). Qed.
Lemma lem7172285 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term398 A u v) : term398 A u v.
Proof. exact (h1). Qed.
Lemma lem7172286 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term398 A u v) (h2 : term400 A u v) : term398 A u v.
Proof. exact (@lem7172284 A u v h2 (@lem7172285 A u v h1)). Qed.
Lemma lem7172287 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term398 A u v) : term401 A u v.
Proof. exact (fun h0 : term400 A u v => @lem7172286 A u v h1 h0). Qed.
Lemma lem7172288 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term400 A u v) : term400 A u v.
Proof. exact (h1). Qed.
Lemma lem7172289 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term398 A u v) (h2 : term400 A u v) : term398 A u v.
Proof. exact (@lem7172287 A u v h1 (@lem7172288 A u v h2)). Qed.
Lemma lem7172290 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term400 A u v) : term400 A u v.
Proof. exact (fun h0 : term398 A u v => @lem7172289 A u v h0 h1). Qed.
Lemma lem7172291 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term402 A u v.
Proof. exact (fun h0 : term400 A u v => @lem7172290 A u v h0). Qed.
Lemma lem7172294 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term400 A u v.
Proof. exact (@lem7172291 A u v (@lem7172283 A u v)). Qed.
Lemma lem7172295 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term400 A u v.
Proof. exact (@lem7172294 A u v). Qed.
Lemma lem7172305 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7172306 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term398 A u v) = (term403 A u v).
Proof. exact (@lem7172305 (term399 A u v)). Qed.
Lemma lem7172308 (t : Prop) : (term204 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7172309 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term403 A u v) = (term397 A u v).
Proof. exact (@lem7172308 (term397 A u v)). Qed.
Lemma lem7172314 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term398 A u v) = (term397 A u v).
Proof. exact (TRANS (@lem7172306 A u v) (@lem7172309 A u v)). Qed.
Lemma lem7172321 {A : Type'} (v : A -> Prop) : (term404 A v) = (term405 A v).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7172314 A u v)). Qed.
Lemma lem7172322 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7172323 {A : Type'} (v : A -> Prop) : (term406 A v) = (term407 A v).
Proof. exact (MK_COMB (@lem7172322 A) (@lem7172321 A v)). Qed.
Lemma lem7172328 {A : Type'} : (term408 A) = (term409 A).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7172323 A v)). Qed.
Lemma lem7172329 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7172338 {A : Type'} : (term410 A) = (term411 A).
Proof. exact (MK_COMB (@lem7172329 A) (@lem7172328 A)). Qed.
Lemma lem7172355 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term394 A u v x) = (term394 A u v x).
Proof. exact (eq_refl (term394 A u v x)). Qed.
Lemma lem7172356 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term396 A u v) = (term396 A u v).
Proof. exact (fun_ext (fun x : A => @lem7172355 A u v x)). Qed.
Lemma lem7172357 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7172358 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term397 A u v) = (term397 A u v).
Proof. exact (MK_COMB (@lem7172357 A) (@lem7172356 A u v)). Qed.
Lemma lem7172359 {A : Type'} (v : A -> Prop) : (term405 A v) = (term405 A v).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7172358 A u v)). Qed.
Lemma lem7172360 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7172361 {A : Type'} (v : A -> Prop) : (term407 A v) = (term407 A v).
Proof. exact (MK_COMB (@lem7172360 A) (@lem7172359 A v)). Qed.
Lemma lem7172362 {A : Type'} : (term409 A) = (term409 A).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7172361 A v)). Qed.
Lemma lem7172363 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7172364 {A : Type'} : (term411 A) = (term411 A).
Proof. exact (MK_COMB (@lem7172363 A) (@lem7172362 A)). Qed.
Lemma lem7172391 {A : Type'} : (term410 A) = (term411 A).
Proof. exact (TRANS (@lem7172338 A) (@lem7172364 A)). Qed.
Lemma lem7172392 {A : Type'} : (term411 A) = (term410 A).
Proof. exact (SYM (@lem7172391 A)). Qed.
Lemma lem7172411 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : term391 A u v x.
Proof. exact (h1). Qed.
Lemma lem7172435 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : term391 A u v x.
Proof. exact (h1). Qed.
Lemma lem7172436 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : term190 A u v x.
Proof. exact (proj2 (@lem7172435 A u v x h1)). Qed.
Lemma lem7172437 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : term183 A u v x.
Proof. exact (proj1 (@lem7172435 A u v x h1)). Qed.
Lemma lem7172461 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : term189 A v x.
Proof. exact (proj2 (@lem7172436 A u v x h1)). Qed.
Lemma lem7172467 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : v x.
Proof. exact (proj2 (@lem7172437 A u v x h1)). Qed.
Lemma lem7172468 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : term235 A v x.
Proof. exact (fun h0 : term189 A v x => @lem7172467 A u v x h1). Qed.
Lemma lem7172470 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7172471 {A : Type'} (v : A -> Prop) (x : A) : (term235 A v x) = (v x).
Proof. exact (@lem7172470 (v x)). Qed.
Lemma lem7172472 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : v x.
Proof. exact (EQ_MP (@lem7172471 A v x) (@lem7172468 A u v x h1)). Qed.
Lemma lem7172475 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7172477 {A : Type'} (v : A -> Prop) (x : A) : (term189 A v x) = (term237 A v x).
Proof. exact (@lem7172475 (v x)). Qed.
Lemma lem7172480 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : term237 A v x.
Proof. exact (EQ_MP (@lem7172477 A v x) (@lem7172461 A u v x h1)). Qed.
Lemma lem7172483 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : False.
Proof. exact (@lem7172480 A u v x h1 (@lem7172472 A u v x h1)). Qed.
Lemma lem7172484 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : term238.
Proof. exact (fun h0 : ~ False => @lem7172483 A u v x h1). Qed.
Lemma lem7172486 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7172487 : term238 = False.
Proof. exact (@lem7172486 False). Qed.
Lemma lem7172488 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : False.
Proof. exact (EQ_MP (@lem7172487) (@lem7172484 A u v x h1)). Qed.
Lemma lem7172489 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : (term391 A u v x) = False.
Proof. exact (prop_ext (fun h2 : term391 A u v x => @lem7172488 A u v x h1) (fun h2 : False => @lem7172435 A u v x h1)). Qed.
Lemma lem7172490 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : False.
Proof. exact (EQ_MP (@lem7172489 A u v x h1) (@lem7172435 A u v x h1)). Qed.
Lemma lem7172491 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : (term391 A u v x) = False.
Proof. exact (prop_ext (fun h2 : term391 A u v x => @lem7172490 A u v x h1) (fun h2 : False => @lem7172411 A u v x h1)). Qed.
Lemma lem7172492 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) (h1 : term391 A u v x) : False.
Proof. exact (EQ_MP (@lem7172491 A u v x h1) (@lem7172411 A u v x h1)). Qed.
Lemma lem7172493 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : term412 A u v x.
Proof. exact (fun h0 : term391 A u v x => @lem7172492 A u v x h0). Qed.
Lemma lem7172494 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term412 A u v x) = (term394 A u v x).
Proof. exact (@lem69 (term391 A u v x)). Qed.
Lemma lem7172495 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : term394 A u v x.
Proof. exact (EQ_MP (@lem7172494 A u v x) (@lem7172493 A u v x)). Qed.
Lemma lem7172500 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term397 A u v.
Proof. exact (fun x : A => @lem7172495 A u v x). Qed.
Lemma lem7172505 {A : Type'} (v : A -> Prop) : term407 A v.
Proof. exact (fun u : A -> Prop => @lem7172500 A u v). Qed.
Lemma lem7172510 {A : Type'} : term411 A.
Proof. exact (fun v : A -> Prop => @lem7172505 A v). Qed.
Lemma lem7172511 {A : Type'} : term410 A.
Proof. exact (EQ_MP (@lem7172392 A) (@lem7172510 A)). Qed.
Lemma lem7172512 {A : Type'} (v : A -> Prop) : term413 A v.
Proof. exact (@lem7172511 A v). Qed.
Lemma lem7172513 {A : Type'} (v : A -> Prop) : (term413 A v) = (term406 A v).
Proof. exact (eq_refl (term413 A v)). Qed.
Lemma lem7172514 {A : Type'} (v : A -> Prop) : term406 A v.
Proof. exact (EQ_MP (@lem7172513 A v) (@lem7172512 A v)). Qed.
Lemma lem7172515 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term414 A v u.
Proof. exact (@lem7172514 A v u). Qed.
Lemma lem7172516 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term414 A v u) = (term398 A u v).
Proof. exact (eq_refl (term414 A v u)). Qed.
Lemma lem7172517 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term398 A u v.
Proof. exact (EQ_MP (@lem7172516 A u v) (@lem7172515 A v u)). Qed.
Lemma lem7172519 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term398 A u v.
Proof. exact (@lem7172295 A u v (@lem7172517 A u v)). Qed.
Lemma lem7172520 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term399 A u v) : False.
Proof. exact (@lem7172519 A u v (@lem7172279 A u v h1)). Qed.
Lemma lem7172521 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term399 A u v) : (term399 A u v) = False.
Proof. exact (prop_ext (fun h2 : term399 A u v => @lem7172520 A u v h1) (fun h2 : False => @lem7172279 A u v h1)). Qed.
Lemma lem7172522 {A : Type'} (u : A -> Prop) (v : A -> Prop) (h1 : term399 A u v) : False.
Proof. exact (EQ_MP (@lem7172521 A u v h1) (@lem7172279 A u v h1)). Qed.
Lemma lem7172523 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term398 A u v.
Proof. exact (fun h0 : term399 A u v => @lem7172522 A u v h0). Qed.
Lemma lem7172524 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term397 A u v.
Proof. exact (EQ_MP (@lem7172278 A u v) (@lem7172523 A u v)). Qed.
Lemma lem7172525 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term386 A u v.
Proof. exact (EQ_MP (@lem7172274 A u v) (@lem7172524 A u v)). Qed.
Lemma lem7172526 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term346 A u v.
Proof. exact (EQ_MP (@lem7172190 A u v) (@lem7172525 A u v)). Qed.
Lemma lem7172527 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : (@sum A u f) = (term298 A u v f)) : (@sum A u f) = (term298 A u v f).
Proof. exact (h1). Qed.
Lemma lem7172528 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term415 A u v f) = (term415 A u v f).
Proof. exact (eq_refl (term415 A u v f)). Qed.
Lemma lem7172529 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : (@sum A u f) = (term298 A u v f)) : (term416 A v u f) = (term417 A u v f).
Proof. exact (MK_COMB (@lem7172528 A u v f) (@lem7172527 A u v f h1)). Qed.
Lemma lem7172530 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term417 A u v f) = (term418 A u v f).
Proof. exact (eq_refl (term417 A u v f)). Qed.
Lemma lem7172531 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term419 A v u f) = (term419 A v u f).
Proof. exact (eq_refl (term419 A v u f)). Qed.
Lemma lem7172532 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : ((term416 A v u f) = (term417 A u v f)) = ((term416 A v u f) = (term418 A u v f)).
Proof. exact (MK_COMB (@lem7172531 A v u f) (@lem7172530 A u v f)). Qed.
Lemma lem7172533 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term416 A v u f) = (term379 A u v f).
Proof. exact (eq_refl (term416 A v u f)). Qed.
Lemma lem7172534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7172535 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term419 A v u f) = (term420 A u v f).
Proof. exact (MK_COMB (@lem7172534) (@lem7172533 A u v f)). Qed.
Lemma lem7172536 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term418 A u v f) = (term418 A u v f).
Proof. exact (eq_refl (term418 A u v f)). Qed.
Lemma lem7172537 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : ((term416 A v u f) = (term418 A u v f)) = ((term379 A u v f) = (term418 A u v f)).
Proof. exact (MK_COMB (@lem7172535 A u v f) (@lem7172536 A u v f)). Qed.
Lemma lem7172538 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : ((term416 A v u f) = (term417 A u v f)) = ((term379 A u v f) = (term418 A u v f)).
Proof. exact (TRANS (@lem7172532 A u v f) (@lem7172537 A u v f)). Qed.
Lemma lem7172539 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : (@sum A u f) = (term298 A u v f)) : (term379 A u v f) = (term418 A u v f).
Proof. exact (EQ_MP (@lem7172538 A u v f) (@lem7172529 A u v f h1)). Qed.
Lemma lem7172540 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : (@sum A u f) = (term298 A u v f)) : (term418 A u v f) = (term379 A u v f).
Proof. exact (SYM (@lem7172539 A u v f h1)). Qed.
Lemma lem7172542 (p : Prop) (q : Prop) (r : Prop) : term383 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem7172543 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term421 A u v f.
Proof. exact (@lem7172542 (term367 A v u) ((@sum A v f) = (term306 A v u f)) (term422 A u v f)). Qed.
Lemma lem7172545 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem7172546 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem7172545 A s t). Qed.
Lemma lem7172547 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term367 A v u) = ((term423 A v u) = (@EMPTY A)).
Proof. exact (@lem7172546 A (@INTER A u v) (@DIFF A v u)). Qed.
Lemma lem7172551 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term172 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem7172552 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term172 A s t).
Proof. exact (@lem7172551 A s t). Qed.
Lemma lem7172553 {A : Type'} (v : A -> Prop) (u : A -> Prop) : ((term423 A v u) = (@EMPTY A)) = (term424 A v u).
Proof. exact (@lem7172552 A (term423 A v u) (@EMPTY A)). Qed.
Lemma lem7172558 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term367 A v u) = (term424 A v u).
Proof. exact (TRANS (@lem7172547 A v u) (@lem7172553 A v u)). Qed.
Lemma lem7172563 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term424 A v u) = (term367 A v u).
Proof. exact (SYM (@lem7172558 A v u)). Qed.
Lemma lem7172571 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term179 A x s t) = (term180 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem7172572 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term179 A x s t) = (term180 A s x t).
Proof. exact (@lem7172571 A s x t). Qed.
Lemma lem7172573 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) : (term425 A x v u) = (term426 A x v u).
Proof. exact (@lem7172572 A (@INTER A u v) x (@DIFF A v u)). Qed.
Lemma lem7172577 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term179 A x s t) = (term180 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem7172578 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term179 A x s t) = (term180 A s x t).
Proof. exact (@lem7172577 A s x t). Qed.
Lemma lem7172579 {A : Type'} (u : A -> Prop) (x : A) (v : A -> Prop) : (term179 A x u v) = (term180 A u x v).
Proof. exact (@lem7172578 A u x v). Qed.
Lemma lem7172583 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7172584 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7172583 A P x). Qed.
Lemma lem7172585 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem7172584 A u x). Qed.
Lemma lem7172586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7172587 {A : Type'} (u : A -> Prop) (x : A) : (term181 A x u) = (term182 A u x).
Proof. exact (MK_COMB (@lem7172586) (@lem7172585 A u x)). Qed.
Lemma lem7172589 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7172590 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7172589 A P x). Qed.
Lemma lem7172591 {A : Type'} (v : A -> Prop) (x : A) : (@IN A x v) = (v x).
Proof. exact (@lem7172590 A v x). Qed.
Lemma lem7172592 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term180 A u x v) = (term183 A u v x).
Proof. exact (MK_COMB (@lem7172587 A u x) (@lem7172591 A v x)). Qed.
Lemma lem7172595 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term179 A x u v) = (term183 A u v x).
Proof. exact (TRANS (@lem7172579 A u x v) (@lem7172592 A u v x)). Qed.
Lemma lem7172596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7172597 {A : Type'} (u : A -> Prop) (v : A -> Prop) (x : A) : (term389 A x u v) = (term390 A u v x).
Proof. exact (MK_COMB (@lem7172596) (@lem7172595 A u v x)). Qed.
Lemma lem7172599 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term186 A x s t) = (term187 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem7172600 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term186 A x s t) = (term187 A s x t).
Proof. exact (@lem7172599 A s x t). Qed.
Lemma lem7172601 {A : Type'} (v : A -> Prop) (x : A) (u : A -> Prop) : (term186 A x v u) = (term187 A v x u).
Proof. exact (@lem7172600 A v x u). Qed.
Lemma lem7172605 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7172606 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7172605 A P x). Qed.
Lemma lem7172607 {A : Type'} (v : A -> Prop) (x : A) : (@IN A x v) = (v x).
Proof. exact (@lem7172606 A v x). Qed.
Lemma lem7172608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7172609 {A : Type'} (v : A -> Prop) (x : A) : (term181 A x v) = (term182 A v x).
Proof. exact (MK_COMB (@lem7172608) (@lem7172607 A v x)). Qed.
Lemma lem7172611 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7172612 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7172611 A P x). Qed.
Lemma lem7172613 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem7172612 A u x). Qed.
Lemma lem7172614 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7172615 {A : Type'} (u : A -> Prop) (x : A) : (term188 A x u) = (term189 A u x).
Proof. exact (MK_COMB (@lem7172614) (@lem7172613 A u x)). Qed.
Lemma lem7172616 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term187 A v x u) = (term190 A v u x).
Proof. exact (MK_COMB (@lem7172609 A v x) (@lem7172615 A u x)). Qed.
Lemma lem7172619 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term186 A x v u) = (term190 A v u x).
Proof. exact (TRANS (@lem7172601 A v x u) (@lem7172616 A v u x)). Qed.
Lemma lem7172620 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term426 A x v u) = (term427 A v u x).
Proof. exact (MK_COMB (@lem7172597 A u v x) (@lem7172619 A v u x)). Qed.
Lemma lem7172623 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term425 A x v u) = (term427 A v u x).
Proof. exact (TRANS (@lem7172573 A x v u) (@lem7172620 A v u x)). Qed.
Lemma lem7172624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7172625 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term428 A x v u) = (term429 A v u x).
Proof. exact (MK_COMB (@lem7172624) (@lem7172623 A v u x)). Qed.
Lemma lem7172627 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem7172628 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7172627 A x). Qed.
Lemma lem7172629 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : ((term425 A x v u) = (@IN A x (@EMPTY A))) = ((term427 A v u x) = False).
Proof. exact (MK_COMB (@lem7172625 A v u x) (@lem7172628 A x)). Qed.
Lemma lem7172631 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem7172632 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : ((term427 A v u x) = False) = (term430 A v u x).
Proof. exact (@lem7172631 (term427 A v u x)). Qed.
Lemma lem7172639 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : ((term425 A x v u) = (@IN A x (@EMPTY A))) = (term430 A v u x).
Proof. exact (TRANS (@lem7172629 A v u x) (@lem7172632 A v u x)). Qed.
Lemma lem7172640 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term431 A v u) = (term432 A v u).
Proof. exact (fun_ext (fun x : A => @lem7172639 A v u x)). Qed.
Lemma lem7172641 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7172642 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term424 A v u) = (term433 A v u).
Proof. exact (MK_COMB (@lem7172641 A) (@lem7172640 A v u)). Qed.
Lemma lem7172647 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term433 A v u) = (term424 A v u).
Proof. exact (SYM (@lem7172642 A v u)). Qed.
Lemma lem7172649 (p : Prop) : p = (term197 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7172650 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term433 A v u) = (term434 A v u).
Proof. exact (@lem7172649 (term433 A v u)). Qed.
Lemma lem7172651 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term434 A v u) = (term433 A v u).
Proof. exact (SYM (@lem7172650 A v u)). Qed.
Lemma lem7172652 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term435 A v u) : term435 A v u.
Proof. exact (h1). Qed.
Lemma lem7172655 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term434 A v u) : term434 A v u.
Proof. exact (h1). Qed.
Lemma lem7172656 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term436 A v u.
Proof. exact (fun h0 : term434 A v u => @lem7172655 A v u h0). Qed.
Lemma lem7172657 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term436 A v u) : term436 A v u.
Proof. exact (h1). Qed.
Lemma lem7172658 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term434 A v u) : term434 A v u.
Proof. exact (h1). Qed.
Lemma lem7172659 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term434 A v u) (h2 : term436 A v u) : term434 A v u.
Proof. exact (@lem7172657 A v u h2 (@lem7172658 A v u h1)). Qed.
Lemma lem7172660 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term434 A v u) : term437 A v u.
Proof. exact (fun h0 : term436 A v u => @lem7172659 A v u h1 h0). Qed.
Lemma lem7172661 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term436 A v u) : term436 A v u.
Proof. exact (h1). Qed.
Lemma lem7172662 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term434 A v u) (h2 : term436 A v u) : term434 A v u.
Proof. exact (@lem7172660 A v u h1 (@lem7172661 A v u h2)). Qed.
Lemma lem7172663 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term436 A v u) : term436 A v u.
Proof. exact (fun h0 : term434 A v u => @lem7172662 A v u h0 h1). Qed.
Lemma lem7172664 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term438 A v u.
Proof. exact (fun h0 : term436 A v u => @lem7172663 A v u h0). Qed.
Lemma lem7172667 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term436 A v u.
Proof. exact (@lem7172664 A v u (@lem7172656 A v u)). Qed.
Lemma lem7172668 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term436 A v u.
Proof. exact (@lem7172667 A v u). Qed.
Lemma lem7172678 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7172679 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term434 A v u) = (term439 A v u).
Proof. exact (@lem7172678 (term435 A v u)). Qed.
Lemma lem7172681 (t : Prop) : (term204 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7172682 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term439 A v u) = (term433 A v u).
Proof. exact (@lem7172681 (term433 A v u)). Qed.
Lemma lem7172687 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term434 A v u) = (term433 A v u).
Proof. exact (TRANS (@lem7172679 A v u) (@lem7172682 A v u)). Qed.
Lemma lem7172694 {A : Type'} (u : A -> Prop) : (term440 A u) = (term441 A u).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7172687 A v u)). Qed.
Lemma lem7172695 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7172696 {A : Type'} (u : A -> Prop) : (term442 A u) = (term443 A u).
Proof. exact (MK_COMB (@lem7172695 A) (@lem7172694 A u)). Qed.
Lemma lem7172701 {A : Type'} : (term444 A) = (term445 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7172696 A u)). Qed.
Lemma lem7172702 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7172711 {A : Type'} : (term446 A) = (term447 A).
Proof. exact (MK_COMB (@lem7172702 A) (@lem7172701 A)). Qed.
Lemma lem7172728 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term430 A v u x) = (term430 A v u x).
Proof. exact (eq_refl (term430 A v u x)). Qed.
Lemma lem7172729 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term432 A v u) = (term432 A v u).
Proof. exact (fun_ext (fun x : A => @lem7172728 A v u x)). Qed.
Lemma lem7172730 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7172731 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term433 A v u) = (term433 A v u).
Proof. exact (MK_COMB (@lem7172730 A) (@lem7172729 A v u)). Qed.
Lemma lem7172732 {A : Type'} (u : A -> Prop) : (term441 A u) = (term441 A u).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7172731 A v u)). Qed.
Lemma lem7172733 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7172734 {A : Type'} (u : A -> Prop) : (term443 A u) = (term443 A u).
Proof. exact (MK_COMB (@lem7172733 A) (@lem7172732 A u)). Qed.
Lemma lem7172735 {A : Type'} : (term445 A) = (term445 A).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7172734 A u)). Qed.
Lemma lem7172736 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7172737 {A : Type'} : (term447 A) = (term447 A).
Proof. exact (MK_COMB (@lem7172736 A) (@lem7172735 A)). Qed.
Lemma lem7172764 {A : Type'} : (term446 A) = (term447 A).
Proof. exact (TRANS (@lem7172711 A) (@lem7172737 A)). Qed.
Lemma lem7172765 {A : Type'} : (term447 A) = (term446 A).
Proof. exact (SYM (@lem7172764 A)). Qed.
Lemma lem7172784 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : term427 A v u x.
Proof. exact (h1). Qed.
Lemma lem7172808 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : term427 A v u x.
Proof. exact (h1). Qed.
Lemma lem7172809 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : term190 A v u x.
Proof. exact (proj2 (@lem7172808 A v u x h1)). Qed.
Lemma lem7172810 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : term183 A u v x.
Proof. exact (proj1 (@lem7172808 A v u x h1)). Qed.
Lemma lem7172834 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : term189 A u x.
Proof. exact (proj2 (@lem7172809 A v u x h1)). Qed.
Lemma lem7172840 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : u x.
Proof. exact (proj1 (@lem7172810 A v u x h1)). Qed.
Lemma lem7172841 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : term235 A u x.
Proof. exact (fun h0 : term189 A u x => @lem7172840 A v u x h1). Qed.
Lemma lem7172843 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7172844 {A : Type'} (u : A -> Prop) (x : A) : (term235 A u x) = (u x).
Proof. exact (@lem7172843 (u x)). Qed.
Lemma lem7172845 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : u x.
Proof. exact (EQ_MP (@lem7172844 A u x) (@lem7172841 A v u x h1)). Qed.
Lemma lem7172848 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7172850 {A : Type'} (u : A -> Prop) (x : A) : (term189 A u x) = (term237 A u x).
Proof. exact (@lem7172848 (u x)). Qed.
Lemma lem7172853 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : term237 A u x.
Proof. exact (EQ_MP (@lem7172850 A u x) (@lem7172834 A v u x h1)). Qed.
Lemma lem7172856 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : False.
Proof. exact (@lem7172853 A v u x h1 (@lem7172845 A v u x h1)). Qed.
Lemma lem7172857 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : term238.
Proof. exact (fun h0 : ~ False => @lem7172856 A v u x h1). Qed.
Lemma lem7172859 (p : Prop) : (term236 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7172860 : term238 = False.
Proof. exact (@lem7172859 False). Qed.
Lemma lem7172861 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : False.
Proof. exact (EQ_MP (@lem7172860) (@lem7172857 A v u x h1)). Qed.
Lemma lem7172862 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : (term427 A v u x) = False.
Proof. exact (prop_ext (fun h2 : term427 A v u x => @lem7172861 A v u x h1) (fun h2 : False => @lem7172808 A v u x h1)). Qed.
Lemma lem7172863 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : False.
Proof. exact (EQ_MP (@lem7172862 A v u x h1) (@lem7172808 A v u x h1)). Qed.
Lemma lem7172864 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : (term427 A v u x) = False.
Proof. exact (prop_ext (fun h2 : term427 A v u x => @lem7172863 A v u x h1) (fun h2 : False => @lem7172784 A v u x h1)). Qed.
Lemma lem7172865 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) (h1 : term427 A v u x) : False.
Proof. exact (EQ_MP (@lem7172864 A v u x h1) (@lem7172784 A v u x h1)). Qed.
Lemma lem7172866 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : term448 A v u x.
Proof. exact (fun h0 : term427 A v u x => @lem7172865 A v u x h0). Qed.
Lemma lem7172867 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : (term448 A v u x) = (term430 A v u x).
Proof. exact (@lem69 (term427 A v u x)). Qed.
Lemma lem7172868 {A : Type'} (v : A -> Prop) (u : A -> Prop) (x : A) : term430 A v u x.
Proof. exact (EQ_MP (@lem7172867 A v u x) (@lem7172866 A v u x)). Qed.
Lemma lem7172873 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term433 A v u.
Proof. exact (fun x : A => @lem7172868 A v u x). Qed.
Lemma lem7172878 {A : Type'} (u : A -> Prop) : term443 A u.
Proof. exact (fun v : A -> Prop => @lem7172873 A v u). Qed.
Lemma lem7172883 {A : Type'} : term447 A.
Proof. exact (fun u : A -> Prop => @lem7172878 A u). Qed.
Lemma lem7172884 {A : Type'} : term446 A.
Proof. exact (EQ_MP (@lem7172765 A) (@lem7172883 A)). Qed.
Lemma lem7172885 {A : Type'} (u : A -> Prop) : term449 A u.
Proof. exact (@lem7172884 A u). Qed.
Lemma lem7172886 {A : Type'} (u : A -> Prop) : (term449 A u) = (term442 A u).
Proof. exact (eq_refl (term449 A u)). Qed.
Lemma lem7172887 {A : Type'} (u : A -> Prop) : term442 A u.
Proof. exact (EQ_MP (@lem7172886 A u) (@lem7172885 A u)). Qed.
Lemma lem7172888 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term450 A u v.
Proof. exact (@lem7172887 A u v). Qed.
Lemma lem7172889 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term450 A u v) = (term434 A v u).
Proof. exact (eq_refl (term450 A u v)). Qed.
Lemma lem7172890 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term434 A v u.
Proof. exact (EQ_MP (@lem7172889 A v u) (@lem7172888 A u v)). Qed.
Lemma lem7172892 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term434 A v u.
Proof. exact (@lem7172668 A v u (@lem7172890 A v u)). Qed.
Lemma lem7172893 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term435 A v u) : False.
Proof. exact (@lem7172892 A v u (@lem7172652 A v u h1)). Qed.
Lemma lem7172894 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term435 A v u) : (term435 A v u) = False.
Proof. exact (prop_ext (fun h2 : term435 A v u => @lem7172893 A v u h1) (fun h2 : False => @lem7172652 A v u h1)). Qed.
Lemma lem7172895 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term435 A v u) : False.
Proof. exact (EQ_MP (@lem7172894 A v u h1) (@lem7172652 A v u h1)). Qed.
Lemma lem7172896 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term434 A v u.
Proof. exact (fun h0 : term435 A v u => @lem7172895 A v u h0). Qed.
Lemma lem7172897 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term433 A v u.
Proof. exact (EQ_MP (@lem7172651 A v u) (@lem7172896 A v u)). Qed.
Lemma lem7172898 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term424 A v u.
Proof. exact (EQ_MP (@lem7172647 A v u) (@lem7172897 A v u)). Qed.
Lemma lem7172899 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term367 A v u.
Proof. exact (EQ_MP (@lem7172563 A v u) (@lem7172898 A v u)). Qed.
Lemma lem7172900 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : (@sum A v f) = (term306 A v u f)) : (@sum A v f) = (term306 A v u f).
Proof. exact (h1). Qed.
Lemma lem7172901 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term451 A u v f) = (term451 A u v f).
Proof. exact (eq_refl (term451 A u v f)). Qed.
Lemma lem7172902 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : (@sum A v f) = (term306 A v u f)) : (term452 A u v f) = (term453 A v u f).
Proof. exact (MK_COMB (@lem7172901 A u v f) (@lem7172900 A v u f h1)). Qed.
Lemma lem7172903 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term453 A v u f) = (term454 A v u f).
Proof. exact (eq_refl (term453 A v u f)). Qed.
Lemma lem7172904 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term455 A u v f) = (term455 A u v f).
Proof. exact (eq_refl (term455 A u v f)). Qed.
Lemma lem7172905 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term452 A u v f) = (term453 A v u f)) = ((term452 A u v f) = (term454 A v u f)).
Proof. exact (MK_COMB (@lem7172904 A u v f) (@lem7172903 A v u f)). Qed.
Lemma lem7172906 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term452 A u v f) = (term422 A u v f).
Proof. exact (eq_refl (term452 A u v f)). Qed.
Lemma lem7172907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7172908 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term455 A u v f) = (term456 A u v f).
Proof. exact (MK_COMB (@lem7172907) (@lem7172906 A u v f)). Qed.
Lemma lem7172909 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term454 A v u f) = (term454 A v u f).
Proof. exact (eq_refl (term454 A v u f)). Qed.
Lemma lem7172910 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term452 A u v f) = (term454 A v u f)) = ((term422 A u v f) = (term454 A v u f)).
Proof. exact (MK_COMB (@lem7172908 A u v f) (@lem7172909 A v u f)). Qed.
Lemma lem7172911 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term452 A u v f) = (term453 A v u f)) = ((term422 A u v f) = (term454 A v u f)).
Proof. exact (TRANS (@lem7172905 A v u f) (@lem7172910 A v u f)). Qed.
Lemma lem7172912 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : (@sum A v f) = (term306 A v u f)) : (term422 A u v f) = (term454 A v u f).
Proof. exact (EQ_MP (@lem7172911 A v u f) (@lem7172902 A v u f h1)). Qed.
Lemma lem7172913 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : (@sum A v f) = (term306 A v u f)) : (term454 A v u f) = (term422 A u v f).
Proof. exact (SYM (@lem7172912 A v u f h1)). Qed.
Lemma lem7172917 (x : real) (a : real) (y : real) : term169 x a y.
Proof. exact (@lem7170015 x a y (@lem7170007 x a y)). Qed.
Lemma lem7172918 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term457 A v u f.
Proof. exact (@lem7172917 (term458 A u v f) (term459 A u v f) (term458 A v u f)). Qed.
Lemma lem7172934 {_132004 : Type'} (f : _132004 -> real) : term460 _132004 f.
Proof. exact (@lem7169087 _132004 f). Qed.
Lemma lem7172935 {_132004 : Type'} (f : _132004 -> real) : (term460 _132004 f) = (term12 _132004 f).
Proof. exact (eq_refl (term460 _132004 f)). Qed.
Lemma lem7172936 {_132004 : Type'} (f : _132004 -> real) : term12 _132004 f.
Proof. exact (EQ_MP (@lem7172935 _132004 f) (@lem7172934 _132004 f)). Qed.
Lemma lem7172937 {_132004 : Type'} (f : _132004 -> real) (s : _132004 -> Prop) : term461 _132004 f s.
Proof. exact (@lem7172936 _132004 f s). Qed.
Lemma lem7172938 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term461 _132004 f s) = ((term8 _132004 s f) = (term7 _132004 s f)).
Proof. exact (eq_refl (term461 _132004 f s)). Qed.
Lemma lem7172971 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term8 _132004 s f) = (term7 _132004 s f).
Proof. exact (EQ_MP (@lem7172938 _132004 s f) (@lem7172937 _132004 f s)). Qed.
Lemma lem7172972 {A : Type'} (s : A -> Prop) (f : A -> real) : (term8 A s f) = (term7 A s f).
Proof. exact (@lem7172971 A s f). Qed.
Lemma lem7172973 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term462 A u v f) = (term463 A u v f).
Proof. exact (@lem7172972 A (@DIFF A u v) f). Qed.
Lemma lem7172974 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem7172975 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term465 A u v f) = (term466 A u v f).
Proof. exact (MK_COMB (@lem7172974) (@lem7172973 A u v f)). Qed.
Lemma lem7172976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7172977 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : (term467 A u v f) = (term468 A u v f).
Proof. exact (MK_COMB (@lem7172976) (@lem7172975 A u v f)). Qed.
Lemma lem7172978 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term469 A v u f) = (term469 A v u f).
Proof. exact (eq_refl (term469 A v u f)). Qed.
Lemma lem7172979 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term470 A v u f) = (term471 A v u f).
Proof. exact (MK_COMB (@lem7172977 A u v f) (@lem7172978 A v u f)). Qed.
Lemma lem7172982 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term471 A v u f) = (term470 A v u f).
Proof. exact (SYM (@lem7172979 A v u f)). Qed.
Lemma lem7172984 {A : Type'} (s : A -> Prop) (f : A -> real) : term2 A s f.
Proof. exact (EQ_MP (@lem7169072 A s f) (@lem7169071 A f s)). Qed.
Lemma lem7172985 {A : Type'} (s : A -> Prop) (f : A -> real) : term2 A s f.
Proof. exact (@lem7172984 A s f). Qed.
Lemma lem7172986 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term472 A u v f.
Proof. exact (@lem7172985 A (@DIFF A u v) (term473 A f)). Qed.
Lemma lem7172988 {A : Type'} (s : A -> Prop) (f : A -> real) : term2 A s f.
Proof. exact (EQ_MP (@lem7169072 A s f) (@lem7169071 A f s)). Qed.
Lemma lem7172989 {A : Type'} (s : A -> Prop) (f : A -> real) : term2 A s f.
Proof. exact (@lem7172988 A s f). Qed.
Lemma lem7172990 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term474 A v u f.
Proof. exact (@lem7172989 A (@DIFF A v u) f). Qed.
Lemma lem7172991 (x : real) : term475 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem7172992 (x : real) : (term475 x) = ((term476 x) = x).
Proof. exact (eq_refl (term475 x)). Qed.
Lemma lem7172994 (x : real) : term477 x.
Proof. exact (@lem1362465 x). Qed.
Lemma lem7172995 (x : real) : (term477 x) = (term478 x).
Proof. exact (eq_refl (term477 x)). Qed.
Lemma lem7172996 (x : real) : term478 x.
Proof. exact (EQ_MP (@lem7172995 x) (@lem7172994 x)). Qed.
Lemma lem7172997 (x : real) (y : real) : term479 x y.
Proof. exact (@lem7172996 x y). Qed.
Lemma lem7172998 (x : real) (y : real) : (term479 x y) = ((term480 x y) = (term481 x y)).
Proof. exact (eq_refl (term479 x y)). Qed.
Lemma lem7173019 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : term482 A u v f x.
Proof. exact (@lem7171418 A u v f h1 x). Qed.
Lemma lem7173020 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : (term482 A u v f x) = (term483 A u v f x).
Proof. exact (eq_refl (term482 A u v f x)). Qed.
Lemma lem7173021 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : term483 A u v f x.
Proof. exact (EQ_MP (@lem7173020 A u v f x) (@lem7173019 A x u v f h1)). Qed.
Lemma lem7173022 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term186 A x u v) : term186 A x u v.
Proof. exact (h1). Qed.
Lemma lem7173023 {A : Type'} (f : A -> real) (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term186 A x u v) : term484 A f x.
Proof. exact (@lem7173021 A x u v f h1 (@lem7173022 A x u v h2)). Qed.
Lemma lem7173024 {A : Type'} (f : A -> real) (x : A) : (term484 A f x) = ((term484 A f x) = True).
Proof. exact (@lem7 (term484 A f x)). Qed.
Lemma lem7173025 {A : Type'} (f : A -> real) (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term186 A x u v) : (term484 A f x) = True.
Proof. exact (EQ_MP (@lem7173024 A f x) (@lem7173023 A f x u v h1 h2)). Qed.
Lemma lem7173050 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term327 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7173051 (p : Prop) (q : Prop) (p' : Prop) : term328 p q p'.
Proof. exact (fun q' : Prop => @lem7173050 p q p' q'). Qed.
Lemma lem7173052 (p : Prop) (q : Prop) : term329 p q.
Proof. exact (fun p' : Prop => @lem7173051 p q p'). Qed.
Lemma lem7173053 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) : term485 A u v f x.
Proof. exact (@lem7173052 (term186 A x u v) (term486 A f x)). Qed.
Lemma lem7173054 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : term487 A u v f x p'.
Proof. exact (@lem7173053 A u v f x p'). Qed.
Lemma lem7173055 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : (term487 A u v f x p') = (term488 A u v f x p').
Proof. exact (eq_refl (term487 A u v f x p')). Qed.
Lemma lem7173056 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : term488 A u v f x p'.
Proof. exact (EQ_MP (@lem7173055 A u v f x p') (@lem7173054 A u v f x p')). Qed.
Lemma lem7173057 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term489 A u v f x p' q'.
Proof. exact (@lem7173056 A u v f x p' q'). Qed.
Lemma lem7173058 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term489 A u v f x p' q') = (term490 A u v f x p' q').
Proof. exact (eq_refl (term489 A u v f x p' q')). Qed.
Lemma lem7173059 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term490 A u v f x p' q'.
Proof. exact (EQ_MP (@lem7173058 A u v f x p' q') (@lem7173057 A u v f x p' q')). Qed.
Lemma lem7173060 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) : (term186 A x u v) = (term186 A x u v).
Proof. exact (eq_refl (term186 A x u v)). Qed.
Lemma lem7173061 {A : Type'} (f : A -> real) (x : A) (u : A -> Prop) (v : A -> Prop) (q' : Prop) : term491 A f x u v q'.
Proof. exact (@lem7173059 A u v f x (term186 A x u v) q'). Qed.
Lemma lem7173062 {A : Type'} (f : A -> real) (x : A) (u : A -> Prop) (v : A -> Prop) (q' : Prop) : term492 A f x u v q'.
Proof. exact (@lem7173061 A f x u v q' (@lem7173060 A x u v)). Qed.
Lemma lem7173063 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term186 A x u v) : term186 A x u v.
Proof. exact (h1). Qed.
Lemma lem7173064 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) : (term186 A x u v) = ((term186 A x u v) = True).
Proof. exact (@lem7 (term186 A x u v)). Qed.
Lemma lem7173067 {A B : Type'} (f : A -> B) (y : A) : (term493 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7173068 {A : Type'} (f : A -> real) (y : A) : (term494 A f y) = (f y).
Proof. exact (@lem7173067 A real f y). Qed.
Lemma lem7173069 {A : Type'} (f : A -> real) (x : A) : (term495 A f x) = (term496 A f x).
Proof. exact (@lem7173068 A (term473 A f) x). Qed.
Lemma lem7173070 {A : Type'} (f : A -> real) (x : A) : (term496 A f x) = (term497 A f x).
Proof. exact (eq_refl (term496 A f x)). Qed.
Lemma lem7173071 {A : Type'} (f : A -> real) : (term498 A f) = (term473 A f).
Proof. exact (fun_ext (fun x : A => @lem7173070 A f x)). Qed.
Lemma lem7173072 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7173073 {A : Type'} (f : A -> real) (x : A) : (term495 A f x) = (term496 A f x).
Proof. exact (MK_COMB (@lem7173071 A f) (@lem7173072 A x)). Qed.
Lemma lem7173074 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7173075 {A : Type'} (f : A -> real) (x : A) : (term499 A f x) = (term500 A f x).
Proof. exact (MK_COMB (@lem7173074) (@lem7173073 A f x)). Qed.
Lemma lem7173076 {A : Type'} (f : A -> real) (x : A) : (term496 A f x) = (term497 A f x).
Proof. exact (eq_refl (term496 A f x)). Qed.
Lemma lem7173077 {A : Type'} (f : A -> real) (x : A) : ((term495 A f x) = (term496 A f x)) = ((term496 A f x) = (term497 A f x)).
Proof. exact (MK_COMB (@lem7173075 A f x) (@lem7173076 A f x)). Qed.
Lemma lem7173078 {A : Type'} (f : A -> real) (x : A) : (term496 A f x) = (term497 A f x).
Proof. exact (EQ_MP (@lem7173077 A f x) (@lem7173069 A f x)). Qed.
Lemma lem7173079 : term464 = term464.
Proof. exact (eq_refl term464). Qed.
Lemma lem7173080 {A : Type'} (f : A -> real) (x : A) : (term486 A f x) = (term501 A f x).
Proof. exact (MK_COMB (@lem7173079) (@lem7173078 A f x)). Qed.
Lemma lem7173082 (x : real) (y : real) : (term480 x y) = (term481 x y).
Proof. exact (EQ_MP (@lem7172998 x y) (@lem7172997 x y)). Qed.
Lemma lem7173083 {A : Type'} (f : A -> real) (x : A) : (term501 A f x) = (term502 A f x).
Proof. exact (@lem7173082 term23 (f x)). Qed.
Lemma lem7173085 (x : real) : (term476 x) = x.
Proof. exact (EQ_MP (@lem7172992 x) (@lem7172991 x)). Qed.
Lemma lem7173086 {A : Type'} (f : A -> real) (x : A) : (term503 A f x) = (f x).
Proof. exact (@lem7173085 (f x)). Qed.
Lemma lem7173087 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7173088 {A : Type'} (f : A -> real) (x : A) : (term504 A f x) = (term505 A f x).
Proof. exact (MK_COMB (@lem7173087) (@lem7173086 A f x)). Qed.
Lemma lem7173089 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem7173090 {A : Type'} (f : A -> real) (x : A) : (term502 A f x) = (term484 A f x).
Proof. exact (MK_COMB (@lem7173088 A f x) (@lem7173089)). Qed.
Lemma lem7173092 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : term506 A u v f x.
Proof. exact (fun h0 : term186 A x u v => @lem7173025 A f x u v h1 h0). Qed.
Lemma lem7173093 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : term506 A u v f x.
Proof. exact (@lem7173092 A x u v f h1). Qed.
Lemma lem7173095 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term186 A x u v) : (term186 A x u v) = True.
Proof. exact (EQ_MP (@lem7173064 A x u v) (@lem7173063 A x u v h1)). Qed.
Lemma lem7173096 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term186 A x u v) : True = (term186 A x u v).
Proof. exact (SYM (@lem7173095 A x u v h1)). Qed.
Lemma lem7173097 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term186 A x u v) : term186 A x u v.
Proof. exact (EQ_MP (@lem7173096 A x u v h1) (@lem0)). Qed.
Lemma lem7173098 {A : Type'} (f : A -> real) (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term186 A x u v) : (term484 A f x) = True.
Proof. exact (@lem7173093 A x u v f h1 (@lem7173097 A x u v h2)). Qed.
Lemma lem7173099 {A : Type'} (f : A -> real) (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term186 A x u v) : (term502 A f x) = True.
Proof. exact (TRANS (@lem7173090 A f x) (@lem7173098 A f x u v h1 h2)). Qed.
Lemma lem7173100 {A : Type'} (f : A -> real) (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term186 A x u v) : (term501 A f x) = True.
Proof. exact (TRANS (@lem7173083 A f x) (@lem7173099 A f x u v h1 h2)). Qed.
Lemma lem7173101 {A : Type'} (f : A -> real) (x : A) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term186 A x u v) : (term486 A f x) = True.
Proof. exact (TRANS (@lem7173080 A f x) (@lem7173100 A f x u v h1 h2)). Qed.
Lemma lem7173102 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : term507 A u v f x.
Proof. exact (fun h0 : term186 A x u v => @lem7173101 A f x u v h1 h0). Qed.
Lemma lem7173103 {A : Type'} (f : A -> real) (x : A) (u : A -> Prop) (v : A -> Prop) : term508 A f x u v.
Proof. exact (@lem7173062 A f x u v True). Qed.
Lemma lem7173104 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : (term509 A u v f x) = (term510 A x u v).
Proof. exact (@lem7173103 A f x u v (@lem7173102 A x u v f h1)). Qed.
Lemma lem7173106 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7173107 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) : (term510 A x u v) = True.
Proof. exact (@lem7173106 (term186 A x u v)). Qed.
Lemma lem7173108 {A : Type'} (x : A) (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : (term509 A u v f x) = True.
Proof. exact (TRANS (@lem7173104 A x u v f h1) (@lem7173107 A x u v)). Qed.
Lemma lem7173109 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : (term511 A u v f) = (term512 A).
Proof. exact (fun_ext (fun x : A => @lem7173108 A x u v f h1)). Qed.
Lemma lem7173110 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7173111 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : (term513 A u v f) = (term514 A).
Proof. exact (MK_COMB (@lem7173110 A) (@lem7173109 A u v f h1)). Qed.
Lemma lem7173113 {A : Type'} (t : Prop) : (term515 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7173114 {A : Type'} (t : Prop) : (term515 A t) = t.
Proof. exact (@lem7173113 A t). Qed.
Lemma lem7173115 {A : Type'} : (term514 A) = True.
Proof. exact (@lem7173114 A True). Qed.
Lemma lem7173116 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : (term513 A u v f) = True.
Proof. exact (TRANS (@lem7173111 A u v f h1) (@lem7173115 A)). Qed.
Lemma lem7173117 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : True = (term513 A u v f).
Proof. exact (SYM (@lem7173116 A u v f h1)). Qed.
Lemma lem7173118 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : term513 A u v f.
Proof. exact (EQ_MP (@lem7173117 A u v f h1) (@lem0)). Qed.
Lemma lem7173159 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : term516 A v u f x.
Proof. exact (@lem7171417 A v u f h1 x). Qed.
Lemma lem7173160 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term516 A v u f x) = (term517 A v u f x).
Proof. exact (eq_refl (term516 A v u f x)). Qed.
Lemma lem7173161 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : term517 A v u f x.
Proof. exact (EQ_MP (@lem7173160 A v u f x) (@lem7173159 A x v u f h1)). Qed.
Lemma lem7173162 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (h1 : term186 A x v u) : term186 A x v u.
Proof. exact (h1). Qed.
Lemma lem7173163 {A : Type'} (f : A -> real) (x : A) (v : A -> Prop) (u : A -> Prop) (h1 : term288 A v u f) (h2 : term186 A x v u) : term518 A f x.
Proof. exact (@lem7173161 A x v u f h1 (@lem7173162 A x v u h2)). Qed.
Lemma lem7173164 {A : Type'} (f : A -> real) (x : A) : (term518 A f x) = ((term518 A f x) = True).
Proof. exact (@lem7 (term518 A f x)). Qed.
Lemma lem7173165 {A : Type'} (f : A -> real) (x : A) (v : A -> Prop) (u : A -> Prop) (h1 : term288 A v u f) (h2 : term186 A x v u) : (term518 A f x) = True.
Proof. exact (EQ_MP (@lem7173164 A f x) (@lem7173163 A f x v u h1 h2)). Qed.
Lemma lem7173178 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term327 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7173179 (p : Prop) (q : Prop) (p' : Prop) : term328 p q p'.
Proof. exact (fun q' : Prop => @lem7173178 p q p' q'). Qed.
Lemma lem7173180 (p : Prop) (q : Prop) : term329 p q.
Proof. exact (fun p' : Prop => @lem7173179 p q p'). Qed.
Lemma lem7173181 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : term519 A v u f x.
Proof. exact (@lem7173180 (term186 A x v u) (term518 A f x)). Qed.
Lemma lem7173182 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : term520 A v u f x p'.
Proof. exact (@lem7173181 A v u f x p'). Qed.
Lemma lem7173183 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : (term520 A v u f x p') = (term521 A v u f x p').
Proof. exact (eq_refl (term520 A v u f x p')). Qed.
Lemma lem7173184 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : term521 A v u f x p'.
Proof. exact (EQ_MP (@lem7173183 A v u f x p') (@lem7173182 A v u f x p')). Qed.
Lemma lem7173185 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term522 A v u f x p' q'.
Proof. exact (@lem7173184 A v u f x p' q'). Qed.
Lemma lem7173186 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term522 A v u f x p' q') = (term523 A v u f x p' q').
Proof. exact (eq_refl (term522 A v u f x p' q')). Qed.
Lemma lem7173187 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term523 A v u f x p' q'.
Proof. exact (EQ_MP (@lem7173186 A v u f x p' q') (@lem7173185 A v u f x p' q')). Qed.
Lemma lem7173188 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) : (term186 A x v u) = (term186 A x v u).
Proof. exact (eq_refl (term186 A x v u)). Qed.
Lemma lem7173189 {A : Type'} (f : A -> real) (x : A) (v : A -> Prop) (u : A -> Prop) (q' : Prop) : term524 A f x v u q'.
Proof. exact (@lem7173187 A v u f x (term186 A x v u) q'). Qed.
Lemma lem7173190 {A : Type'} (f : A -> real) (x : A) (v : A -> Prop) (u : A -> Prop) (q' : Prop) : term525 A f x v u q'.
Proof. exact (@lem7173189 A f x v u q' (@lem7173188 A x v u)). Qed.
Lemma lem7173191 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (h1 : term186 A x v u) : term186 A x v u.
Proof. exact (h1). Qed.
Lemma lem7173192 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) : (term186 A x v u) = ((term186 A x v u) = True).
Proof. exact (@lem7 (term186 A x v u)). Qed.
Lemma lem7173195 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : term526 A v u f x.
Proof. exact (fun h0 : term186 A x v u => @lem7173165 A f x v u h1 h0). Qed.
Lemma lem7173196 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : term526 A v u f x.
Proof. exact (@lem7173195 A x v u f h1). Qed.
Lemma lem7173198 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (h1 : term186 A x v u) : (term186 A x v u) = True.
Proof. exact (EQ_MP (@lem7173192 A x v u) (@lem7173191 A x v u h1)). Qed.
Lemma lem7173199 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (h1 : term186 A x v u) : True = (term186 A x v u).
Proof. exact (SYM (@lem7173198 A x v u h1)). Qed.
Lemma lem7173200 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (h1 : term186 A x v u) : term186 A x v u.
Proof. exact (EQ_MP (@lem7173199 A x v u h1) (@lem0)). Qed.
Lemma lem7173201 {A : Type'} (f : A -> real) (x : A) (v : A -> Prop) (u : A -> Prop) (h1 : term288 A v u f) (h2 : term186 A x v u) : (term518 A f x) = True.
Proof. exact (@lem7173196 A x v u f h1 (@lem7173200 A x v u h2)). Qed.
Lemma lem7173202 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : term526 A v u f x.
Proof. exact (fun h0 : term186 A x v u => @lem7173201 A f x v u h1 h0). Qed.
Lemma lem7173203 {A : Type'} (f : A -> real) (x : A) (v : A -> Prop) (u : A -> Prop) : term527 A f x v u.
Proof. exact (@lem7173190 A f x v u True). Qed.
Lemma lem7173204 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : (term517 A v u f x) = (term510 A x v u).
Proof. exact (@lem7173203 A f x v u (@lem7173202 A x v u f h1)). Qed.
Lemma lem7173206 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7173207 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) : (term510 A x v u) = True.
Proof. exact (@lem7173206 (term186 A x v u)). Qed.
Lemma lem7173208 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : (term517 A v u f x) = True.
Proof. exact (TRANS (@lem7173204 A x v u f h1) (@lem7173207 A x v u)). Qed.
Lemma lem7173209 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : (term528 A v u f) = (term512 A).
Proof. exact (fun_ext (fun x : A => @lem7173208 A x v u f h1)). Qed.
Lemma lem7173210 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7173211 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : (term288 A v u f) = (term514 A).
Proof. exact (MK_COMB (@lem7173210 A) (@lem7173209 A v u f h1)). Qed.
Lemma lem7173213 {A : Type'} (t : Prop) : (term515 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7173214 {A : Type'} (t : Prop) : (term515 A t) = t.
Proof. exact (@lem7173213 A t). Qed.
Lemma lem7173215 {A : Type'} : (term514 A) = True.
Proof. exact (@lem7173214 A True). Qed.
Lemma lem7173216 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : (term288 A v u f) = True.
Proof. exact (TRANS (@lem7173211 A v u f h1) (@lem7173215 A)). Qed.
Lemma lem7173217 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : True = (term288 A v u f).
Proof. exact (SYM (@lem7173216 A v u f h1)). Qed.
Lemma lem7173218 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : term288 A v u f.
Proof. exact (EQ_MP (@lem7173217 A v u f h1) (@lem0)). Qed.
Lemma lem7173219 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term288 A v u f) : term469 A v u f.
Proof. exact (@lem7172990 A v u f (@lem7173218 A v u f h1)). Qed.
Lemma lem7173220 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) : term466 A u v f.
Proof. exact (@lem7172986 A u v f (@lem7173118 A u v f h1)). Qed.
Lemma lem7173221 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : term288 A v u f) : term471 A v u f.
Proof. exact (conj (@lem7173220 A u v f h1) (@lem7173219 A v u f h2)). Qed.
Lemma lem7173222 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : term288 A v u f) : term470 A v u f.
Proof. exact (EQ_MP (@lem7172982 A v u f) (@lem7173221 A v u f h1 h2)). Qed.
Lemma lem7173223 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : term288 A v u f) : term454 A v u f.
Proof. exact (@lem7172918 A v u f (@lem7173222 A v u f h1 h2)). Qed.
Lemma lem7173224 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : term288 A v u f) (h3 : (@sum A v f) = (term306 A v u f)) : term422 A u v f.
Proof. exact (EQ_MP (@lem7172913 A v u f h3) (@lem7173223 A v u f h1 h2)). Qed.
Lemma lem7173225 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : term288 A v u f) : term529 A u v f.
Proof. exact (fun h0 : (@sum A v f) = (term306 A v u f) => @lem7173224 A v u f h1 h2 h0). Qed.
Lemma lem7173226 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : term288 A v u f) : term530 A u v f.
Proof. exact (conj (@lem7172899 A v u) (@lem7173225 A v u f h1 h2)). Qed.
Lemma lem7173227 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : term288 A v u f) : term418 A u v f.
Proof. exact (@lem7172543 A u v f (@lem7173226 A v u f h1 h2)). Qed.
Lemma lem7173228 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : term288 A v u f) (h3 : (@sum A u f) = (term298 A u v f)) : term379 A u v f.
Proof. exact (EQ_MP (@lem7172540 A u v f h3) (@lem7173227 A v u f h1 h2)). Qed.
Lemma lem7173229 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : term288 A v u f) : term531 A u v f.
Proof. exact (fun h0 : (@sum A u f) = (term298 A u v f) => @lem7173228 A u v f h1 h2 h0). Qed.
Lemma lem7173230 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : term288 A v u f) : term532 A u v f.
Proof. exact (conj (@lem7172526 A u v) (@lem7173229 A v u f h1 h2)). Qed.
Lemma lem7173231 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : term288 A v u f) : term382 A u v f.
Proof. exact (@lem7172170 A u v f (@lem7173230 A v u f h1 h2)). Qed.
Lemma lem7173232 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term288 A v u f) (h3 : @FINITE A u) (h4 : @FINITE A v) : term315 A u v f.
Proof. exact (EQ_MP (@lem7172167 A f u v h3 h4) (@lem7173231 A v u f h1 h2)). Qed.
Lemma lem7173233 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term288 A v u f) (h3 : @FINITE A u) (h4 : @FINITE A v) : term314 A u v f.
Proof. exact (EQ_MP (@lem7171493 A u v f) (@lem7173232 A f u v h1 h2 h3 h4)). Qed.
Lemma lem7173234 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term288 A v u f) (h3 : term284 A u v f) (h4 : @FINITE A u) (h5 : @FINITE A v) : term312 A u v f.
Proof. exact (@lem7173233 A f u v h1 h2 h4 h5 (@lem7171422 A u v f h3)). Qed.
Lemma lem7173235 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term288 A v u f) (h3 : term284 A u v f) (h4 : @FINITE A u) (h5 : @FINITE A v) : term311 A u v f.
Proof. exact (@lem7173234 A f u v h1 h2 h3 h4 h5 (@lem7171425 A u v f h3)). Qed.
Lemma lem7173236 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term288 A v u f) (h3 : @FINITE A u) (h4 : @FINITE A v) : term533 A u v f.
Proof. exact (fun h0 : term284 A u v f => @lem7173235 A f u v h1 h2 h0 h3 h4). Qed.
Lemma lem7173237 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term288 A v u f) (h3 : @FINITE A u) (h4 : @FINITE A v) : term311 A u v f.
Proof. exact (@lem7173236 A f u v h1 h2 h3 h4 (@lem7171411 A u v f)). Qed.
Lemma lem7173238 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term285 A v u f) : term286 A v u f.
Proof. exact (proj2 (@lem7171412 A v u f h1)). Qed.
Lemma lem7173239 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term285 A v u f) : @FINITE A u.
Proof. exact (proj1 (@lem7171412 A v u f h1)). Qed.
Lemma lem7173240 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term286 A v u f) : term287 A v u f.
Proof. exact (proj2 (@lem7171413 A v u f h1)). Qed.
Lemma lem7173241 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term286 A v u f) : @FINITE A v.
Proof. exact (proj1 (@lem7171413 A v u f h1)). Qed.
Lemma lem7173242 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term287 A v u f) : term288 A v u f.
Proof. exact (proj2 (@lem7171415 A v u f h1)). Qed.
Lemma lem7173243 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term287 A v u f) : term289 A u v f.
Proof. exact (proj1 (@lem7171415 A v u f h1)). Qed.
Lemma lem7173244 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term288 A v u f) (h3 : @FINITE A u) (h4 : @FINITE A v) : (term288 A v u f) = (term311 A u v f).
Proof. exact (prop_ext (fun h5 : term288 A v u f => @lem7173237 A f u v h1 h2 h3 h4) (fun h5 : term311 A u v f => @lem7171417 A v u f h2)). Qed.
Lemma lem7173245 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term288 A v u f) (h3 : @FINITE A u) (h4 : @FINITE A v) : term311 A u v f.
Proof. exact (EQ_MP (@lem7173244 A f u v h1 h2 h3 h4) (@lem7171417 A v u f h2)). Qed.
Lemma lem7173246 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term288 A v u f) (h3 : @FINITE A u) (h4 : @FINITE A v) : (term289 A u v f) = (term311 A u v f).
Proof. exact (prop_ext (fun h5 : term289 A u v f => @lem7173245 A f u v h1 h2 h3 h4) (fun h5 : term311 A u v f => @lem7171418 A u v f h1)). Qed.
Lemma lem7173247 {A : Type'} (f : A -> real) (u : A -> Prop) (v : A -> Prop) (h1 : term289 A u v f) (h2 : term288 A v u f) (h3 : @FINITE A u) (h4 : @FINITE A v) : term311 A u v f.
Proof. exact (EQ_MP (@lem7173246 A f u v h1 h2 h3 h4) (@lem7171418 A u v f h1)). Qed.
Lemma lem7173248 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : @FINITE A u) (h3 : @FINITE A v) (h4 : term287 A v u f) : (term288 A v u f) = (term311 A u v f).
Proof. exact (prop_ext (fun h5 : term288 A v u f => @lem7173247 A f u v h1 h5 h2 h3) (fun h5 : term311 A u v f => @lem7173242 A v u f h4)). Qed.
Lemma lem7173249 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term289 A u v f) (h2 : @FINITE A u) (h3 : @FINITE A v) (h4 : term287 A v u f) : term311 A u v f.
Proof. exact (EQ_MP (@lem7173248 A v u f h1 h2 h3 h4) (@lem7173242 A v u f h4)). Qed.
Lemma lem7173250 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : @FINITE A v) (h3 : term287 A v u f) : (term289 A u v f) = (term311 A u v f).
Proof. exact (prop_ext (fun h4 : term289 A u v f => @lem7173249 A v u f h4 h1 h2 h3) (fun h4 : term311 A u v f => @lem7173243 A v u f h3)). Qed.
Lemma lem7173251 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : @FINITE A v) (h3 : term287 A v u f) : term311 A u v f.
Proof. exact (EQ_MP (@lem7173250 A v u f h1 h2 h3) (@lem7173243 A v u f h3)). Qed.
Lemma lem7173252 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : @FINITE A v) (h3 : term287 A v u f) : (@FINITE A v) = (term311 A u v f).
Proof. exact (prop_ext (fun h4 : @FINITE A v => @lem7173251 A v u f h1 h2 h3) (fun h4 : term311 A u v f => @lem7171416 A v h2)). Qed.
Lemma lem7173253 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : @FINITE A v) (h3 : term287 A v u f) : term311 A u v f.
Proof. exact (EQ_MP (@lem7173252 A v u f h1 h2 h3) (@lem7171416 A v h2)). Qed.
Lemma lem7173254 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : @FINITE A v) (h3 : term286 A v u f) : (term287 A v u f) = (term311 A u v f).
Proof. exact (prop_ext (fun h4 : term287 A v u f => @lem7173253 A v u f h1 h2 h4) (fun h4 : term311 A u v f => @lem7173240 A v u f h3)). Qed.
Lemma lem7173255 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : @FINITE A v) (h3 : term286 A v u f) : term311 A u v f.
Proof. exact (EQ_MP (@lem7173254 A v u f h1 h2 h3) (@lem7173240 A v u f h3)). Qed.
Lemma lem7173256 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : term286 A v u f) : (@FINITE A v) = (term311 A u v f).
Proof. exact (prop_ext (fun h3 : @FINITE A v => @lem7173255 A v u f h1 h3 h2) (fun h3 : term311 A u v f => @lem7173241 A v u f h2)). Qed.
Lemma lem7173257 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : term286 A v u f) : term311 A u v f.
Proof. exact (EQ_MP (@lem7173256 A v u f h1 h2) (@lem7173241 A v u f h2)). Qed.
Lemma lem7173258 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : term286 A v u f) : (@FINITE A u) = (term311 A u v f).
Proof. exact (prop_ext (fun h3 : @FINITE A u => @lem7173257 A v u f h1 h2) (fun h3 : term311 A u v f => @lem7171414 A u h1)). Qed.
Lemma lem7173259 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : term286 A v u f) : term311 A u v f.
Proof. exact (EQ_MP (@lem7173258 A v u f h1 h2) (@lem7171414 A u h1)). Qed.
Lemma lem7173260 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : term285 A v u f) : (term286 A v u f) = (term311 A u v f).
Proof. exact (prop_ext (fun h3 : term286 A v u f => @lem7173259 A v u f h1 h3) (fun h3 : term311 A u v f => @lem7173238 A v u f h2)). Qed.
Lemma lem7173261 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : @FINITE A u) (h2 : term285 A v u f) : term311 A u v f.
Proof. exact (EQ_MP (@lem7173260 A v u f h1 h2) (@lem7173238 A v u f h2)). Qed.
Lemma lem7173262 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term285 A v u f) : (@FINITE A u) = (term311 A u v f).
Proof. exact (prop_ext (fun h2 : @FINITE A u => @lem7173261 A v u f h2 h1) (fun h2 : term311 A u v f => @lem7173239 A v u f h1)). Qed.
Lemma lem7173263 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term285 A v u f) : term311 A u v f.
Proof. exact (EQ_MP (@lem7173262 A v u f h1) (@lem7173239 A v u f h1)). Qed.
Lemma lem7173264 {A : Type'} (u : A -> Prop) (v : A -> Prop) (f : A -> real) : term534 A u v f.
Proof. exact (fun h0 : term285 A v u f => @lem7173263 A v u f h0). Qed.
Lemma lem7173269 {A : Type'} (u : A -> Prop) (v : A -> Prop) : term535 A u v.
Proof. exact (fun f : A -> real => @lem7173264 A u v f). Qed.
Lemma lem7173274 {A : Type'} (u : A -> Prop) : term536 A u.
Proof. exact (fun v : A -> Prop => @lem7173269 A u v). Qed.
Lemma lem7173279 {A : Type'} : term537 A.
Proof. exact (fun u : A -> Prop => @lem7173274 A u). Qed.
