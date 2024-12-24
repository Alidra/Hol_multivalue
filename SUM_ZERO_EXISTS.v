Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_ZERO_EXISTS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import SUM_NEG_spec.
Require Import SUM_POS_EQ_0_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1361604_spec.
Require Import thm1362040_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
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
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988285_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988293_spec.
Require Import thm1988295_spec.
Require Import thm1988297_spec.
Require Import thm1988299_spec.
Require Import thm1988318_spec.
Require Import thm1988332_spec.
Require Import thm1988338_spec.
Require Import thm1988348_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7114168 {_132718 : Type'} (h1 : term0 _132718) : term0 _132718.
Proof. exact (h1). Qed.
Lemma lem7114169 {_132718 : Type'} (f : _132718 -> real) (h1 : term0 _132718) : term1 _132718 f.
Proof. exact (@lem7114168 _132718 h1 f). Qed.
Lemma lem7114170 {_132718 : Type'} (f : _132718 -> real) : (term1 _132718 f) = (term2 _132718 f).
Proof. exact (eq_refl (term1 _132718 f)). Qed.
Lemma lem7114171 {_132718 : Type'} (f : _132718 -> real) (h1 : term0 _132718) : term2 _132718 f.
Proof. exact (EQ_MP (@lem7114170 _132718 f) (@lem7114169 _132718 f h1)). Qed.
Lemma lem7114172 {_132718 : Type'} (f : _132718 -> real) (s : _132718 -> Prop) (h1 : term0 _132718) : term3 _132718 f s.
Proof. exact (@lem7114171 _132718 f h1 s). Qed.
Lemma lem7114173 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term3 _132718 f s) = (term4 _132718 s f).
Proof. exact (eq_refl (term3 _132718 f s)). Qed.
Lemma lem7114174 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (h1 : term0 _132718) : term4 _132718 s f.
Proof. exact (EQ_MP (@lem7114173 _132718 s f) (@lem7114172 _132718 f s h1)). Qed.
Lemma lem7114175 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (h1 : term5 _132718 s f) : term5 _132718 s f.
Proof. exact (h1). Qed.
Lemma lem7114176 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (h1 : term0 _132718) (h2 : term5 _132718 s f) : term6 _132718 s f.
Proof. exact (@lem7114174 _132718 s f h1 (@lem7114175 _132718 s f h2)). Qed.
Lemma lem7114177 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (h1 : term5 _132718 s f) : term7 _132718 s f.
Proof. exact (fun h0 : term0 _132718 => @lem7114176 _132718 s f h0 h1). Qed.
Lemma lem7114178 {_132718 : Type'} (h1 : term0 _132718) : term0 _132718.
Proof. exact (h1). Qed.
Lemma lem7114179 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (h1 : term0 _132718) (h2 : term5 _132718 s f) : term6 _132718 s f.
Proof. exact (@lem7114177 _132718 s f h2 (@lem7114178 _132718 h1)). Qed.
Lemma lem7114180 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (h1 : term0 _132718) : term4 _132718 s f.
Proof. exact (fun h0 : term5 _132718 s f => @lem7114179 _132718 s f h1 h0). Qed.
Lemma lem7114181 {_132718 : Type'} (s : _132718 -> Prop) (h1 : term0 _132718) : term8 _132718 s.
Proof. exact (fun f : _132718 -> real => @lem7114180 _132718 s f h1). Qed.
Lemma lem7114182 {_132718 : Type'} (h1 : term0 _132718) : term9 _132718.
Proof. exact (fun s : _132718 -> Prop => @lem7114181 _132718 s h1). Qed.
Lemma lem7114183 {_132718 : Type'} : term10 _132718.
Proof. exact (fun h0 : term0 _132718 => @lem7114182 _132718 h0). Qed.
Lemma lem7114184 {_132718 : Type'} : term9 _132718.
Proof. exact (@lem7114183 _132718 (@lem7114167 _132718)). Qed.
Lemma lem7114185 {_132718 : Type'} (s : _132718 -> Prop) : term11 _132718 s.
Proof. exact (@lem7114184 _132718 s). Qed.
Lemma lem7114186 {_132718 : Type'} (s : _132718 -> Prop) : (term11 _132718 s) = (term8 _132718 s).
Proof. exact (eq_refl (term11 _132718 s)). Qed.
Lemma lem7114187 {_132718 : Type'} (s : _132718 -> Prop) : term8 _132718 s.
Proof. exact (EQ_MP (@lem7114186 _132718 s) (@lem7114185 _132718 s)). Qed.
Lemma lem7114188 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : term12 _132718 s f.
Proof. exact (@lem7114187 _132718 s f). Qed.
Lemma lem7114189 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term12 _132718 s f) = (term4 _132718 s f).
Proof. exact (eq_refl (term12 _132718 s f)). Qed.
Lemma lem7114228 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem17646 (x = term15) ((real_neg x) = term15)). Qed.
Lemma lem7114229 (x : real) : (x = term15) = ((term16 x) = term15).
Proof. exact (@lem1988293 x term15). Qed.
Lemma lem7114235 (x : real) : (term16 x) = (term17 x).
Proof. exact (@lem1982792 x term15). Qed.
Lemma lem7114237 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7114238 : term15 = term19.
Proof. exact (@lem7114237 (NUMERAL 0)). Qed.
Lemma lem7114240 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7114241 : term22 = term23.
Proof. exact (@lem7114240 term24). Qed.
Lemma lem7114242 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7114243 : term25 = term26.
Proof. exact (MK_COMB (@lem7114242) (@lem7114241)). Qed.
Lemma lem7114244 : term27 = term28.
Proof. exact (MK_COMB (@lem7114243) (@lem7114238)). Qed.
Lemma lem7114245 : term28 = term29.
Proof. exact (@lem1981613 term22 term15 term30 term30). Qed.
Lemma lem7114247 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7114248 : term33 = term34.
Proof. exact (@lem7114247 term24 term24). Qed.
Lemma lem7114249 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114250 : term36 = term24.
Proof. exact (EQ_MP (@lem7114249) (@lem940073)). Qed.
Lemma lem7114251 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114252 : term34 = term30.
Proof. exact (MK_COMB (@lem7114251) (@lem7114250)). Qed.
Lemma lem7114253 : term33 = term30.
Proof. exact (TRANS (@lem7114248) (@lem7114252)). Qed.
Lemma lem7114255 (x : nat) : (term37 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7114256 : term27 = term15.
Proof. exact (@lem7114255 term24). Qed.
Lemma lem7114257 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7114258 : term38 = term39.
Proof. exact (MK_COMB (@lem7114257) (@lem7114256)). Qed.
Lemma lem7114259 : term29 = term19.
Proof. exact (MK_COMB (@lem7114258) (@lem7114253)). Qed.
Lemma lem7114260 : term28 = term19.
Proof. exact (TRANS (@lem7114245) (@lem7114259)). Qed.
Lemma lem7114261 : term27 = term19.
Proof. exact (TRANS (@lem7114244) (@lem7114260)). Qed.
Lemma lem7114263 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7114264 : term19 = term15.
Proof. exact (@lem7114263 term15). Qed.
Lemma lem7114265 : term27 = term15.
Proof. exact (TRANS (@lem7114261) (@lem7114264)). Qed.
Lemma lem7114266 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem7114267 (x : real) : (term17 x) = (term41 x).
Proof. exact (MK_COMB (@lem7114266 x) (@lem7114265)). Qed.
Lemma lem7114268 (x : real) : (term41 x) = x.
Proof. exact (@lem1982723 x). Qed.
Lemma lem7114269 (x : real) : (term17 x) = x.
Proof. exact (TRANS (@lem7114267 x) (@lem7114268 x)). Qed.
Lemma lem7114271 (x : real) : (term16 x) = x.
Proof. exact (TRANS (@lem7114235 x) (@lem7114269 x)). Qed.
Lemma lem7114272 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7114273 (x : real) : (term42 x) = (@eq real x).
Proof. exact (MK_COMB (@lem7114272) (@lem7114271 x)). Qed.
Lemma lem7114274 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7114275 (x : real) : ((term16 x) = term15) = (x = term15).
Proof. exact (MK_COMB (@lem7114273 x) (@lem7114274)). Qed.
Lemma lem7114276 (x : real) : (x = term15) = (x = term15).
Proof. exact (TRANS (@lem7114229 x) (@lem7114275 x)). Qed.
Lemma lem7114277 (x : real) : (term43 x) = (term44 x).
Proof. exact (@lem1988318 (real_neg x) term15). Qed.
Lemma lem7114278 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7114285 (x : real) : (real_neg x) = (term45 x).
Proof. exact (@lem1982785 x). Qed.
Lemma lem7114286 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7114287 (x : real) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem7114286) (@lem7114285 x)). Qed.
Lemma lem7114288 (x : real) : (term48 x) = (term49 x).
Proof. exact (MK_COMB (@lem7114287 x) (@lem7114278)). Qed.
Lemma lem7114289 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1982792 (term45 x) term15). Qed.
Lemma lem7114291 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7114292 : term15 = term19.
Proof. exact (@lem7114291 (NUMERAL 0)). Qed.
Lemma lem7114294 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7114295 : term22 = term23.
Proof. exact (@lem7114294 term24). Qed.
Lemma lem7114296 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7114297 : term25 = term26.
Proof. exact (MK_COMB (@lem7114296) (@lem7114295)). Qed.
Lemma lem7114298 : term27 = term28.
Proof. exact (MK_COMB (@lem7114297) (@lem7114292)). Qed.
Lemma lem7114299 : term28 = term29.
Proof. exact (@lem1981613 term22 term15 term30 term30). Qed.
Lemma lem7114301 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7114302 : term33 = term34.
Proof. exact (@lem7114301 term24 term24). Qed.
Lemma lem7114303 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114304 : term36 = term24.
Proof. exact (EQ_MP (@lem7114303) (@lem940073)). Qed.
Lemma lem7114305 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114306 : term34 = term30.
Proof. exact (MK_COMB (@lem7114305) (@lem7114304)). Qed.
Lemma lem7114307 : term33 = term30.
Proof. exact (TRANS (@lem7114302) (@lem7114306)). Qed.
Lemma lem7114309 (x : nat) : (term37 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7114310 : term27 = term15.
Proof. exact (@lem7114309 term24). Qed.
Lemma lem7114311 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7114312 : term38 = term39.
Proof. exact (MK_COMB (@lem7114311) (@lem7114310)). Qed.
Lemma lem7114313 : term29 = term19.
Proof. exact (MK_COMB (@lem7114312) (@lem7114307)). Qed.
Lemma lem7114314 : term28 = term19.
Proof. exact (TRANS (@lem7114299) (@lem7114313)). Qed.
Lemma lem7114315 : term27 = term19.
Proof. exact (TRANS (@lem7114298) (@lem7114314)). Qed.
Lemma lem7114317 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7114318 : term19 = term15.
Proof. exact (@lem7114317 term15). Qed.
Lemma lem7114319 : term27 = term15.
Proof. exact (TRANS (@lem7114315) (@lem7114318)). Qed.
Lemma lem7114320 (x : real) : (term51 x) = (term51 x).
Proof. exact (eq_refl (term51 x)). Qed.
Lemma lem7114321 (x : real) : (term50 x) = (term52 x).
Proof. exact (MK_COMB (@lem7114320 x) (@lem7114319)). Qed.
Lemma lem7114322 (x : real) : (term52 x) = (term45 x).
Proof. exact (@lem1982723 (term45 x)). Qed.
Lemma lem7114323 (x : real) : (term50 x) = (term45 x).
Proof. exact (TRANS (@lem7114321 x) (@lem7114322 x)). Qed.
Lemma lem7114324 (x : real) : (term49 x) = (term45 x).
Proof. exact (TRANS (@lem7114289 x) (@lem7114323 x)). Qed.
Lemma lem7114325 (x : real) : (term48 x) = (term45 x).
Proof. exact (TRANS (@lem7114288 x) (@lem7114324 x)). Qed.
Lemma lem7114326 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7114327 (x : real) : (term53 x) = (term54 x).
Proof. exact (MK_COMB (@lem7114326) (@lem7114325 x)). Qed.
Lemma lem7114328 (x : real) : (term54 x) = (term55 x).
Proof. exact (@lem1982785 (term45 x)). Qed.
Lemma lem7114329 (x : real) : (term55 x) = (term56 x).
Proof. exact (@lem1982749 term22 term22 x). Qed.
Lemma lem7114331 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7114332 : term22 = term23.
Proof. exact (@lem7114331 term24). Qed.
Lemma lem7114334 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7114335 : term22 = term23.
Proof. exact (@lem7114334 term24). Qed.
Lemma lem7114336 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7114337 : term25 = term26.
Proof. exact (MK_COMB (@lem7114336) (@lem7114335)). Qed.
Lemma lem7114338 : term57 = term58.
Proof. exact (MK_COMB (@lem7114337) (@lem7114332)). Qed.
Lemma lem7114339 : term58 = term59.
Proof. exact (@lem1981613 term22 term22 term30 term30). Qed.
Lemma lem7114341 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7114342 : term33 = term34.
Proof. exact (@lem7114341 term24 term24). Qed.
Lemma lem7114343 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114344 : term36 = term24.
Proof. exact (EQ_MP (@lem7114343) (@lem940073)). Qed.
Lemma lem7114345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114346 : term34 = term30.
Proof. exact (MK_COMB (@lem7114345) (@lem7114344)). Qed.
Lemma lem7114347 : term33 = term30.
Proof. exact (TRANS (@lem7114342) (@lem7114346)). Qed.
Lemma lem7114349 (m : nat) (n : nat) : (term60 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7114350 : term57 = term34.
Proof. exact (@lem7114349 term24 term24). Qed.
Lemma lem7114351 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114352 : term36 = term24.
Proof. exact (EQ_MP (@lem7114351) (@lem940073)). Qed.
Lemma lem7114353 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114354 : term34 = term30.
Proof. exact (MK_COMB (@lem7114353) (@lem7114352)). Qed.
Lemma lem7114355 : term57 = term30.
Proof. exact (TRANS (@lem7114350) (@lem7114354)). Qed.
Lemma lem7114356 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7114357 : term61 = term62.
Proof. exact (MK_COMB (@lem7114356) (@lem7114355)). Qed.
Lemma lem7114358 : term59 = term63.
Proof. exact (MK_COMB (@lem7114357) (@lem7114347)). Qed.
Lemma lem7114359 : term58 = term63.
Proof. exact (TRANS (@lem7114339) (@lem7114358)). Qed.
Lemma lem7114360 : term57 = term63.
Proof. exact (TRANS (@lem7114338) (@lem7114359)). Qed.
Lemma lem7114362 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7114363 : term63 = term30.
Proof. exact (@lem7114362 term30). Qed.
Lemma lem7114364 : term57 = term30.
Proof. exact (TRANS (@lem7114360) (@lem7114363)). Qed.
Lemma lem7114365 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7114366 : term64 = term65.
Proof. exact (MK_COMB (@lem7114365) (@lem7114364)). Qed.
Lemma lem7114367 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7114368 (x : real) : (term56 x) = (term66 x).
Proof. exact (MK_COMB (@lem7114366) (@lem7114367 x)). Qed.
Lemma lem7114369 (x : real) : (term55 x) = (term66 x).
Proof. exact (TRANS (@lem7114329 x) (@lem7114368 x)). Qed.
Lemma lem7114370 (x : real) : (term66 x) = x.
Proof. exact (@lem1982709 x). Qed.
Lemma lem7114371 (x : real) : (term55 x) = x.
Proof. exact (TRANS (@lem7114369 x) (@lem7114370 x)). Qed.
Lemma lem7114372 (x : real) : (term54 x) = x.
Proof. exact (TRANS (@lem7114328 x) (@lem7114371 x)). Qed.
Lemma lem7114373 (x : real) : (term67 x) = (term67 x).
Proof. exact (eq_refl (term67 x)). Qed.
Lemma lem7114374 (x : real) : ((term53 x) = (term54 x)) = ((term53 x) = x).
Proof. exact (MK_COMB (@lem7114373 x) (@lem7114372 x)). Qed.
Lemma lem7114375 (x : real) : (term53 x) = x.
Proof. exact (EQ_MP (@lem7114374 x) (@lem7114327 x)). Qed.
Lemma lem7114376 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7114377 (x : real) : (term68 x) = (real_gt x).
Proof. exact (MK_COMB (@lem7114376) (@lem7114375 x)). Qed.
Lemma lem7114378 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7114379 (x : real) : (term69 x) = (term70 x).
Proof. exact (MK_COMB (@lem7114377 x) (@lem7114378)). Qed.
Lemma lem7114380 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7114381 (x : real) : (term71 x) = (term72 x).
Proof. exact (MK_COMB (@lem7114380) (@lem7114325 x)). Qed.
Lemma lem7114382 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7114383 (x : real) : (term73 x) = (term74 x).
Proof. exact (MK_COMB (@lem7114381 x) (@lem7114382)). Qed.
Lemma lem7114384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7114385 (x : real) : (term75 x) = (term76 x).
Proof. exact (MK_COMB (@lem7114384) (@lem7114383 x)). Qed.
Lemma lem7114386 (x : real) : (term44 x) = (term77 x).
Proof. exact (MK_COMB (@lem7114385 x) (@lem7114379 x)). Qed.
Lemma lem7114387 (x : real) : (term43 x) = (term77 x).
Proof. exact (TRANS (@lem7114277 x) (@lem7114386 x)). Qed.
Lemma lem7114388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7114389 (x : real) : (term78 x) = (term78 x).
Proof. exact (MK_COMB (@lem7114388) (@lem7114276 x)). Qed.
Lemma lem7114390 (x : real) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem7114389 x) (@lem7114387 x)). Qed.
Lemma lem7114391 (x : real) : (term81 x) = (term82 x).
Proof. exact (@lem1988318 x term15). Qed.
Lemma lem7114397 (x : real) : (term16 x) = (term17 x).
Proof. exact (@lem1982792 x term15). Qed.
Lemma lem7114399 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7114400 : term15 = term19.
Proof. exact (@lem7114399 (NUMERAL 0)). Qed.
Lemma lem7114402 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7114403 : term22 = term23.
Proof. exact (@lem7114402 term24). Qed.
Lemma lem7114404 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7114405 : term25 = term26.
Proof. exact (MK_COMB (@lem7114404) (@lem7114403)). Qed.
Lemma lem7114406 : term27 = term28.
Proof. exact (MK_COMB (@lem7114405) (@lem7114400)). Qed.
Lemma lem7114407 : term28 = term29.
Proof. exact (@lem1981613 term22 term15 term30 term30). Qed.
Lemma lem7114409 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7114410 : term33 = term34.
Proof. exact (@lem7114409 term24 term24). Qed.
Lemma lem7114411 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114412 : term36 = term24.
Proof. exact (EQ_MP (@lem7114411) (@lem940073)). Qed.
Lemma lem7114413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114414 : term34 = term30.
Proof. exact (MK_COMB (@lem7114413) (@lem7114412)). Qed.
Lemma lem7114415 : term33 = term30.
Proof. exact (TRANS (@lem7114410) (@lem7114414)). Qed.
Lemma lem7114417 (x : nat) : (term37 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7114418 : term27 = term15.
Proof. exact (@lem7114417 term24). Qed.
Lemma lem7114419 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7114420 : term38 = term39.
Proof. exact (MK_COMB (@lem7114419) (@lem7114418)). Qed.
Lemma lem7114421 : term29 = term19.
Proof. exact (MK_COMB (@lem7114420) (@lem7114415)). Qed.
Lemma lem7114422 : term28 = term19.
Proof. exact (TRANS (@lem7114407) (@lem7114421)). Qed.
Lemma lem7114423 : term27 = term19.
Proof. exact (TRANS (@lem7114406) (@lem7114422)). Qed.
Lemma lem7114425 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7114426 : term19 = term15.
Proof. exact (@lem7114425 term15). Qed.
Lemma lem7114427 : term27 = term15.
Proof. exact (TRANS (@lem7114423) (@lem7114426)). Qed.
Lemma lem7114428 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem7114429 (x : real) : (term17 x) = (term41 x).
Proof. exact (MK_COMB (@lem7114428 x) (@lem7114427)). Qed.
Lemma lem7114430 (x : real) : (term41 x) = x.
Proof. exact (@lem1982723 x). Qed.
Lemma lem7114431 (x : real) : (term17 x) = x.
Proof. exact (TRANS (@lem7114429 x) (@lem7114430 x)). Qed.
Lemma lem7114433 (x : real) : (term16 x) = x.
Proof. exact (TRANS (@lem7114397 x) (@lem7114431 x)). Qed.
Lemma lem7114434 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7114435 (x : real) : (term83 x) = (real_neg x).
Proof. exact (MK_COMB (@lem7114434) (@lem7114433 x)). Qed.
Lemma lem7114438 (x : real) : (real_neg x) = (term45 x).
Proof. exact (@lem1982785 x). Qed.
Lemma lem7114439 (x : real) : (term84 x) = (term84 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem7114440 (x : real) : ((term83 x) = (real_neg x)) = ((term83 x) = (term45 x)).
Proof. exact (MK_COMB (@lem7114439 x) (@lem7114438 x)). Qed.
Lemma lem7114441 (x : real) : (term83 x) = (term45 x).
Proof. exact (EQ_MP (@lem7114440 x) (@lem7114435 x)). Qed.
Lemma lem7114442 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7114443 (x : real) : (term85 x) = (term72 x).
Proof. exact (MK_COMB (@lem7114442) (@lem7114441 x)). Qed.
Lemma lem7114444 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7114445 (x : real) : (term86 x) = (term74 x).
Proof. exact (MK_COMB (@lem7114443 x) (@lem7114444)). Qed.
Lemma lem7114446 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7114447 (x : real) : (term87 x) = (real_gt x).
Proof. exact (MK_COMB (@lem7114446) (@lem7114433 x)). Qed.
Lemma lem7114448 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7114449 (x : real) : (term88 x) = (term70 x).
Proof. exact (MK_COMB (@lem7114447 x) (@lem7114448)). Qed.
Lemma lem7114450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7114451 (x : real) : (term89 x) = (term90 x).
Proof. exact (MK_COMB (@lem7114450) (@lem7114449 x)). Qed.
Lemma lem7114452 (x : real) : (term82 x) = (term91 x).
Proof. exact (MK_COMB (@lem7114451 x) (@lem7114445 x)). Qed.
Lemma lem7114453 (x : real) : (term81 x) = (term91 x).
Proof. exact (TRANS (@lem7114391 x) (@lem7114452 x)). Qed.
Lemma lem7114454 (x : real) : ((real_neg x) = term15) = ((term48 x) = term15).
Proof. exact (@lem1988293 (real_neg x) term15). Qed.
Lemma lem7114455 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7114462 (x : real) : (real_neg x) = (term45 x).
Proof. exact (@lem1982785 x). Qed.
Lemma lem7114463 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7114464 (x : real) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem7114463) (@lem7114462 x)). Qed.
Lemma lem7114465 (x : real) : (term48 x) = (term49 x).
Proof. exact (MK_COMB (@lem7114464 x) (@lem7114455)). Qed.
Lemma lem7114466 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1982792 (term45 x) term15). Qed.
Lemma lem7114468 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7114469 : term15 = term19.
Proof. exact (@lem7114468 (NUMERAL 0)). Qed.
Lemma lem7114471 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7114472 : term22 = term23.
Proof. exact (@lem7114471 term24). Qed.
Lemma lem7114473 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7114474 : term25 = term26.
Proof. exact (MK_COMB (@lem7114473) (@lem7114472)). Qed.
Lemma lem7114475 : term27 = term28.
Proof. exact (MK_COMB (@lem7114474) (@lem7114469)). Qed.
Lemma lem7114476 : term28 = term29.
Proof. exact (@lem1981613 term22 term15 term30 term30). Qed.
Lemma lem7114478 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7114479 : term33 = term34.
Proof. exact (@lem7114478 term24 term24). Qed.
Lemma lem7114480 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114481 : term36 = term24.
Proof. exact (EQ_MP (@lem7114480) (@lem940073)). Qed.
Lemma lem7114482 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114483 : term34 = term30.
Proof. exact (MK_COMB (@lem7114482) (@lem7114481)). Qed.
Lemma lem7114484 : term33 = term30.
Proof. exact (TRANS (@lem7114479) (@lem7114483)). Qed.
Lemma lem7114486 (x : nat) : (term37 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7114487 : term27 = term15.
Proof. exact (@lem7114486 term24). Qed.
Lemma lem7114488 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7114489 : term38 = term39.
Proof. exact (MK_COMB (@lem7114488) (@lem7114487)). Qed.
Lemma lem7114490 : term29 = term19.
Proof. exact (MK_COMB (@lem7114489) (@lem7114484)). Qed.
Lemma lem7114491 : term28 = term19.
Proof. exact (TRANS (@lem7114476) (@lem7114490)). Qed.
Lemma lem7114492 : term27 = term19.
Proof. exact (TRANS (@lem7114475) (@lem7114491)). Qed.
Lemma lem7114494 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7114495 : term19 = term15.
Proof. exact (@lem7114494 term15). Qed.
Lemma lem7114496 : term27 = term15.
Proof. exact (TRANS (@lem7114492) (@lem7114495)). Qed.
Lemma lem7114497 (x : real) : (term51 x) = (term51 x).
Proof. exact (eq_refl (term51 x)). Qed.
Lemma lem7114498 (x : real) : (term50 x) = (term52 x).
Proof. exact (MK_COMB (@lem7114497 x) (@lem7114496)). Qed.
Lemma lem7114499 (x : real) : (term52 x) = (term45 x).
Proof. exact (@lem1982723 (term45 x)). Qed.
Lemma lem7114500 (x : real) : (term50 x) = (term45 x).
Proof. exact (TRANS (@lem7114498 x) (@lem7114499 x)). Qed.
Lemma lem7114501 (x : real) : (term49 x) = (term45 x).
Proof. exact (TRANS (@lem7114466 x) (@lem7114500 x)). Qed.
Lemma lem7114502 (x : real) : (term48 x) = (term45 x).
Proof. exact (TRANS (@lem7114465 x) (@lem7114501 x)). Qed.
Lemma lem7114503 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7114504 (x : real) : (term92 x) = (term93 x).
Proof. exact (MK_COMB (@lem7114503) (@lem7114502 x)). Qed.
Lemma lem7114505 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7114506 (x : real) : ((term48 x) = term15) = ((term45 x) = term15).
Proof. exact (MK_COMB (@lem7114504 x) (@lem7114505)). Qed.
Lemma lem7114507 (x : real) : ((real_neg x) = term15) = ((term45 x) = term15).
Proof. exact (TRANS (@lem7114454 x) (@lem7114506 x)). Qed.
Lemma lem7114508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7114509 (x : real) : (term94 x) = (term95 x).
Proof. exact (MK_COMB (@lem7114508) (@lem7114453 x)). Qed.
Lemma lem7114510 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem7114509 x) (@lem7114507 x)). Qed.
Lemma lem7114511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7114512 (x : real) : (term98 x) = (term99 x).
Proof. exact (MK_COMB (@lem7114511) (@lem7114390 x)). Qed.
Lemma lem7114513 (x : real) : (term14 x) = (term100 x).
Proof. exact (MK_COMB (@lem7114512 x) (@lem7114510 x)). Qed.
Lemma lem7114520 (x : real) : (term13 x) = (term100 x).
Proof. exact (TRANS (@lem7114228 x) (@lem7114513 x)). Qed.
Lemma lem7114537 (x : real) : (term97 x) = (term101 x).
Proof. exact (@lem19367 (term70 x) (term74 x) ((term45 x) = term15)). Qed.
Lemma lem7114554 (x : real) : (term80 x) = (term102 x).
Proof. exact (@lem19158 (term74 x) (x = term15) (term70 x)). Qed.
Lemma lem7114555 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7114556 (x : real) : (term99 x) = (term103 x).
Proof. exact (MK_COMB (@lem7114555) (@lem7114554 x)). Qed.
Lemma lem7114557 (x : real) : (term100 x) = (term104 x).
Proof. exact (MK_COMB (@lem7114556 x) (@lem7114537 x)). Qed.
Lemma lem7114558 (x : real) : (term13 x) = (term104 x).
Proof. exact (TRANS (@lem7114520 x) (@lem7114557 x)). Qed.
Lemma lem7114580 (x : real) (h1 : term104 x) : term104 x.
Proof. exact (h1). Qed.
Lemma lem7114581 (x : real) (h1 : term102 x) : term102 x.
Proof. exact (h1). Qed.
Lemma lem7114582 (x : real) (h1 : term105 x) : term105 x.
Proof. exact (h1). Qed.
Lemma lem7114583 (x : real) (h1 : term105 x) : term74 x.
Proof. exact (proj2 (@lem7114582 x h1)). Qed.
Lemma lem7114584 (x : real) (h1 : term105 x) : x = term15.
Proof. exact (proj1 (@lem7114582 x h1)). Qed.
Lemma lem7114586 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7114587 : term106 = term107.
Proof. exact (@lem7114586 term15 term30). Qed.
Lemma lem7114589 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7114590 : term30 = term63.
Proof. exact (@lem7114589 term24). Qed.
Lemma lem7114592 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7114593 : term15 = term19.
Proof. exact (@lem7114592 (NUMERAL 0)). Qed.
Lemma lem7114594 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7114595 : term108 = term109.
Proof. exact (MK_COMB (@lem7114594) (@lem7114593)). Qed.
Lemma lem7114596 : term107 = term110.
Proof. exact (MK_COMB (@lem7114595) (@lem7114590)). Qed.
Lemma lem7114597 : term111.
Proof. exact (@lem1980255 term15 term30 term30 term30). Qed.
Lemma lem7114599 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114600 : term107 = term113.
Proof. exact (@lem7114599 (NUMERAL 0) term24). Qed.
Lemma lem7114601 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114602 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114603 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114602 h1) (fun h1 : term113 = True => @lem7114601)). Qed.
Lemma lem7114604 : term113 = True.
Proof. exact (EQ_MP (@lem7114603) (@lem7114601)). Qed.
Lemma lem7114605 : term107 = True.
Proof. exact (TRANS (@lem7114600) (@lem7114604)). Qed.
Lemma lem7114606 : True = term107.
Proof. exact (SYM (@lem7114605)). Qed.
Lemma lem7114607 : term107.
Proof. exact (EQ_MP (@lem7114606) (@lem0)). Qed.
Lemma lem7114608 : term115.
Proof. exact (@lem7114597 (@lem7114607)). Qed.
Lemma lem7114610 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114611 : term107 = term113.
Proof. exact (@lem7114610 (NUMERAL 0) term24). Qed.
Lemma lem7114612 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114613 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114614 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114613 h1) (fun h1 : term113 = True => @lem7114612)). Qed.
Lemma lem7114615 : term113 = True.
Proof. exact (EQ_MP (@lem7114614) (@lem7114612)). Qed.
Lemma lem7114616 : term107 = True.
Proof. exact (TRANS (@lem7114611) (@lem7114615)). Qed.
Lemma lem7114617 : True = term107.
Proof. exact (SYM (@lem7114616)). Qed.
Lemma lem7114618 : term107.
Proof. exact (EQ_MP (@lem7114617) (@lem0)). Qed.
Lemma lem7114619 : term110 = term116.
Proof. exact (@lem7114608 (@lem7114618)). Qed.
Lemma lem7114621 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7114622 : term33 = term34.
Proof. exact (@lem7114621 term24 term24). Qed.
Lemma lem7114623 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114624 : term36 = term24.
Proof. exact (EQ_MP (@lem7114623) (@lem940073)). Qed.
Lemma lem7114625 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114626 : term34 = term30.
Proof. exact (MK_COMB (@lem7114625) (@lem7114624)). Qed.
Lemma lem7114627 : term33 = term30.
Proof. exact (TRANS (@lem7114622) (@lem7114626)). Qed.
Lemma lem7114629 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7114630 : term118 = term15.
Proof. exact (@lem7114629 term24). Qed.
Lemma lem7114631 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7114632 : term119 = term108.
Proof. exact (MK_COMB (@lem7114631) (@lem7114630)). Qed.
Lemma lem7114633 : term116 = term107.
Proof. exact (MK_COMB (@lem7114632) (@lem7114627)). Qed.
Lemma lem7114635 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114636 : term107 = term113.
Proof. exact (@lem7114635 (NUMERAL 0) term24). Qed.
Lemma lem7114637 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114638 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114639 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114638 h1) (fun h1 : term113 = True => @lem7114637)). Qed.
Lemma lem7114640 : term113 = True.
Proof. exact (EQ_MP (@lem7114639) (@lem7114637)). Qed.
Lemma lem7114641 : term107 = True.
Proof. exact (TRANS (@lem7114636) (@lem7114640)). Qed.
Lemma lem7114642 : term116 = True.
Proof. exact (TRANS (@lem7114633) (@lem7114641)). Qed.
Lemma lem7114643 : term110 = True.
Proof. exact (TRANS (@lem7114619) (@lem7114642)). Qed.
Lemma lem7114644 : term107 = True.
Proof. exact (TRANS (@lem7114596) (@lem7114643)). Qed.
Lemma lem7114645 : term106 = True.
Proof. exact (TRANS (@lem7114587) (@lem7114644)). Qed.
Lemma lem7114646 : True = term106.
Proof. exact (SYM (@lem7114645)). Qed.
Lemma lem7114647 : term106.
Proof. exact (EQ_MP (@lem7114646) (@lem0)). Qed.
Lemma lem7114648 (x : real) (h1 : term105 x) : term120 x.
Proof. exact (conj (@lem7114647) (@lem7114583 x h1)). Qed.
Lemma lem7114650 (x : real) (y : real) : term121 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7114651 (x : real) : term122 x.
Proof. exact (@lem7114650 term30 (term45 x)). Qed.
Lemma lem7114652 (x : real) (h1 : term105 x) : term123 x.
Proof. exact (@lem7114651 x (@lem7114648 x h1)). Qed.
Lemma lem7114653 (x : real) : (term124 x) = (term45 x).
Proof. exact (@lem1982733 (term45 x)). Qed.
Lemma lem7114654 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7114655 (x : real) : (term125 x) = (term72 x).
Proof. exact (MK_COMB (@lem7114654) (@lem7114653 x)). Qed.
Lemma lem7114656 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7114657 (x : real) : (term123 x) = (term74 x).
Proof. exact (MK_COMB (@lem7114655 x) (@lem7114656)). Qed.
Lemma lem7114658 (x : real) (h1 : term105 x) : term74 x.
Proof. exact (EQ_MP (@lem7114657 x) (@lem7114652 x h1)). Qed.
Lemma lem7114660 (y : real) : term126 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7114661 (x : real) : term126 x.
Proof. exact (@lem7114660 x). Qed.
Lemma lem7114662 (x : real) (h1 : term105 x) : term127 x.
Proof. exact (@lem7114661 x (@lem7114584 x h1)). Qed.
Lemma lem7114663 (x : real) (h1 : term105 x) : term128 x.
Proof. exact (@lem7114662 x h1 term30). Qed.
Lemma lem7114664 (x : real) : (term128 x) = ((term66 x) = term15).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem7114665 (x : real) (h1 : term105 x) : (term66 x) = term15.
Proof. exact (EQ_MP (@lem7114664 x) (@lem7114663 x h1)). Qed.
Lemma lem7114666 (x : real) : (term66 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem7114667 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7114668 (x : real) : (term129 x) = (@eq real x).
Proof. exact (MK_COMB (@lem7114667) (@lem7114666 x)). Qed.
Lemma lem7114669 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7114670 (x : real) : ((term66 x) = term15) = (x = term15).
Proof. exact (MK_COMB (@lem7114668 x) (@lem7114669)). Qed.
Lemma lem7114671 (x : real) (h1 : term105 x) : x = term15.
Proof. exact (EQ_MP (@lem7114670 x) (@lem7114665 x h1)). Qed.
Lemma lem7114672 (x : real) (h1 : term105 x) : term105 x.
Proof. exact (conj (@lem7114671 x h1) (@lem7114658 x h1)). Qed.
Lemma lem7114674 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem7114675 (x : real) : term131 x.
Proof. exact (@lem7114674 x (term45 x)). Qed.
Lemma lem7114676 (x : real) (h1 : term105 x) : term132 x.
Proof. exact (@lem7114675 x (@lem7114672 x h1)). Qed.
Lemma lem7114677 (x : real) : (term133 x) = (term134 x).
Proof. exact (@lem1982715 term22 x). Qed.
Lemma lem7114679 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7114680 : term30 = term63.
Proof. exact (@lem7114679 term24). Qed.
Lemma lem7114682 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7114683 : term22 = term23.
Proof. exact (@lem7114682 term24). Qed.
Lemma lem7114684 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7114685 : term135 = term136.
Proof. exact (MK_COMB (@lem7114684) (@lem7114683)). Qed.
Lemma lem7114686 : term137 = term138.
Proof. exact (MK_COMB (@lem7114685) (@lem7114680)). Qed.
Lemma lem7114687 : term139.
Proof. exact (@lem1981473 term22 term30 term30 term30 term15 term30). Qed.
Lemma lem7114689 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114690 : term107 = term113.
Proof. exact (@lem7114689 (NUMERAL 0) term24). Qed.
Lemma lem7114691 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114692 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114693 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114692 h1) (fun h1 : term113 = True => @lem7114691)). Qed.
Lemma lem7114694 : term113 = True.
Proof. exact (EQ_MP (@lem7114693) (@lem7114691)). Qed.
Lemma lem7114695 : term107 = True.
Proof. exact (TRANS (@lem7114690) (@lem7114694)). Qed.
Lemma lem7114696 : True = term107.
Proof. exact (SYM (@lem7114695)). Qed.
Lemma lem7114697 : term107.
Proof. exact (EQ_MP (@lem7114696) (@lem0)). Qed.
Lemma lem7114698 : term140.
Proof. exact (@lem7114687 (@lem7114697)). Qed.
Lemma lem7114700 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114701 : term107 = term113.
Proof. exact (@lem7114700 (NUMERAL 0) term24). Qed.
Lemma lem7114702 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114703 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114704 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114703 h1) (fun h1 : term113 = True => @lem7114702)). Qed.
Lemma lem7114705 : term113 = True.
Proof. exact (EQ_MP (@lem7114704) (@lem7114702)). Qed.
Lemma lem7114706 : term107 = True.
Proof. exact (TRANS (@lem7114701) (@lem7114705)). Qed.
Lemma lem7114707 : True = term107.
Proof. exact (SYM (@lem7114706)). Qed.
Lemma lem7114708 : term107.
Proof. exact (EQ_MP (@lem7114707) (@lem0)). Qed.
Lemma lem7114709 : term141.
Proof. exact (@lem7114698 (@lem7114708)). Qed.
Lemma lem7114711 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114712 : term107 = term113.
Proof. exact (@lem7114711 (NUMERAL 0) term24). Qed.
Lemma lem7114713 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114714 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114715 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114714 h1) (fun h1 : term113 = True => @lem7114713)). Qed.
Lemma lem7114716 : term113 = True.
Proof. exact (EQ_MP (@lem7114715) (@lem7114713)). Qed.
Lemma lem7114717 : term107 = True.
Proof. exact (TRANS (@lem7114712) (@lem7114716)). Qed.
Lemma lem7114718 : True = term107.
Proof. exact (SYM (@lem7114717)). Qed.
Lemma lem7114719 : term107.
Proof. exact (EQ_MP (@lem7114718) (@lem0)). Qed.
Lemma lem7114720 : term142.
Proof. exact (@lem7114709 (@lem7114719)). Qed.
Lemma lem7114722 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7114723 : term33 = term34.
Proof. exact (@lem7114722 term24 term24). Qed.
Lemma lem7114724 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114725 : term36 = term24.
Proof. exact (EQ_MP (@lem7114724) (@lem940073)). Qed.
Lemma lem7114726 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114727 : term34 = term30.
Proof. exact (MK_COMB (@lem7114726) (@lem7114725)). Qed.
Lemma lem7114728 : term33 = term30.
Proof. exact (TRANS (@lem7114723) (@lem7114727)). Qed.
Lemma lem7114730 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7114731 : term145 = term146.
Proof. exact (@lem7114730 term24 term24). Qed.
Lemma lem7114732 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114733 : term36 = term24.
Proof. exact (EQ_MP (@lem7114732) (@lem940073)). Qed.
Lemma lem7114734 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114735 : term34 = term30.
Proof. exact (MK_COMB (@lem7114734) (@lem7114733)). Qed.
Lemma lem7114736 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7114737 : term146 = term22.
Proof. exact (MK_COMB (@lem7114736) (@lem7114735)). Qed.
Lemma lem7114738 : term145 = term22.
Proof. exact (TRANS (@lem7114731) (@lem7114737)). Qed.
Lemma lem7114739 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7114740 : term147 = term135.
Proof. exact (MK_COMB (@lem7114739) (@lem7114738)). Qed.
Lemma lem7114741 : term148 = term137.
Proof. exact (MK_COMB (@lem7114740) (@lem7114728)). Qed.
Lemma lem7114743 (m : nat) : (term149 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7114744 : term137 = term15.
Proof. exact (@lem7114743 term24). Qed.
Lemma lem7114745 : term148 = term15.
Proof. exact (TRANS (@lem7114741) (@lem7114744)). Qed.
Lemma lem7114746 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7114747 : term150 = term151.
Proof. exact (MK_COMB (@lem7114746) (@lem7114745)). Qed.
Lemma lem7114748 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem7114749 : term152 = term118.
Proof. exact (MK_COMB (@lem7114747) (@lem7114748)). Qed.
Lemma lem7114751 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7114752 : term118 = term15.
Proof. exact (@lem7114751 term24). Qed.
Lemma lem7114753 : term152 = term15.
Proof. exact (TRANS (@lem7114749) (@lem7114752)). Qed.
Lemma lem7114755 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7114756 : term33 = term34.
Proof. exact (@lem7114755 term24 term24). Qed.
Lemma lem7114757 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114758 : term36 = term24.
Proof. exact (EQ_MP (@lem7114757) (@lem940073)). Qed.
Lemma lem7114759 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114760 : term34 = term30.
Proof. exact (MK_COMB (@lem7114759) (@lem7114758)). Qed.
Lemma lem7114761 : term33 = term30.
Proof. exact (TRANS (@lem7114756) (@lem7114760)). Qed.
Lemma lem7114762 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7114763 : term153 = term118.
Proof. exact (MK_COMB (@lem7114762) (@lem7114761)). Qed.
Lemma lem7114765 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7114766 : term118 = term15.
Proof. exact (@lem7114765 term24). Qed.
Lemma lem7114767 : term153 = term15.
Proof. exact (TRANS (@lem7114763) (@lem7114766)). Qed.
Lemma lem7114768 : term15 = term153.
Proof. exact (SYM (@lem7114767)). Qed.
Lemma lem7114769 : term152 = term153.
Proof. exact (TRANS (@lem7114753) (@lem7114768)). Qed.
Lemma lem7114770 : term138 = term19.
Proof. exact (@lem7114720 (@lem7114769)). Qed.
Lemma lem7114771 : term137 = term19.
Proof. exact (TRANS (@lem7114686) (@lem7114770)). Qed.
Lemma lem7114773 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7114774 : term19 = term15.
Proof. exact (@lem7114773 term15). Qed.
Lemma lem7114775 : term137 = term15.
Proof. exact (TRANS (@lem7114771) (@lem7114774)). Qed.
Lemma lem7114776 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7114777 : term154 = term151.
Proof. exact (MK_COMB (@lem7114776) (@lem7114775)). Qed.
Lemma lem7114778 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7114779 (x : real) : (term134 x) = (term155 x).
Proof. exact (MK_COMB (@lem7114777) (@lem7114778 x)). Qed.
Lemma lem7114780 (x : real) : (term133 x) = (term155 x).
Proof. exact (TRANS (@lem7114677 x) (@lem7114779 x)). Qed.
Lemma lem7114781 (x : real) : (term155 x) = term15.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7114782 (x : real) : (term133 x) = term15.
Proof. exact (TRANS (@lem7114780 x) (@lem7114781 x)). Qed.
Lemma lem7114783 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7114784 (x : real) : (term156 x) = term157.
Proof. exact (MK_COMB (@lem7114783) (@lem7114782 x)). Qed.
Lemma lem7114785 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7114786 (x : real) : (term132 x) = term158.
Proof. exact (MK_COMB (@lem7114784 x) (@lem7114785)). Qed.
Lemma lem7114787 (x : real) (h1 : term105 x) : term158.
Proof. exact (EQ_MP (@lem7114786 x) (@lem7114676 x h1)). Qed.
Lemma lem7114789 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7114790 : term158 = term159.
Proof. exact (@lem7114789 term15 term15). Qed.
Lemma lem7114792 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7114793 : term15 = term19.
Proof. exact (@lem7114792 (NUMERAL 0)). Qed.
Lemma lem7114795 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7114796 : term15 = term19.
Proof. exact (@lem7114795 (NUMERAL 0)). Qed.
Lemma lem7114797 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7114798 : term108 = term109.
Proof. exact (MK_COMB (@lem7114797) (@lem7114796)). Qed.
Lemma lem7114799 : term159 = term160.
Proof. exact (MK_COMB (@lem7114798) (@lem7114793)). Qed.
Lemma lem7114800 : term161.
Proof. exact (@lem1980255 term15 term30 term15 term30). Qed.
Lemma lem7114802 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114803 : term107 = term113.
Proof. exact (@lem7114802 (NUMERAL 0) term24). Qed.
Lemma lem7114804 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114805 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114806 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114805 h1) (fun h1 : term113 = True => @lem7114804)). Qed.
Lemma lem7114807 : term113 = True.
Proof. exact (EQ_MP (@lem7114806) (@lem7114804)). Qed.
Lemma lem7114808 : term107 = True.
Proof. exact (TRANS (@lem7114803) (@lem7114807)). Qed.
Lemma lem7114809 : True = term107.
Proof. exact (SYM (@lem7114808)). Qed.
Lemma lem7114810 : term107.
Proof. exact (EQ_MP (@lem7114809) (@lem0)). Qed.
Lemma lem7114811 : term162.
Proof. exact (@lem7114800 (@lem7114810)). Qed.
Lemma lem7114813 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114814 : term107 = term113.
Proof. exact (@lem7114813 (NUMERAL 0) term24). Qed.
Lemma lem7114815 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114816 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114817 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114816 h1) (fun h1 : term113 = True => @lem7114815)). Qed.
Lemma lem7114818 : term113 = True.
Proof. exact (EQ_MP (@lem7114817) (@lem7114815)). Qed.
Lemma lem7114819 : term107 = True.
Proof. exact (TRANS (@lem7114814) (@lem7114818)). Qed.
Lemma lem7114820 : True = term107.
Proof. exact (SYM (@lem7114819)). Qed.
Lemma lem7114821 : term107.
Proof. exact (EQ_MP (@lem7114820) (@lem0)). Qed.
Lemma lem7114822 : term160 = term163.
Proof. exact (@lem7114811 (@lem7114821)). Qed.
Lemma lem7114824 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7114825 : term118 = term15.
Proof. exact (@lem7114824 term24). Qed.
Lemma lem7114827 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7114828 : term118 = term15.
Proof. exact (@lem7114827 term24). Qed.
Lemma lem7114829 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7114830 : term119 = term108.
Proof. exact (MK_COMB (@lem7114829) (@lem7114828)). Qed.
Lemma lem7114831 : term163 = term159.
Proof. exact (MK_COMB (@lem7114830) (@lem7114825)). Qed.
Lemma lem7114833 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114834 : term159 = term164.
Proof. exact (@lem7114833 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7114835 : term164 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7114836 : term159 = False.
Proof. exact (TRANS (@lem7114834) (@lem7114835)). Qed.
Lemma lem7114837 : term163 = False.
Proof. exact (TRANS (@lem7114831) (@lem7114836)). Qed.
Lemma lem7114838 : term160 = False.
Proof. exact (TRANS (@lem7114822) (@lem7114837)). Qed.
Lemma lem7114839 : term159 = False.
Proof. exact (TRANS (@lem7114799) (@lem7114838)). Qed.
Lemma lem7114840 : term158 = False.
Proof. exact (TRANS (@lem7114790) (@lem7114839)). Qed.
Lemma lem7114841 (x : real) (h1 : term105 x) : False.
Proof. exact (EQ_MP (@lem7114840) (@lem7114787 x h1)). Qed.
Lemma lem7114842 (x : real) (h1 : term165 x) : term165 x.
Proof. exact (h1). Qed.
Lemma lem7114843 (x : real) (h1 : term165 x) : term70 x.
Proof. exact (proj2 (@lem7114842 x h1)). Qed.
Lemma lem7114844 (x : real) (h1 : term165 x) : x = term15.
Proof. exact (proj1 (@lem7114842 x h1)). Qed.
Lemma lem7114846 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7114847 : term106 = term107.
Proof. exact (@lem7114846 term15 term30). Qed.
Lemma lem7114849 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7114850 : term30 = term63.
Proof. exact (@lem7114849 term24). Qed.
Lemma lem7114852 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7114853 : term15 = term19.
Proof. exact (@lem7114852 (NUMERAL 0)). Qed.
Lemma lem7114854 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7114855 : term108 = term109.
Proof. exact (MK_COMB (@lem7114854) (@lem7114853)). Qed.
Lemma lem7114856 : term107 = term110.
Proof. exact (MK_COMB (@lem7114855) (@lem7114850)). Qed.
Lemma lem7114857 : term111.
Proof. exact (@lem1980255 term15 term30 term30 term30). Qed.
Lemma lem7114859 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114860 : term107 = term113.
Proof. exact (@lem7114859 (NUMERAL 0) term24). Qed.
Lemma lem7114861 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114862 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114863 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114862 h1) (fun h1 : term113 = True => @lem7114861)). Qed.
Lemma lem7114864 : term113 = True.
Proof. exact (EQ_MP (@lem7114863) (@lem7114861)). Qed.
Lemma lem7114865 : term107 = True.
Proof. exact (TRANS (@lem7114860) (@lem7114864)). Qed.
Lemma lem7114866 : True = term107.
Proof. exact (SYM (@lem7114865)). Qed.
Lemma lem7114867 : term107.
Proof. exact (EQ_MP (@lem7114866) (@lem0)). Qed.
Lemma lem7114868 : term115.
Proof. exact (@lem7114857 (@lem7114867)). Qed.
Lemma lem7114870 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114871 : term107 = term113.
Proof. exact (@lem7114870 (NUMERAL 0) term24). Qed.
Lemma lem7114872 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114873 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114874 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114873 h1) (fun h1 : term113 = True => @lem7114872)). Qed.
Lemma lem7114875 : term113 = True.
Proof. exact (EQ_MP (@lem7114874) (@lem7114872)). Qed.
Lemma lem7114876 : term107 = True.
Proof. exact (TRANS (@lem7114871) (@lem7114875)). Qed.
Lemma lem7114877 : True = term107.
Proof. exact (SYM (@lem7114876)). Qed.
Lemma lem7114878 : term107.
Proof. exact (EQ_MP (@lem7114877) (@lem0)). Qed.
Lemma lem7114879 : term110 = term116.
Proof. exact (@lem7114868 (@lem7114878)). Qed.
Lemma lem7114881 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7114882 : term33 = term34.
Proof. exact (@lem7114881 term24 term24). Qed.
Lemma lem7114883 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114884 : term36 = term24.
Proof. exact (EQ_MP (@lem7114883) (@lem940073)). Qed.
Lemma lem7114885 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114886 : term34 = term30.
Proof. exact (MK_COMB (@lem7114885) (@lem7114884)). Qed.
Lemma lem7114887 : term33 = term30.
Proof. exact (TRANS (@lem7114882) (@lem7114886)). Qed.
Lemma lem7114889 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7114890 : term118 = term15.
Proof. exact (@lem7114889 term24). Qed.
Lemma lem7114891 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7114892 : term119 = term108.
Proof. exact (MK_COMB (@lem7114891) (@lem7114890)). Qed.
Lemma lem7114893 : term116 = term107.
Proof. exact (MK_COMB (@lem7114892) (@lem7114887)). Qed.
Lemma lem7114895 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114896 : term107 = term113.
Proof. exact (@lem7114895 (NUMERAL 0) term24). Qed.
Lemma lem7114897 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114898 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114899 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114898 h1) (fun h1 : term113 = True => @lem7114897)). Qed.
Lemma lem7114900 : term113 = True.
Proof. exact (EQ_MP (@lem7114899) (@lem7114897)). Qed.
Lemma lem7114901 : term107 = True.
Proof. exact (TRANS (@lem7114896) (@lem7114900)). Qed.
Lemma lem7114902 : term116 = True.
Proof. exact (TRANS (@lem7114893) (@lem7114901)). Qed.
Lemma lem7114903 : term110 = True.
Proof. exact (TRANS (@lem7114879) (@lem7114902)). Qed.
Lemma lem7114904 : term107 = True.
Proof. exact (TRANS (@lem7114856) (@lem7114903)). Qed.
Lemma lem7114905 : term106 = True.
Proof. exact (TRANS (@lem7114847) (@lem7114904)). Qed.
Lemma lem7114906 : True = term106.
Proof. exact (SYM (@lem7114905)). Qed.
Lemma lem7114907 : term106.
Proof. exact (EQ_MP (@lem7114906) (@lem0)). Qed.
Lemma lem7114908 (x : real) (h1 : term165 x) : term166 x.
Proof. exact (conj (@lem7114907) (@lem7114843 x h1)). Qed.
Lemma lem7114910 (x : real) (y : real) : term121 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7114911 (x : real) : term167 x.
Proof. exact (@lem7114910 term30 x). Qed.
Lemma lem7114912 (x : real) (h1 : term165 x) : term168 x.
Proof. exact (@lem7114911 x (@lem7114908 x h1)). Qed.
Lemma lem7114913 (x : real) : (term66 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem7114914 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7114915 (x : real) : (term169 x) = (real_gt x).
Proof. exact (MK_COMB (@lem7114914) (@lem7114913 x)). Qed.
Lemma lem7114916 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7114917 (x : real) : (term168 x) = (term70 x).
Proof. exact (MK_COMB (@lem7114915 x) (@lem7114916)). Qed.
Lemma lem7114918 (x : real) (h1 : term165 x) : term70 x.
Proof. exact (EQ_MP (@lem7114917 x) (@lem7114912 x h1)). Qed.
Lemma lem7114920 (y : real) : term126 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7114921 (x : real) : term126 x.
Proof. exact (@lem7114920 x). Qed.
Lemma lem7114922 (x : real) (h1 : term165 x) : term127 x.
Proof. exact (@lem7114921 x (@lem7114844 x h1)). Qed.
Lemma lem7114923 (x : real) (h1 : term165 x) : term170 x.
Proof. exact (@lem7114922 x h1 term22). Qed.
Lemma lem7114924 (x : real) : (term170 x) = ((term45 x) = term15).
Proof. exact (eq_refl (term170 x)). Qed.
Lemma lem7114931 (x : real) (h1 : term165 x) : (term45 x) = term15.
Proof. exact (EQ_MP (@lem7114924 x) (@lem7114923 x h1)). Qed.
Lemma lem7114932 (x : real) (h1 : term165 x) : term171 x.
Proof. exact (conj (@lem7114931 x h1) (@lem7114918 x h1)). Qed.
Lemma lem7114934 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem7114935 (x : real) : term172 x.
Proof. exact (@lem7114934 (term45 x) x). Qed.
Lemma lem7114936 (x : real) (h1 : term165 x) : term173 x.
Proof. exact (@lem7114935 x (@lem7114932 x h1)). Qed.
Lemma lem7114937 (x : real) : (term174 x) = (term134 x).
Proof. exact (@lem1982713 term22 x). Qed.
Lemma lem7114939 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7114940 : term30 = term63.
Proof. exact (@lem7114939 term24). Qed.
Lemma lem7114942 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7114943 : term22 = term23.
Proof. exact (@lem7114942 term24). Qed.
Lemma lem7114944 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7114945 : term135 = term136.
Proof. exact (MK_COMB (@lem7114944) (@lem7114943)). Qed.
Lemma lem7114946 : term137 = term138.
Proof. exact (MK_COMB (@lem7114945) (@lem7114940)). Qed.
Lemma lem7114947 : term139.
Proof. exact (@lem1981473 term22 term30 term30 term30 term15 term30). Qed.
Lemma lem7114949 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114950 : term107 = term113.
Proof. exact (@lem7114949 (NUMERAL 0) term24). Qed.
Lemma lem7114951 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114952 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114953 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114952 h1) (fun h1 : term113 = True => @lem7114951)). Qed.
Lemma lem7114954 : term113 = True.
Proof. exact (EQ_MP (@lem7114953) (@lem7114951)). Qed.
Lemma lem7114955 : term107 = True.
Proof. exact (TRANS (@lem7114950) (@lem7114954)). Qed.
Lemma lem7114956 : True = term107.
Proof. exact (SYM (@lem7114955)). Qed.
Lemma lem7114957 : term107.
Proof. exact (EQ_MP (@lem7114956) (@lem0)). Qed.
Lemma lem7114958 : term140.
Proof. exact (@lem7114947 (@lem7114957)). Qed.
Lemma lem7114960 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114961 : term107 = term113.
Proof. exact (@lem7114960 (NUMERAL 0) term24). Qed.
Lemma lem7114962 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114963 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114964 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114963 h1) (fun h1 : term113 = True => @lem7114962)). Qed.
Lemma lem7114965 : term113 = True.
Proof. exact (EQ_MP (@lem7114964) (@lem7114962)). Qed.
Lemma lem7114966 : term107 = True.
Proof. exact (TRANS (@lem7114961) (@lem7114965)). Qed.
Lemma lem7114967 : True = term107.
Proof. exact (SYM (@lem7114966)). Qed.
Lemma lem7114968 : term107.
Proof. exact (EQ_MP (@lem7114967) (@lem0)). Qed.
Lemma lem7114969 : term141.
Proof. exact (@lem7114958 (@lem7114968)). Qed.
Lemma lem7114971 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7114972 : term107 = term113.
Proof. exact (@lem7114971 (NUMERAL 0) term24). Qed.
Lemma lem7114973 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7114974 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7114975 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7114974 h1) (fun h1 : term113 = True => @lem7114973)). Qed.
Lemma lem7114976 : term113 = True.
Proof. exact (EQ_MP (@lem7114975) (@lem7114973)). Qed.
Lemma lem7114977 : term107 = True.
Proof. exact (TRANS (@lem7114972) (@lem7114976)). Qed.
Lemma lem7114978 : True = term107.
Proof. exact (SYM (@lem7114977)). Qed.
Lemma lem7114979 : term107.
Proof. exact (EQ_MP (@lem7114978) (@lem0)). Qed.
Lemma lem7114980 : term142.
Proof. exact (@lem7114969 (@lem7114979)). Qed.
Lemma lem7114982 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7114983 : term33 = term34.
Proof. exact (@lem7114982 term24 term24). Qed.
Lemma lem7114984 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114985 : term36 = term24.
Proof. exact (EQ_MP (@lem7114984) (@lem940073)). Qed.
Lemma lem7114986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114987 : term34 = term30.
Proof. exact (MK_COMB (@lem7114986) (@lem7114985)). Qed.
Lemma lem7114988 : term33 = term30.
Proof. exact (TRANS (@lem7114983) (@lem7114987)). Qed.
Lemma lem7114990 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7114991 : term145 = term146.
Proof. exact (@lem7114990 term24 term24). Qed.
Lemma lem7114992 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7114993 : term36 = term24.
Proof. exact (EQ_MP (@lem7114992) (@lem940073)). Qed.
Lemma lem7114994 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7114995 : term34 = term30.
Proof. exact (MK_COMB (@lem7114994) (@lem7114993)). Qed.
Lemma lem7114996 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7114997 : term146 = term22.
Proof. exact (MK_COMB (@lem7114996) (@lem7114995)). Qed.
Lemma lem7114998 : term145 = term22.
Proof. exact (TRANS (@lem7114991) (@lem7114997)). Qed.
Lemma lem7114999 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7115000 : term147 = term135.
Proof. exact (MK_COMB (@lem7114999) (@lem7114998)). Qed.
Lemma lem7115001 : term148 = term137.
Proof. exact (MK_COMB (@lem7115000) (@lem7114988)). Qed.
Lemma lem7115003 (m : nat) : (term149 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7115004 : term137 = term15.
Proof. exact (@lem7115003 term24). Qed.
Lemma lem7115005 : term148 = term15.
Proof. exact (TRANS (@lem7115001) (@lem7115004)). Qed.
Lemma lem7115006 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115007 : term150 = term151.
Proof. exact (MK_COMB (@lem7115006) (@lem7115005)). Qed.
Lemma lem7115008 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem7115009 : term152 = term118.
Proof. exact (MK_COMB (@lem7115007) (@lem7115008)). Qed.
Lemma lem7115011 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115012 : term118 = term15.
Proof. exact (@lem7115011 term24). Qed.
Lemma lem7115013 : term152 = term15.
Proof. exact (TRANS (@lem7115009) (@lem7115012)). Qed.
Lemma lem7115015 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7115016 : term33 = term34.
Proof. exact (@lem7115015 term24 term24). Qed.
Lemma lem7115017 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115018 : term36 = term24.
Proof. exact (EQ_MP (@lem7115017) (@lem940073)). Qed.
Lemma lem7115019 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115020 : term34 = term30.
Proof. exact (MK_COMB (@lem7115019) (@lem7115018)). Qed.
Lemma lem7115021 : term33 = term30.
Proof. exact (TRANS (@lem7115016) (@lem7115020)). Qed.
Lemma lem7115022 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7115023 : term153 = term118.
Proof. exact (MK_COMB (@lem7115022) (@lem7115021)). Qed.
Lemma lem7115025 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115026 : term118 = term15.
Proof. exact (@lem7115025 term24). Qed.
Lemma lem7115027 : term153 = term15.
Proof. exact (TRANS (@lem7115023) (@lem7115026)). Qed.
Lemma lem7115028 : term15 = term153.
Proof. exact (SYM (@lem7115027)). Qed.
Lemma lem7115029 : term152 = term153.
Proof. exact (TRANS (@lem7115013) (@lem7115028)). Qed.
Lemma lem7115030 : term138 = term19.
Proof. exact (@lem7114980 (@lem7115029)). Qed.
Lemma lem7115031 : term137 = term19.
Proof. exact (TRANS (@lem7114946) (@lem7115030)). Qed.
Lemma lem7115033 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7115034 : term19 = term15.
Proof. exact (@lem7115033 term15). Qed.
Lemma lem7115035 : term137 = term15.
Proof. exact (TRANS (@lem7115031) (@lem7115034)). Qed.
Lemma lem7115036 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115037 : term154 = term151.
Proof. exact (MK_COMB (@lem7115036) (@lem7115035)). Qed.
Lemma lem7115038 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7115039 (x : real) : (term134 x) = (term155 x).
Proof. exact (MK_COMB (@lem7115037) (@lem7115038 x)). Qed.
Lemma lem7115040 (x : real) : (term174 x) = (term155 x).
Proof. exact (TRANS (@lem7114937 x) (@lem7115039 x)). Qed.
Lemma lem7115041 (x : real) : (term155 x) = term15.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7115042 (x : real) : (term174 x) = term15.
Proof. exact (TRANS (@lem7115040 x) (@lem7115041 x)). Qed.
Lemma lem7115043 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7115044 (x : real) : (term175 x) = term157.
Proof. exact (MK_COMB (@lem7115043) (@lem7115042 x)). Qed.
Lemma lem7115045 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7115046 (x : real) : (term173 x) = term158.
Proof. exact (MK_COMB (@lem7115044 x) (@lem7115045)). Qed.
Lemma lem7115047 (x : real) (h1 : term165 x) : term158.
Proof. exact (EQ_MP (@lem7115046 x) (@lem7114936 x h1)). Qed.
Lemma lem7115049 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7115050 : term158 = term159.
Proof. exact (@lem7115049 term15 term15). Qed.
Lemma lem7115052 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115053 : term15 = term19.
Proof. exact (@lem7115052 (NUMERAL 0)). Qed.
Lemma lem7115055 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115056 : term15 = term19.
Proof. exact (@lem7115055 (NUMERAL 0)). Qed.
Lemma lem7115057 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7115058 : term108 = term109.
Proof. exact (MK_COMB (@lem7115057) (@lem7115056)). Qed.
Lemma lem7115059 : term159 = term160.
Proof. exact (MK_COMB (@lem7115058) (@lem7115053)). Qed.
Lemma lem7115060 : term161.
Proof. exact (@lem1980255 term15 term30 term15 term30). Qed.
Lemma lem7115062 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115063 : term107 = term113.
Proof. exact (@lem7115062 (NUMERAL 0) term24). Qed.
Lemma lem7115064 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115065 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115066 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115065 h1) (fun h1 : term113 = True => @lem7115064)). Qed.
Lemma lem7115067 : term113 = True.
Proof. exact (EQ_MP (@lem7115066) (@lem7115064)). Qed.
Lemma lem7115068 : term107 = True.
Proof. exact (TRANS (@lem7115063) (@lem7115067)). Qed.
Lemma lem7115069 : True = term107.
Proof. exact (SYM (@lem7115068)). Qed.
Lemma lem7115070 : term107.
Proof. exact (EQ_MP (@lem7115069) (@lem0)). Qed.
Lemma lem7115071 : term162.
Proof. exact (@lem7115060 (@lem7115070)). Qed.
Lemma lem7115073 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115074 : term107 = term113.
Proof. exact (@lem7115073 (NUMERAL 0) term24). Qed.
Lemma lem7115075 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115076 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115077 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115076 h1) (fun h1 : term113 = True => @lem7115075)). Qed.
Lemma lem7115078 : term113 = True.
Proof. exact (EQ_MP (@lem7115077) (@lem7115075)). Qed.
Lemma lem7115079 : term107 = True.
Proof. exact (TRANS (@lem7115074) (@lem7115078)). Qed.
Lemma lem7115080 : True = term107.
Proof. exact (SYM (@lem7115079)). Qed.
Lemma lem7115081 : term107.
Proof. exact (EQ_MP (@lem7115080) (@lem0)). Qed.
Lemma lem7115082 : term160 = term163.
Proof. exact (@lem7115071 (@lem7115081)). Qed.
Lemma lem7115084 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115085 : term118 = term15.
Proof. exact (@lem7115084 term24). Qed.
Lemma lem7115087 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115088 : term118 = term15.
Proof. exact (@lem7115087 term24). Qed.
Lemma lem7115089 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7115090 : term119 = term108.
Proof. exact (MK_COMB (@lem7115089) (@lem7115088)). Qed.
Lemma lem7115091 : term163 = term159.
Proof. exact (MK_COMB (@lem7115090) (@lem7115085)). Qed.
Lemma lem7115093 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115094 : term159 = term164.
Proof. exact (@lem7115093 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7115095 : term164 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7115096 : term159 = False.
Proof. exact (TRANS (@lem7115094) (@lem7115095)). Qed.
Lemma lem7115097 : term163 = False.
Proof. exact (TRANS (@lem7115091) (@lem7115096)). Qed.
Lemma lem7115098 : term160 = False.
Proof. exact (TRANS (@lem7115082) (@lem7115097)). Qed.
Lemma lem7115099 : term159 = False.
Proof. exact (TRANS (@lem7115059) (@lem7115098)). Qed.
Lemma lem7115100 : term158 = False.
Proof. exact (TRANS (@lem7115050) (@lem7115099)). Qed.
Lemma lem7115101 (x : real) (h1 : term165 x) : False.
Proof. exact (EQ_MP (@lem7115100) (@lem7115047 x h1)). Qed.
Lemma lem7115102 (x : real) (h1 : term102 x) : False.
Proof. exact (or_elim (@lem7114581 x h1) (fun h0 : term105 x => @lem7114841 x h0) (fun h0 : term165 x => @lem7115101 x h0)). Qed.
Lemma lem7115103 (x : real) (h1 : term101 x) : term101 x.
Proof. exact (h1). Qed.
Lemma lem7115104 (x : real) (h1 : term176 x) : term176 x.
Proof. exact (h1). Qed.
Lemma lem7115105 (x : real) (h1 : term176 x) : (term45 x) = term15.
Proof. exact (proj2 (@lem7115104 x h1)). Qed.
Lemma lem7115106 (x : real) (h1 : term176 x) : term70 x.
Proof. exact (proj1 (@lem7115104 x h1)). Qed.
Lemma lem7115108 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7115109 : term106 = term107.
Proof. exact (@lem7115108 term15 term30). Qed.
Lemma lem7115111 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115112 : term30 = term63.
Proof. exact (@lem7115111 term24). Qed.
Lemma lem7115114 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115115 : term15 = term19.
Proof. exact (@lem7115114 (NUMERAL 0)). Qed.
Lemma lem7115116 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7115117 : term108 = term109.
Proof. exact (MK_COMB (@lem7115116) (@lem7115115)). Qed.
Lemma lem7115118 : term107 = term110.
Proof. exact (MK_COMB (@lem7115117) (@lem7115112)). Qed.
Lemma lem7115119 : term111.
Proof. exact (@lem1980255 term15 term30 term30 term30). Qed.
Lemma lem7115121 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115122 : term107 = term113.
Proof. exact (@lem7115121 (NUMERAL 0) term24). Qed.
Lemma lem7115123 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115124 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115125 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115124 h1) (fun h1 : term113 = True => @lem7115123)). Qed.
Lemma lem7115126 : term113 = True.
Proof. exact (EQ_MP (@lem7115125) (@lem7115123)). Qed.
Lemma lem7115127 : term107 = True.
Proof. exact (TRANS (@lem7115122) (@lem7115126)). Qed.
Lemma lem7115128 : True = term107.
Proof. exact (SYM (@lem7115127)). Qed.
Lemma lem7115129 : term107.
Proof. exact (EQ_MP (@lem7115128) (@lem0)). Qed.
Lemma lem7115130 : term115.
Proof. exact (@lem7115119 (@lem7115129)). Qed.
Lemma lem7115132 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115133 : term107 = term113.
Proof. exact (@lem7115132 (NUMERAL 0) term24). Qed.
Lemma lem7115134 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115135 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115136 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115135 h1) (fun h1 : term113 = True => @lem7115134)). Qed.
Lemma lem7115137 : term113 = True.
Proof. exact (EQ_MP (@lem7115136) (@lem7115134)). Qed.
Lemma lem7115138 : term107 = True.
Proof. exact (TRANS (@lem7115133) (@lem7115137)). Qed.
Lemma lem7115139 : True = term107.
Proof. exact (SYM (@lem7115138)). Qed.
Lemma lem7115140 : term107.
Proof. exact (EQ_MP (@lem7115139) (@lem0)). Qed.
Lemma lem7115141 : term110 = term116.
Proof. exact (@lem7115130 (@lem7115140)). Qed.
Lemma lem7115143 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7115144 : term33 = term34.
Proof. exact (@lem7115143 term24 term24). Qed.
Lemma lem7115145 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115146 : term36 = term24.
Proof. exact (EQ_MP (@lem7115145) (@lem940073)). Qed.
Lemma lem7115147 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115148 : term34 = term30.
Proof. exact (MK_COMB (@lem7115147) (@lem7115146)). Qed.
Lemma lem7115149 : term33 = term30.
Proof. exact (TRANS (@lem7115144) (@lem7115148)). Qed.
Lemma lem7115151 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115152 : term118 = term15.
Proof. exact (@lem7115151 term24). Qed.
Lemma lem7115153 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7115154 : term119 = term108.
Proof. exact (MK_COMB (@lem7115153) (@lem7115152)). Qed.
Lemma lem7115155 : term116 = term107.
Proof. exact (MK_COMB (@lem7115154) (@lem7115149)). Qed.
Lemma lem7115157 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115158 : term107 = term113.
Proof. exact (@lem7115157 (NUMERAL 0) term24). Qed.
Lemma lem7115159 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115160 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115161 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115160 h1) (fun h1 : term113 = True => @lem7115159)). Qed.
Lemma lem7115162 : term113 = True.
Proof. exact (EQ_MP (@lem7115161) (@lem7115159)). Qed.
Lemma lem7115163 : term107 = True.
Proof. exact (TRANS (@lem7115158) (@lem7115162)). Qed.
Lemma lem7115164 : term116 = True.
Proof. exact (TRANS (@lem7115155) (@lem7115163)). Qed.
Lemma lem7115165 : term110 = True.
Proof. exact (TRANS (@lem7115141) (@lem7115164)). Qed.
Lemma lem7115166 : term107 = True.
Proof. exact (TRANS (@lem7115118) (@lem7115165)). Qed.
Lemma lem7115167 : term106 = True.
Proof. exact (TRANS (@lem7115109) (@lem7115166)). Qed.
Lemma lem7115168 : True = term106.
Proof. exact (SYM (@lem7115167)). Qed.
Lemma lem7115169 : term106.
Proof. exact (EQ_MP (@lem7115168) (@lem0)). Qed.
Lemma lem7115170 (x : real) (h1 : term176 x) : term166 x.
Proof. exact (conj (@lem7115169) (@lem7115106 x h1)). Qed.
Lemma lem7115172 (x : real) (y : real) : term121 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7115173 (x : real) : term167 x.
Proof. exact (@lem7115172 term30 x). Qed.
Lemma lem7115174 (x : real) (h1 : term176 x) : term168 x.
Proof. exact (@lem7115173 x (@lem7115170 x h1)). Qed.
Lemma lem7115175 (x : real) : (term66 x) = x.
Proof. exact (@lem1982733 x). Qed.
Lemma lem7115176 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7115177 (x : real) : (term169 x) = (real_gt x).
Proof. exact (MK_COMB (@lem7115176) (@lem7115175 x)). Qed.
Lemma lem7115178 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7115179 (x : real) : (term168 x) = (term70 x).
Proof. exact (MK_COMB (@lem7115177 x) (@lem7115178)). Qed.
Lemma lem7115180 (x : real) (h1 : term176 x) : term70 x.
Proof. exact (EQ_MP (@lem7115179 x) (@lem7115174 x h1)). Qed.
Lemma lem7115182 (y : real) : term126 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7115183 (x : real) : term177 x.
Proof. exact (@lem7115182 (term45 x)). Qed.
Lemma lem7115184 (x : real) (h1 : term176 x) : term178 x.
Proof. exact (@lem7115183 x (@lem7115105 x h1)). Qed.
Lemma lem7115185 (x : real) (h1 : term176 x) : term179 x.
Proof. exact (@lem7115184 x h1 term30). Qed.
Lemma lem7115186 (x : real) : (term179 x) = ((term124 x) = term15).
Proof. exact (eq_refl (term179 x)). Qed.
Lemma lem7115187 (x : real) (h1 : term176 x) : (term124 x) = term15.
Proof. exact (EQ_MP (@lem7115186 x) (@lem7115185 x h1)). Qed.
Lemma lem7115188 (x : real) : (term124 x) = (term45 x).
Proof. exact (@lem1982733 (term45 x)). Qed.
Lemma lem7115189 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7115190 (x : real) : (term180 x) = (term93 x).
Proof. exact (MK_COMB (@lem7115189) (@lem7115188 x)). Qed.
Lemma lem7115191 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7115192 (x : real) : ((term124 x) = term15) = ((term45 x) = term15).
Proof. exact (MK_COMB (@lem7115190 x) (@lem7115191)). Qed.
Lemma lem7115193 (x : real) (h1 : term176 x) : (term45 x) = term15.
Proof. exact (EQ_MP (@lem7115192 x) (@lem7115187 x h1)). Qed.
Lemma lem7115194 (x : real) (h1 : term176 x) : term171 x.
Proof. exact (conj (@lem7115193 x h1) (@lem7115180 x h1)). Qed.
Lemma lem7115196 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem7115197 (x : real) : term172 x.
Proof. exact (@lem7115196 (term45 x) x). Qed.
Lemma lem7115198 (x : real) (h1 : term176 x) : term173 x.
Proof. exact (@lem7115197 x (@lem7115194 x h1)). Qed.
Lemma lem7115199 (x : real) : (term174 x) = (term134 x).
Proof. exact (@lem1982713 term22 x). Qed.
Lemma lem7115201 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115202 : term30 = term63.
Proof. exact (@lem7115201 term24). Qed.
Lemma lem7115204 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7115205 : term22 = term23.
Proof. exact (@lem7115204 term24). Qed.
Lemma lem7115206 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7115207 : term135 = term136.
Proof. exact (MK_COMB (@lem7115206) (@lem7115205)). Qed.
Lemma lem7115208 : term137 = term138.
Proof. exact (MK_COMB (@lem7115207) (@lem7115202)). Qed.
Lemma lem7115209 : term139.
Proof. exact (@lem1981473 term22 term30 term30 term30 term15 term30). Qed.
Lemma lem7115211 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115212 : term107 = term113.
Proof. exact (@lem7115211 (NUMERAL 0) term24). Qed.
Lemma lem7115213 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115214 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115215 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115214 h1) (fun h1 : term113 = True => @lem7115213)). Qed.
Lemma lem7115216 : term113 = True.
Proof. exact (EQ_MP (@lem7115215) (@lem7115213)). Qed.
Lemma lem7115217 : term107 = True.
Proof. exact (TRANS (@lem7115212) (@lem7115216)). Qed.
Lemma lem7115218 : True = term107.
Proof. exact (SYM (@lem7115217)). Qed.
Lemma lem7115219 : term107.
Proof. exact (EQ_MP (@lem7115218) (@lem0)). Qed.
Lemma lem7115220 : term140.
Proof. exact (@lem7115209 (@lem7115219)). Qed.
Lemma lem7115222 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115223 : term107 = term113.
Proof. exact (@lem7115222 (NUMERAL 0) term24). Qed.
Lemma lem7115224 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115225 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115226 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115225 h1) (fun h1 : term113 = True => @lem7115224)). Qed.
Lemma lem7115227 : term113 = True.
Proof. exact (EQ_MP (@lem7115226) (@lem7115224)). Qed.
Lemma lem7115228 : term107 = True.
Proof. exact (TRANS (@lem7115223) (@lem7115227)). Qed.
Lemma lem7115229 : True = term107.
Proof. exact (SYM (@lem7115228)). Qed.
Lemma lem7115230 : term107.
Proof. exact (EQ_MP (@lem7115229) (@lem0)). Qed.
Lemma lem7115231 : term141.
Proof. exact (@lem7115220 (@lem7115230)). Qed.
Lemma lem7115233 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115234 : term107 = term113.
Proof. exact (@lem7115233 (NUMERAL 0) term24). Qed.
Lemma lem7115235 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115236 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115237 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115236 h1) (fun h1 : term113 = True => @lem7115235)). Qed.
Lemma lem7115238 : term113 = True.
Proof. exact (EQ_MP (@lem7115237) (@lem7115235)). Qed.
Lemma lem7115239 : term107 = True.
Proof. exact (TRANS (@lem7115234) (@lem7115238)). Qed.
Lemma lem7115240 : True = term107.
Proof. exact (SYM (@lem7115239)). Qed.
Lemma lem7115241 : term107.
Proof. exact (EQ_MP (@lem7115240) (@lem0)). Qed.
Lemma lem7115242 : term142.
Proof. exact (@lem7115231 (@lem7115241)). Qed.
Lemma lem7115244 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7115245 : term33 = term34.
Proof. exact (@lem7115244 term24 term24). Qed.
Lemma lem7115246 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115247 : term36 = term24.
Proof. exact (EQ_MP (@lem7115246) (@lem940073)). Qed.
Lemma lem7115248 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115249 : term34 = term30.
Proof. exact (MK_COMB (@lem7115248) (@lem7115247)). Qed.
Lemma lem7115250 : term33 = term30.
Proof. exact (TRANS (@lem7115245) (@lem7115249)). Qed.
Lemma lem7115252 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7115253 : term145 = term146.
Proof. exact (@lem7115252 term24 term24). Qed.
Lemma lem7115254 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115255 : term36 = term24.
Proof. exact (EQ_MP (@lem7115254) (@lem940073)). Qed.
Lemma lem7115256 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115257 : term34 = term30.
Proof. exact (MK_COMB (@lem7115256) (@lem7115255)). Qed.
Lemma lem7115258 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7115259 : term146 = term22.
Proof. exact (MK_COMB (@lem7115258) (@lem7115257)). Qed.
Lemma lem7115260 : term145 = term22.
Proof. exact (TRANS (@lem7115253) (@lem7115259)). Qed.
Lemma lem7115261 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7115262 : term147 = term135.
Proof. exact (MK_COMB (@lem7115261) (@lem7115260)). Qed.
Lemma lem7115263 : term148 = term137.
Proof. exact (MK_COMB (@lem7115262) (@lem7115250)). Qed.
Lemma lem7115265 (m : nat) : (term149 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7115266 : term137 = term15.
Proof. exact (@lem7115265 term24). Qed.
Lemma lem7115267 : term148 = term15.
Proof. exact (TRANS (@lem7115263) (@lem7115266)). Qed.
Lemma lem7115268 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115269 : term150 = term151.
Proof. exact (MK_COMB (@lem7115268) (@lem7115267)). Qed.
Lemma lem7115270 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem7115271 : term152 = term118.
Proof. exact (MK_COMB (@lem7115269) (@lem7115270)). Qed.
Lemma lem7115273 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115274 : term118 = term15.
Proof. exact (@lem7115273 term24). Qed.
Lemma lem7115275 : term152 = term15.
Proof. exact (TRANS (@lem7115271) (@lem7115274)). Qed.
Lemma lem7115277 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7115278 : term33 = term34.
Proof. exact (@lem7115277 term24 term24). Qed.
Lemma lem7115279 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115280 : term36 = term24.
Proof. exact (EQ_MP (@lem7115279) (@lem940073)). Qed.
Lemma lem7115281 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115282 : term34 = term30.
Proof. exact (MK_COMB (@lem7115281) (@lem7115280)). Qed.
Lemma lem7115283 : term33 = term30.
Proof. exact (TRANS (@lem7115278) (@lem7115282)). Qed.
Lemma lem7115284 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7115285 : term153 = term118.
Proof. exact (MK_COMB (@lem7115284) (@lem7115283)). Qed.
Lemma lem7115287 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115288 : term118 = term15.
Proof. exact (@lem7115287 term24). Qed.
Lemma lem7115289 : term153 = term15.
Proof. exact (TRANS (@lem7115285) (@lem7115288)). Qed.
Lemma lem7115290 : term15 = term153.
Proof. exact (SYM (@lem7115289)). Qed.
Lemma lem7115291 : term152 = term153.
Proof. exact (TRANS (@lem7115275) (@lem7115290)). Qed.
Lemma lem7115292 : term138 = term19.
Proof. exact (@lem7115242 (@lem7115291)). Qed.
Lemma lem7115293 : term137 = term19.
Proof. exact (TRANS (@lem7115208) (@lem7115292)). Qed.
Lemma lem7115295 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7115296 : term19 = term15.
Proof. exact (@lem7115295 term15). Qed.
Lemma lem7115297 : term137 = term15.
Proof. exact (TRANS (@lem7115293) (@lem7115296)). Qed.
Lemma lem7115298 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115299 : term154 = term151.
Proof. exact (MK_COMB (@lem7115298) (@lem7115297)). Qed.
Lemma lem7115300 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7115301 (x : real) : (term134 x) = (term155 x).
Proof. exact (MK_COMB (@lem7115299) (@lem7115300 x)). Qed.
Lemma lem7115302 (x : real) : (term174 x) = (term155 x).
Proof. exact (TRANS (@lem7115199 x) (@lem7115301 x)). Qed.
Lemma lem7115303 (x : real) : (term155 x) = term15.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7115304 (x : real) : (term174 x) = term15.
Proof. exact (TRANS (@lem7115302 x) (@lem7115303 x)). Qed.
Lemma lem7115305 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7115306 (x : real) : (term175 x) = term157.
Proof. exact (MK_COMB (@lem7115305) (@lem7115304 x)). Qed.
Lemma lem7115307 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7115308 (x : real) : (term173 x) = term158.
Proof. exact (MK_COMB (@lem7115306 x) (@lem7115307)). Qed.
Lemma lem7115309 (x : real) (h1 : term176 x) : term158.
Proof. exact (EQ_MP (@lem7115308 x) (@lem7115198 x h1)). Qed.
Lemma lem7115311 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7115312 : term158 = term159.
Proof. exact (@lem7115311 term15 term15). Qed.
Lemma lem7115314 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115315 : term15 = term19.
Proof. exact (@lem7115314 (NUMERAL 0)). Qed.
Lemma lem7115317 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115318 : term15 = term19.
Proof. exact (@lem7115317 (NUMERAL 0)). Qed.
Lemma lem7115319 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7115320 : term108 = term109.
Proof. exact (MK_COMB (@lem7115319) (@lem7115318)). Qed.
Lemma lem7115321 : term159 = term160.
Proof. exact (MK_COMB (@lem7115320) (@lem7115315)). Qed.
Lemma lem7115322 : term161.
Proof. exact (@lem1980255 term15 term30 term15 term30). Qed.
Lemma lem7115324 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115325 : term107 = term113.
Proof. exact (@lem7115324 (NUMERAL 0) term24). Qed.
Lemma lem7115326 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115327 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115328 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115327 h1) (fun h1 : term113 = True => @lem7115326)). Qed.
Lemma lem7115329 : term113 = True.
Proof. exact (EQ_MP (@lem7115328) (@lem7115326)). Qed.
Lemma lem7115330 : term107 = True.
Proof. exact (TRANS (@lem7115325) (@lem7115329)). Qed.
Lemma lem7115331 : True = term107.
Proof. exact (SYM (@lem7115330)). Qed.
Lemma lem7115332 : term107.
Proof. exact (EQ_MP (@lem7115331) (@lem0)). Qed.
Lemma lem7115333 : term162.
Proof. exact (@lem7115322 (@lem7115332)). Qed.
Lemma lem7115335 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115336 : term107 = term113.
Proof. exact (@lem7115335 (NUMERAL 0) term24). Qed.
Lemma lem7115337 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115338 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115339 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115338 h1) (fun h1 : term113 = True => @lem7115337)). Qed.
Lemma lem7115340 : term113 = True.
Proof. exact (EQ_MP (@lem7115339) (@lem7115337)). Qed.
Lemma lem7115341 : term107 = True.
Proof. exact (TRANS (@lem7115336) (@lem7115340)). Qed.
Lemma lem7115342 : True = term107.
Proof. exact (SYM (@lem7115341)). Qed.
Lemma lem7115343 : term107.
Proof. exact (EQ_MP (@lem7115342) (@lem0)). Qed.
Lemma lem7115344 : term160 = term163.
Proof. exact (@lem7115333 (@lem7115343)). Qed.
Lemma lem7115346 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115347 : term118 = term15.
Proof. exact (@lem7115346 term24). Qed.
Lemma lem7115349 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115350 : term118 = term15.
Proof. exact (@lem7115349 term24). Qed.
Lemma lem7115351 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7115352 : term119 = term108.
Proof. exact (MK_COMB (@lem7115351) (@lem7115350)). Qed.
Lemma lem7115353 : term163 = term159.
Proof. exact (MK_COMB (@lem7115352) (@lem7115347)). Qed.
Lemma lem7115355 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115356 : term159 = term164.
Proof. exact (@lem7115355 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7115357 : term164 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7115358 : term159 = False.
Proof. exact (TRANS (@lem7115356) (@lem7115357)). Qed.
Lemma lem7115359 : term163 = False.
Proof. exact (TRANS (@lem7115353) (@lem7115358)). Qed.
Lemma lem7115360 : term160 = False.
Proof. exact (TRANS (@lem7115344) (@lem7115359)). Qed.
Lemma lem7115361 : term159 = False.
Proof. exact (TRANS (@lem7115321) (@lem7115360)). Qed.
Lemma lem7115362 : term158 = False.
Proof. exact (TRANS (@lem7115312) (@lem7115361)). Qed.
Lemma lem7115363 (x : real) (h1 : term176 x) : False.
Proof. exact (EQ_MP (@lem7115362) (@lem7115309 x h1)). Qed.
Lemma lem7115364 (x : real) (h1 : term181 x) : term181 x.
Proof. exact (h1). Qed.
Lemma lem7115365 (x : real) (h1 : term181 x) : (term45 x) = term15.
Proof. exact (proj2 (@lem7115364 x h1)). Qed.
Lemma lem7115366 (x : real) (h1 : term181 x) : term74 x.
Proof. exact (proj1 (@lem7115364 x h1)). Qed.
Lemma lem7115368 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7115369 : term106 = term107.
Proof. exact (@lem7115368 term15 term30). Qed.
Lemma lem7115371 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115372 : term30 = term63.
Proof. exact (@lem7115371 term24). Qed.
Lemma lem7115374 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115375 : term15 = term19.
Proof. exact (@lem7115374 (NUMERAL 0)). Qed.
Lemma lem7115376 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7115377 : term108 = term109.
Proof. exact (MK_COMB (@lem7115376) (@lem7115375)). Qed.
Lemma lem7115378 : term107 = term110.
Proof. exact (MK_COMB (@lem7115377) (@lem7115372)). Qed.
Lemma lem7115379 : term111.
Proof. exact (@lem1980255 term15 term30 term30 term30). Qed.
Lemma lem7115381 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115382 : term107 = term113.
Proof. exact (@lem7115381 (NUMERAL 0) term24). Qed.
Lemma lem7115383 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115384 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115385 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115384 h1) (fun h1 : term113 = True => @lem7115383)). Qed.
Lemma lem7115386 : term113 = True.
Proof. exact (EQ_MP (@lem7115385) (@lem7115383)). Qed.
Lemma lem7115387 : term107 = True.
Proof. exact (TRANS (@lem7115382) (@lem7115386)). Qed.
Lemma lem7115388 : True = term107.
Proof. exact (SYM (@lem7115387)). Qed.
Lemma lem7115389 : term107.
Proof. exact (EQ_MP (@lem7115388) (@lem0)). Qed.
Lemma lem7115390 : term115.
Proof. exact (@lem7115379 (@lem7115389)). Qed.
Lemma lem7115392 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115393 : term107 = term113.
Proof. exact (@lem7115392 (NUMERAL 0) term24). Qed.
Lemma lem7115394 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115395 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115396 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115395 h1) (fun h1 : term113 = True => @lem7115394)). Qed.
Lemma lem7115397 : term113 = True.
Proof. exact (EQ_MP (@lem7115396) (@lem7115394)). Qed.
Lemma lem7115398 : term107 = True.
Proof. exact (TRANS (@lem7115393) (@lem7115397)). Qed.
Lemma lem7115399 : True = term107.
Proof. exact (SYM (@lem7115398)). Qed.
Lemma lem7115400 : term107.
Proof. exact (EQ_MP (@lem7115399) (@lem0)). Qed.
Lemma lem7115401 : term110 = term116.
Proof. exact (@lem7115390 (@lem7115400)). Qed.
Lemma lem7115403 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7115404 : term33 = term34.
Proof. exact (@lem7115403 term24 term24). Qed.
Lemma lem7115405 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115406 : term36 = term24.
Proof. exact (EQ_MP (@lem7115405) (@lem940073)). Qed.
Lemma lem7115407 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115408 : term34 = term30.
Proof. exact (MK_COMB (@lem7115407) (@lem7115406)). Qed.
Lemma lem7115409 : term33 = term30.
Proof. exact (TRANS (@lem7115404) (@lem7115408)). Qed.
Lemma lem7115411 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115412 : term118 = term15.
Proof. exact (@lem7115411 term24). Qed.
Lemma lem7115413 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7115414 : term119 = term108.
Proof. exact (MK_COMB (@lem7115413) (@lem7115412)). Qed.
Lemma lem7115415 : term116 = term107.
Proof. exact (MK_COMB (@lem7115414) (@lem7115409)). Qed.
Lemma lem7115417 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115418 : term107 = term113.
Proof. exact (@lem7115417 (NUMERAL 0) term24). Qed.
Lemma lem7115419 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115420 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115421 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115420 h1) (fun h1 : term113 = True => @lem7115419)). Qed.
Lemma lem7115422 : term113 = True.
Proof. exact (EQ_MP (@lem7115421) (@lem7115419)). Qed.
Lemma lem7115423 : term107 = True.
Proof. exact (TRANS (@lem7115418) (@lem7115422)). Qed.
Lemma lem7115424 : term116 = True.
Proof. exact (TRANS (@lem7115415) (@lem7115423)). Qed.
Lemma lem7115425 : term110 = True.
Proof. exact (TRANS (@lem7115401) (@lem7115424)). Qed.
Lemma lem7115426 : term107 = True.
Proof. exact (TRANS (@lem7115378) (@lem7115425)). Qed.
Lemma lem7115427 : term106 = True.
Proof. exact (TRANS (@lem7115369) (@lem7115426)). Qed.
Lemma lem7115428 : True = term106.
Proof. exact (SYM (@lem7115427)). Qed.
Lemma lem7115429 : term106.
Proof. exact (EQ_MP (@lem7115428) (@lem0)). Qed.
Lemma lem7115430 (x : real) (h1 : term181 x) : term120 x.
Proof. exact (conj (@lem7115429) (@lem7115366 x h1)). Qed.
Lemma lem7115432 (x : real) (y : real) : term121 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7115433 (x : real) : term122 x.
Proof. exact (@lem7115432 term30 (term45 x)). Qed.
Lemma lem7115434 (x : real) (h1 : term181 x) : term123 x.
Proof. exact (@lem7115433 x (@lem7115430 x h1)). Qed.
Lemma lem7115435 (x : real) : (term124 x) = (term45 x).
Proof. exact (@lem1982733 (term45 x)). Qed.
Lemma lem7115436 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7115437 (x : real) : (term125 x) = (term72 x).
Proof. exact (MK_COMB (@lem7115436) (@lem7115435 x)). Qed.
Lemma lem7115438 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7115439 (x : real) : (term123 x) = (term74 x).
Proof. exact (MK_COMB (@lem7115437 x) (@lem7115438)). Qed.
Lemma lem7115440 (x : real) (h1 : term181 x) : term74 x.
Proof. exact (EQ_MP (@lem7115439 x) (@lem7115434 x h1)). Qed.
Lemma lem7115442 (y : real) : term126 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7115443 (x : real) : term177 x.
Proof. exact (@lem7115442 (term45 x)). Qed.
Lemma lem7115444 (x : real) (h1 : term181 x) : term178 x.
Proof. exact (@lem7115443 x (@lem7115365 x h1)). Qed.
Lemma lem7115445 (x : real) (h1 : term181 x) : term182 x.
Proof. exact (@lem7115444 x h1 term22). Qed.
Lemma lem7115446 (x : real) : (term182 x) = ((term55 x) = term15).
Proof. exact (eq_refl (term182 x)). Qed.
Lemma lem7115447 (x : real) (h1 : term181 x) : (term55 x) = term15.
Proof. exact (EQ_MP (@lem7115446 x) (@lem7115445 x h1)). Qed.
Lemma lem7115448 (x : real) : (term55 x) = (term56 x).
Proof. exact (@lem1982749 term22 term22 x). Qed.
Lemma lem7115450 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7115451 : term22 = term23.
Proof. exact (@lem7115450 term24). Qed.
Lemma lem7115453 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7115454 : term22 = term23.
Proof. exact (@lem7115453 term24). Qed.
Lemma lem7115455 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115456 : term25 = term26.
Proof. exact (MK_COMB (@lem7115455) (@lem7115454)). Qed.
Lemma lem7115457 : term57 = term58.
Proof. exact (MK_COMB (@lem7115456) (@lem7115451)). Qed.
Lemma lem7115458 : term58 = term59.
Proof. exact (@lem1981613 term22 term22 term30 term30). Qed.
Lemma lem7115460 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7115461 : term33 = term34.
Proof. exact (@lem7115460 term24 term24). Qed.
Lemma lem7115462 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115463 : term36 = term24.
Proof. exact (EQ_MP (@lem7115462) (@lem940073)). Qed.
Lemma lem7115464 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115465 : term34 = term30.
Proof. exact (MK_COMB (@lem7115464) (@lem7115463)). Qed.
Lemma lem7115466 : term33 = term30.
Proof. exact (TRANS (@lem7115461) (@lem7115465)). Qed.
Lemma lem7115468 (m : nat) (n : nat) : (term60 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7115469 : term57 = term34.
Proof. exact (@lem7115468 term24 term24). Qed.
Lemma lem7115470 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115471 : term36 = term24.
Proof. exact (EQ_MP (@lem7115470) (@lem940073)). Qed.
Lemma lem7115472 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115473 : term34 = term30.
Proof. exact (MK_COMB (@lem7115472) (@lem7115471)). Qed.
Lemma lem7115474 : term57 = term30.
Proof. exact (TRANS (@lem7115469) (@lem7115473)). Qed.
Lemma lem7115475 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7115476 : term61 = term62.
Proof. exact (MK_COMB (@lem7115475) (@lem7115474)). Qed.
Lemma lem7115477 : term59 = term63.
Proof. exact (MK_COMB (@lem7115476) (@lem7115466)). Qed.
Lemma lem7115478 : term58 = term63.
Proof. exact (TRANS (@lem7115458) (@lem7115477)). Qed.
Lemma lem7115479 : term57 = term63.
Proof. exact (TRANS (@lem7115457) (@lem7115478)). Qed.
Lemma lem7115481 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7115482 : term63 = term30.
Proof. exact (@lem7115481 term30). Qed.
Lemma lem7115483 : term57 = term30.
Proof. exact (TRANS (@lem7115479) (@lem7115482)). Qed.
Lemma lem7115484 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115485 : term64 = term65.
Proof. exact (MK_COMB (@lem7115484) (@lem7115483)). Qed.
Lemma lem7115486 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7115487 (x : real) : (term56 x) = (term66 x).
Proof. exact (MK_COMB (@lem7115485) (@lem7115486 x)). Qed.
Lemma lem7115488 (x : real) : (term55 x) = (term66 x).
Proof. exact (TRANS (@lem7115448 x) (@lem7115487 x)). Qed.
Lemma lem7115489 (x : real) : (term66 x) = x.
Proof. exact (@lem1982709 x). Qed.
Lemma lem7115490 (x : real) : (term55 x) = x.
Proof. exact (TRANS (@lem7115488 x) (@lem7115489 x)). Qed.
Lemma lem7115491 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7115492 (x : real) : (term183 x) = (@eq real x).
Proof. exact (MK_COMB (@lem7115491) (@lem7115490 x)). Qed.
Lemma lem7115493 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7115494 (x : real) : ((term55 x) = term15) = (x = term15).
Proof. exact (MK_COMB (@lem7115492 x) (@lem7115493)). Qed.
Lemma lem7115495 (x : real) (h1 : term181 x) : x = term15.
Proof. exact (EQ_MP (@lem7115494 x) (@lem7115447 x h1)). Qed.
Lemma lem7115496 (x : real) (h1 : term181 x) : term105 x.
Proof. exact (conj (@lem7115495 x h1) (@lem7115440 x h1)). Qed.
Lemma lem7115498 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1988338 x y)). Qed.
Lemma lem7115499 (x : real) : term131 x.
Proof. exact (@lem7115498 x (term45 x)). Qed.
Lemma lem7115500 (x : real) (h1 : term181 x) : term132 x.
Proof. exact (@lem7115499 x (@lem7115496 x h1)). Qed.
Lemma lem7115501 (x : real) : (term133 x) = (term134 x).
Proof. exact (@lem1982715 term22 x). Qed.
Lemma lem7115503 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115504 : term30 = term63.
Proof. exact (@lem7115503 term24). Qed.
Lemma lem7115506 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7115507 : term22 = term23.
Proof. exact (@lem7115506 term24). Qed.
Lemma lem7115508 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7115509 : term135 = term136.
Proof. exact (MK_COMB (@lem7115508) (@lem7115507)). Qed.
Lemma lem7115510 : term137 = term138.
Proof. exact (MK_COMB (@lem7115509) (@lem7115504)). Qed.
Lemma lem7115511 : term139.
Proof. exact (@lem1981473 term22 term30 term30 term30 term15 term30). Qed.
Lemma lem7115513 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115514 : term107 = term113.
Proof. exact (@lem7115513 (NUMERAL 0) term24). Qed.
Lemma lem7115515 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115516 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115517 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115516 h1) (fun h1 : term113 = True => @lem7115515)). Qed.
Lemma lem7115518 : term113 = True.
Proof. exact (EQ_MP (@lem7115517) (@lem7115515)). Qed.
Lemma lem7115519 : term107 = True.
Proof. exact (TRANS (@lem7115514) (@lem7115518)). Qed.
Lemma lem7115520 : True = term107.
Proof. exact (SYM (@lem7115519)). Qed.
Lemma lem7115521 : term107.
Proof. exact (EQ_MP (@lem7115520) (@lem0)). Qed.
Lemma lem7115522 : term140.
Proof. exact (@lem7115511 (@lem7115521)). Qed.
Lemma lem7115524 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115525 : term107 = term113.
Proof. exact (@lem7115524 (NUMERAL 0) term24). Qed.
Lemma lem7115526 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115527 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115528 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115527 h1) (fun h1 : term113 = True => @lem7115526)). Qed.
Lemma lem7115529 : term113 = True.
Proof. exact (EQ_MP (@lem7115528) (@lem7115526)). Qed.
Lemma lem7115530 : term107 = True.
Proof. exact (TRANS (@lem7115525) (@lem7115529)). Qed.
Lemma lem7115531 : True = term107.
Proof. exact (SYM (@lem7115530)). Qed.
Lemma lem7115532 : term107.
Proof. exact (EQ_MP (@lem7115531) (@lem0)). Qed.
Lemma lem7115533 : term141.
Proof. exact (@lem7115522 (@lem7115532)). Qed.
Lemma lem7115535 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115536 : term107 = term113.
Proof. exact (@lem7115535 (NUMERAL 0) term24). Qed.
Lemma lem7115537 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115538 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115539 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115538 h1) (fun h1 : term113 = True => @lem7115537)). Qed.
Lemma lem7115540 : term113 = True.
Proof. exact (EQ_MP (@lem7115539) (@lem7115537)). Qed.
Lemma lem7115541 : term107 = True.
Proof. exact (TRANS (@lem7115536) (@lem7115540)). Qed.
Lemma lem7115542 : True = term107.
Proof. exact (SYM (@lem7115541)). Qed.
Lemma lem7115543 : term107.
Proof. exact (EQ_MP (@lem7115542) (@lem0)). Qed.
Lemma lem7115544 : term142.
Proof. exact (@lem7115533 (@lem7115543)). Qed.
Lemma lem7115546 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7115547 : term33 = term34.
Proof. exact (@lem7115546 term24 term24). Qed.
Lemma lem7115548 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115549 : term36 = term24.
Proof. exact (EQ_MP (@lem7115548) (@lem940073)). Qed.
Lemma lem7115550 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115551 : term34 = term30.
Proof. exact (MK_COMB (@lem7115550) (@lem7115549)). Qed.
Lemma lem7115552 : term33 = term30.
Proof. exact (TRANS (@lem7115547) (@lem7115551)). Qed.
Lemma lem7115554 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7115555 : term145 = term146.
Proof. exact (@lem7115554 term24 term24). Qed.
Lemma lem7115556 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115557 : term36 = term24.
Proof. exact (EQ_MP (@lem7115556) (@lem940073)). Qed.
Lemma lem7115558 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115559 : term34 = term30.
Proof. exact (MK_COMB (@lem7115558) (@lem7115557)). Qed.
Lemma lem7115560 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7115561 : term146 = term22.
Proof. exact (MK_COMB (@lem7115560) (@lem7115559)). Qed.
Lemma lem7115562 : term145 = term22.
Proof. exact (TRANS (@lem7115555) (@lem7115561)). Qed.
Lemma lem7115563 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7115564 : term147 = term135.
Proof. exact (MK_COMB (@lem7115563) (@lem7115562)). Qed.
Lemma lem7115565 : term148 = term137.
Proof. exact (MK_COMB (@lem7115564) (@lem7115552)). Qed.
Lemma lem7115567 (m : nat) : (term149 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7115568 : term137 = term15.
Proof. exact (@lem7115567 term24). Qed.
Lemma lem7115569 : term148 = term15.
Proof. exact (TRANS (@lem7115565) (@lem7115568)). Qed.
Lemma lem7115570 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115571 : term150 = term151.
Proof. exact (MK_COMB (@lem7115570) (@lem7115569)). Qed.
Lemma lem7115572 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem7115573 : term152 = term118.
Proof. exact (MK_COMB (@lem7115571) (@lem7115572)). Qed.
Lemma lem7115575 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115576 : term118 = term15.
Proof. exact (@lem7115575 term24). Qed.
Lemma lem7115577 : term152 = term15.
Proof. exact (TRANS (@lem7115573) (@lem7115576)). Qed.
Lemma lem7115579 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7115580 : term33 = term34.
Proof. exact (@lem7115579 term24 term24). Qed.
Lemma lem7115581 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115582 : term36 = term24.
Proof. exact (EQ_MP (@lem7115581) (@lem940073)). Qed.
Lemma lem7115583 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115584 : term34 = term30.
Proof. exact (MK_COMB (@lem7115583) (@lem7115582)). Qed.
Lemma lem7115585 : term33 = term30.
Proof. exact (TRANS (@lem7115580) (@lem7115584)). Qed.
Lemma lem7115586 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7115587 : term153 = term118.
Proof. exact (MK_COMB (@lem7115586) (@lem7115585)). Qed.
Lemma lem7115589 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115590 : term118 = term15.
Proof. exact (@lem7115589 term24). Qed.
Lemma lem7115591 : term153 = term15.
Proof. exact (TRANS (@lem7115587) (@lem7115590)). Qed.
Lemma lem7115592 : term15 = term153.
Proof. exact (SYM (@lem7115591)). Qed.
Lemma lem7115593 : term152 = term153.
Proof. exact (TRANS (@lem7115577) (@lem7115592)). Qed.
Lemma lem7115594 : term138 = term19.
Proof. exact (@lem7115544 (@lem7115593)). Qed.
Lemma lem7115595 : term137 = term19.
Proof. exact (TRANS (@lem7115510) (@lem7115594)). Qed.
Lemma lem7115597 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7115598 : term19 = term15.
Proof. exact (@lem7115597 term15). Qed.
Lemma lem7115599 : term137 = term15.
Proof. exact (TRANS (@lem7115595) (@lem7115598)). Qed.
Lemma lem7115600 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115601 : term154 = term151.
Proof. exact (MK_COMB (@lem7115600) (@lem7115599)). Qed.
Lemma lem7115602 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7115603 (x : real) : (term134 x) = (term155 x).
Proof. exact (MK_COMB (@lem7115601) (@lem7115602 x)). Qed.
Lemma lem7115604 (x : real) : (term133 x) = (term155 x).
Proof. exact (TRANS (@lem7115501 x) (@lem7115603 x)). Qed.
Lemma lem7115605 (x : real) : (term155 x) = term15.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7115606 (x : real) : (term133 x) = term15.
Proof. exact (TRANS (@lem7115604 x) (@lem7115605 x)). Qed.
Lemma lem7115607 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7115608 (x : real) : (term156 x) = term157.
Proof. exact (MK_COMB (@lem7115607) (@lem7115606 x)). Qed.
Lemma lem7115609 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7115610 (x : real) : (term132 x) = term158.
Proof. exact (MK_COMB (@lem7115608 x) (@lem7115609)). Qed.
Lemma lem7115611 (x : real) (h1 : term181 x) : term158.
Proof. exact (EQ_MP (@lem7115610 x) (@lem7115500 x h1)). Qed.
Lemma lem7115613 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7115614 : term158 = term159.
Proof. exact (@lem7115613 term15 term15). Qed.
Lemma lem7115616 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115617 : term15 = term19.
Proof. exact (@lem7115616 (NUMERAL 0)). Qed.
Lemma lem7115619 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115620 : term15 = term19.
Proof. exact (@lem7115619 (NUMERAL 0)). Qed.
Lemma lem7115621 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7115622 : term108 = term109.
Proof. exact (MK_COMB (@lem7115621) (@lem7115620)). Qed.
Lemma lem7115623 : term159 = term160.
Proof. exact (MK_COMB (@lem7115622) (@lem7115617)). Qed.
Lemma lem7115624 : term161.
Proof. exact (@lem1980255 term15 term30 term15 term30). Qed.
Lemma lem7115626 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115627 : term107 = term113.
Proof. exact (@lem7115626 (NUMERAL 0) term24). Qed.
Lemma lem7115628 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115629 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115630 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115629 h1) (fun h1 : term113 = True => @lem7115628)). Qed.
Lemma lem7115631 : term113 = True.
Proof. exact (EQ_MP (@lem7115630) (@lem7115628)). Qed.
Lemma lem7115632 : term107 = True.
Proof. exact (TRANS (@lem7115627) (@lem7115631)). Qed.
Lemma lem7115633 : True = term107.
Proof. exact (SYM (@lem7115632)). Qed.
Lemma lem7115634 : term107.
Proof. exact (EQ_MP (@lem7115633) (@lem0)). Qed.
Lemma lem7115635 : term162.
Proof. exact (@lem7115624 (@lem7115634)). Qed.
Lemma lem7115637 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115638 : term107 = term113.
Proof. exact (@lem7115637 (NUMERAL 0) term24). Qed.
Lemma lem7115639 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7115640 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7115641 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7115640 h1) (fun h1 : term113 = True => @lem7115639)). Qed.
Lemma lem7115642 : term113 = True.
Proof. exact (EQ_MP (@lem7115641) (@lem7115639)). Qed.
Lemma lem7115643 : term107 = True.
Proof. exact (TRANS (@lem7115638) (@lem7115642)). Qed.
Lemma lem7115644 : True = term107.
Proof. exact (SYM (@lem7115643)). Qed.
Lemma lem7115645 : term107.
Proof. exact (EQ_MP (@lem7115644) (@lem0)). Qed.
Lemma lem7115646 : term160 = term163.
Proof. exact (@lem7115635 (@lem7115645)). Qed.
Lemma lem7115648 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115649 : term118 = term15.
Proof. exact (@lem7115648 term24). Qed.
Lemma lem7115651 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7115652 : term118 = term15.
Proof. exact (@lem7115651 term24). Qed.
Lemma lem7115653 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7115654 : term119 = term108.
Proof. exact (MK_COMB (@lem7115653) (@lem7115652)). Qed.
Lemma lem7115655 : term163 = term159.
Proof. exact (MK_COMB (@lem7115654) (@lem7115649)). Qed.
Lemma lem7115657 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7115658 : term159 = term164.
Proof. exact (@lem7115657 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7115659 : term164 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7115660 : term159 = False.
Proof. exact (TRANS (@lem7115658) (@lem7115659)). Qed.
Lemma lem7115661 : term163 = False.
Proof. exact (TRANS (@lem7115655) (@lem7115660)). Qed.
Lemma lem7115662 : term160 = False.
Proof. exact (TRANS (@lem7115646) (@lem7115661)). Qed.
Lemma lem7115663 : term159 = False.
Proof. exact (TRANS (@lem7115623) (@lem7115662)). Qed.
Lemma lem7115664 : term158 = False.
Proof. exact (TRANS (@lem7115614) (@lem7115663)). Qed.
Lemma lem7115665 (x : real) (h1 : term181 x) : False.
Proof. exact (EQ_MP (@lem7115664) (@lem7115611 x h1)). Qed.
Lemma lem7115666 (x : real) (h1 : term101 x) : False.
Proof. exact (or_elim (@lem7115103 x h1) (fun h0 : term176 x => @lem7115363 x h0) (fun h0 : term181 x => @lem7115665 x h0)). Qed.
Lemma lem7115667 (x : real) (h1 : term104 x) : False.
Proof. exact (or_elim (@lem7114580 x h1) (fun h0 : term102 x => @lem7115102 x h0) (fun h0 : term101 x => @lem7115666 x h0)). Qed.
Lemma lem7115669 (x : real) (h1 : term104 x) : term104 x.
Proof. exact (h1). Qed.
Lemma lem7115670 (x : real) (h1 : term104 x) : (term104 x) = False.
Proof. exact (prop_ext (fun h2 : term104 x => @lem7115667 x h1) (fun h2 : False => @lem7115669 x h1)). Qed.
Lemma lem7115671 (x : real) (h1 : term104 x) : False.
Proof. exact (EQ_MP (@lem7115670 x h1) (@lem7115669 x h1)). Qed.
Lemma lem7115672 (x : real) (h1 : term13 x) : term13 x.
Proof. exact (h1). Qed.
Lemma lem7115673 (x : real) (h1 : term13 x) : term104 x.
Proof. exact (EQ_MP (@lem7114558 x) (@lem7115672 x h1)). Qed.
Lemma lem7115674 (x : real) (h1 : term13 x) : (term104 x) = False.
Proof. exact (prop_ext (fun h2 : term104 x => @lem7115671 x h2) (fun h2 : False => @lem7115673 x h1)). Qed.
Lemma lem7115675 (x : real) (h1 : term13 x) : False.
Proof. exact (EQ_MP (@lem7115674 x h1) (@lem7115673 x h1)). Qed.
Lemma lem7115676 (x : real) : term184 x.
Proof. exact (fun h0 : term13 x => @lem7115675 x h0). Qed.
Lemma lem7115677 (x : real) : term185 x.
Proof. exact (@lem1386578 ((x = term15) = ((real_neg x) = term15))). Qed.
Lemma lem7115692 (u : real) : (term186 u) = (term70 u).
Proof. exact (@lem16933 (term70 u)). Qed.
Lemma lem7115695 (u : real) : (term187 u) = (term187 u).
Proof. exact (eq_refl (term187 u)). Qed.
Lemma lem7115697 (u : real) : (term188 u) = (term188 u).
Proof. exact (eq_refl (term188 u)). Qed.
Lemma lem7115698 (u : real) : (term189 u) = (term190 u).
Proof. exact (MK_COMB (@lem7115697 u) (@lem7115692 u)). Qed.
Lemma lem7115699 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7115700 (u : real) : (term191 u) = (term192 u).
Proof. exact (MK_COMB (@lem7115699) (@lem7115698 u)). Qed.
Lemma lem7115701 (u : real) : (term193 u) = (term194 u).
Proof. exact (MK_COMB (@lem7115700 u) (@lem7115695 u)). Qed.
Lemma lem7115702 (u : real) : (term195 u) = (term193 u).
Proof. exact (@lem17646 (term196 u) (term197 u)). Qed.
Lemma lem7115703 (u : real) : (term195 u) = (term194 u).
Proof. exact (TRANS (@lem7115702 u) (@lem7115701 u)). Qed.
Lemma lem7115709 (u : real) : (term198 u) = (term199 u).
Proof. exact (@lem16933 (term199 u)). Qed.
Lemma lem7115712 (u : real) : (term200 u) = (term200 u).
Proof. exact (eq_refl (term200 u)). Qed.
Lemma lem7115714 (u : real) : (term201 u) = (term201 u).
Proof. exact (eq_refl (term201 u)). Qed.
Lemma lem7115715 (u : real) : (term202 u) = (term203 u).
Proof. exact (MK_COMB (@lem7115714 u) (@lem7115709 u)). Qed.
Lemma lem7115716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7115717 (u : real) : (term204 u) = (term205 u).
Proof. exact (MK_COMB (@lem7115716) (@lem7115715 u)). Qed.
Lemma lem7115718 (u : real) : (term206 u) = (term207 u).
Proof. exact (MK_COMB (@lem7115717 u) (@lem7115712 u)). Qed.
Lemma lem7115719 (u : real) : (term208 u) = (term206 u).
Proof. exact (@lem17646 (term209 u) (term210 u)). Qed.
Lemma lem7115720 (u : real) : (term208 u) = (term207 u).
Proof. exact (TRANS (@lem7115719 u) (@lem7115718 u)). Qed.
Lemma lem7115721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7115722 (u : real) : (term211 u) = (term212 u).
Proof. exact (MK_COMB (@lem7115721) (@lem7115703 u)). Qed.
Lemma lem7115723 (u : real) : (term213 u) = (term214 u).
Proof. exact (MK_COMB (@lem7115722 u) (@lem7115720 u)). Qed.
Lemma lem7115724 (u : real) : (term215 u) = (term213 u).
Proof. exact (@lem17045 ((term196 u) = (term197 u)) ((term209 u) = (term210 u))). Qed.
Lemma lem7115764 (u : real) : (term215 u) = (term214 u).
Proof. exact (TRANS (@lem7115724 u) (@lem7115723 u)). Qed.
Lemma lem7115765 (u : real) : (term196 u) = (term216 u).
Proof. exact (@lem1988287 (real_neg u) term15). Qed.
Lemma lem7115766 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7115773 (u : real) : (real_neg u) = (term45 u).
Proof. exact (@lem1982785 u). Qed.
Lemma lem7115774 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7115775 (u : real) : (term46 u) = (term47 u).
Proof. exact (MK_COMB (@lem7115774) (@lem7115773 u)). Qed.
Lemma lem7115776 (u : real) : (term48 u) = (term49 u).
Proof. exact (MK_COMB (@lem7115775 u) (@lem7115766)). Qed.
Lemma lem7115777 (u : real) : (term49 u) = (term50 u).
Proof. exact (@lem1982792 (term45 u) term15). Qed.
Lemma lem7115779 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115780 : term15 = term19.
Proof. exact (@lem7115779 (NUMERAL 0)). Qed.
Lemma lem7115782 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7115783 : term22 = term23.
Proof. exact (@lem7115782 term24). Qed.
Lemma lem7115784 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115785 : term25 = term26.
Proof. exact (MK_COMB (@lem7115784) (@lem7115783)). Qed.
Lemma lem7115786 : term27 = term28.
Proof. exact (MK_COMB (@lem7115785) (@lem7115780)). Qed.
Lemma lem7115787 : term28 = term29.
Proof. exact (@lem1981613 term22 term15 term30 term30). Qed.
Lemma lem7115789 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7115790 : term33 = term34.
Proof. exact (@lem7115789 term24 term24). Qed.
Lemma lem7115791 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115792 : term36 = term24.
Proof. exact (EQ_MP (@lem7115791) (@lem940073)). Qed.
Lemma lem7115793 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115794 : term34 = term30.
Proof. exact (MK_COMB (@lem7115793) (@lem7115792)). Qed.
Lemma lem7115795 : term33 = term30.
Proof. exact (TRANS (@lem7115790) (@lem7115794)). Qed.
Lemma lem7115797 (x : nat) : (term37 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7115798 : term27 = term15.
Proof. exact (@lem7115797 term24). Qed.
Lemma lem7115799 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7115800 : term38 = term39.
Proof. exact (MK_COMB (@lem7115799) (@lem7115798)). Qed.
Lemma lem7115801 : term29 = term19.
Proof. exact (MK_COMB (@lem7115800) (@lem7115795)). Qed.
Lemma lem7115802 : term28 = term19.
Proof. exact (TRANS (@lem7115787) (@lem7115801)). Qed.
Lemma lem7115803 : term27 = term19.
Proof. exact (TRANS (@lem7115786) (@lem7115802)). Qed.
Lemma lem7115805 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7115806 : term19 = term15.
Proof. exact (@lem7115805 term15). Qed.
Lemma lem7115807 : term27 = term15.
Proof. exact (TRANS (@lem7115803) (@lem7115806)). Qed.
Lemma lem7115808 (u : real) : (term51 u) = (term51 u).
Proof. exact (eq_refl (term51 u)). Qed.
Lemma lem7115809 (u : real) : (term50 u) = (term52 u).
Proof. exact (MK_COMB (@lem7115808 u) (@lem7115807)). Qed.
Lemma lem7115810 (u : real) : (term52 u) = (term45 u).
Proof. exact (@lem1982723 (term45 u)). Qed.
Lemma lem7115811 (u : real) : (term50 u) = (term45 u).
Proof. exact (TRANS (@lem7115809 u) (@lem7115810 u)). Qed.
Lemma lem7115812 (u : real) : (term49 u) = (term45 u).
Proof. exact (TRANS (@lem7115777 u) (@lem7115811 u)). Qed.
Lemma lem7115813 (u : real) : (term48 u) = (term45 u).
Proof. exact (TRANS (@lem7115776 u) (@lem7115812 u)). Qed.
Lemma lem7115814 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7115815 (u : real) : (term217 u) = (term218 u).
Proof. exact (MK_COMB (@lem7115814) (@lem7115813 u)). Qed.
Lemma lem7115816 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7115817 (u : real) : (term216 u) = (term219 u).
Proof. exact (MK_COMB (@lem7115815 u) (@lem7115816)). Qed.
Lemma lem7115818 (u : real) : (term196 u) = (term219 u).
Proof. exact (TRANS (@lem7115765 u) (@lem7115817 u)). Qed.
Lemma lem7115819 (u : real) : (term70 u) = (term88 u).
Proof. exact (@lem1988289 u term15). Qed.
Lemma lem7115825 (u : real) : (term16 u) = (term17 u).
Proof. exact (@lem1982792 u term15). Qed.
Lemma lem7115827 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115828 : term15 = term19.
Proof. exact (@lem7115827 (NUMERAL 0)). Qed.
Lemma lem7115830 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7115831 : term22 = term23.
Proof. exact (@lem7115830 term24). Qed.
Lemma lem7115832 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115833 : term25 = term26.
Proof. exact (MK_COMB (@lem7115832) (@lem7115831)). Qed.
Lemma lem7115834 : term27 = term28.
Proof. exact (MK_COMB (@lem7115833) (@lem7115828)). Qed.
Lemma lem7115835 : term28 = term29.
Proof. exact (@lem1981613 term22 term15 term30 term30). Qed.
Lemma lem7115837 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7115838 : term33 = term34.
Proof. exact (@lem7115837 term24 term24). Qed.
Lemma lem7115839 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115840 : term36 = term24.
Proof. exact (EQ_MP (@lem7115839) (@lem940073)). Qed.
Lemma lem7115841 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115842 : term34 = term30.
Proof. exact (MK_COMB (@lem7115841) (@lem7115840)). Qed.
Lemma lem7115843 : term33 = term30.
Proof. exact (TRANS (@lem7115838) (@lem7115842)). Qed.
Lemma lem7115845 (x : nat) : (term37 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7115846 : term27 = term15.
Proof. exact (@lem7115845 term24). Qed.
Lemma lem7115847 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7115848 : term38 = term39.
Proof. exact (MK_COMB (@lem7115847) (@lem7115846)). Qed.
Lemma lem7115849 : term29 = term19.
Proof. exact (MK_COMB (@lem7115848) (@lem7115843)). Qed.
Lemma lem7115850 : term28 = term19.
Proof. exact (TRANS (@lem7115835) (@lem7115849)). Qed.
Lemma lem7115851 : term27 = term19.
Proof. exact (TRANS (@lem7115834) (@lem7115850)). Qed.
Lemma lem7115853 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7115854 : term19 = term15.
Proof. exact (@lem7115853 term15). Qed.
Lemma lem7115855 : term27 = term15.
Proof. exact (TRANS (@lem7115851) (@lem7115854)). Qed.
Lemma lem7115856 (u : real) : (real_add u) = (real_add u).
Proof. exact (eq_refl (real_add u)). Qed.
Lemma lem7115857 (u : real) : (term17 u) = (term41 u).
Proof. exact (MK_COMB (@lem7115856 u) (@lem7115855)). Qed.
Lemma lem7115858 (u : real) : (term41 u) = u.
Proof. exact (@lem1982723 u). Qed.
Lemma lem7115859 (u : real) : (term17 u) = u.
Proof. exact (TRANS (@lem7115857 u) (@lem7115858 u)). Qed.
Lemma lem7115861 (u : real) : (term16 u) = u.
Proof. exact (TRANS (@lem7115825 u) (@lem7115859 u)). Qed.
Lemma lem7115862 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7115863 (u : real) : (term87 u) = (real_gt u).
Proof. exact (MK_COMB (@lem7115862) (@lem7115861 u)). Qed.
Lemma lem7115864 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7115865 (u : real) : (term88 u) = (term70 u).
Proof. exact (MK_COMB (@lem7115863 u) (@lem7115864)). Qed.
Lemma lem7115866 (u : real) : (term70 u) = (term70 u).
Proof. exact (TRANS (@lem7115819 u) (@lem7115865 u)). Qed.
Lemma lem7115867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7115868 (u : real) : (term188 u) = (term220 u).
Proof. exact (MK_COMB (@lem7115867) (@lem7115818 u)). Qed.
Lemma lem7115869 (u : real) : (term190 u) = (term221 u).
Proof. exact (MK_COMB (@lem7115868 u) (@lem7115866 u)). Qed.
Lemma lem7115870 (u : real) : (term222 u) = (term223 u).
Proof. exact (@lem1988297 term15 (real_neg u)). Qed.
Lemma lem7115877 (u : real) : (real_neg u) = (term45 u).
Proof. exact (@lem1982785 u). Qed.
Lemma lem7115880 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem7115881 (u : real) : (term225 u) = (term226 u).
Proof. exact (MK_COMB (@lem7115880) (@lem7115877 u)). Qed.
Lemma lem7115882 (u : real) : (term226 u) = (term227 u).
Proof. exact (@lem1982792 term15 (term45 u)). Qed.
Lemma lem7115883 (u : real) : (term55 u) = (term56 u).
Proof. exact (@lem1982749 term22 term22 u). Qed.
Lemma lem7115885 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7115886 : term22 = term23.
Proof. exact (@lem7115885 term24). Qed.
Lemma lem7115888 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7115889 : term22 = term23.
Proof. exact (@lem7115888 term24). Qed.
Lemma lem7115890 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115891 : term25 = term26.
Proof. exact (MK_COMB (@lem7115890) (@lem7115889)). Qed.
Lemma lem7115892 : term57 = term58.
Proof. exact (MK_COMB (@lem7115891) (@lem7115886)). Qed.
Lemma lem7115893 : term58 = term59.
Proof. exact (@lem1981613 term22 term22 term30 term30). Qed.
Lemma lem7115895 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7115896 : term33 = term34.
Proof. exact (@lem7115895 term24 term24). Qed.
Lemma lem7115897 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115898 : term36 = term24.
Proof. exact (EQ_MP (@lem7115897) (@lem940073)). Qed.
Lemma lem7115899 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115900 : term34 = term30.
Proof. exact (MK_COMB (@lem7115899) (@lem7115898)). Qed.
Lemma lem7115901 : term33 = term30.
Proof. exact (TRANS (@lem7115896) (@lem7115900)). Qed.
Lemma lem7115903 (m : nat) (n : nat) : (term60 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7115904 : term57 = term34.
Proof. exact (@lem7115903 term24 term24). Qed.
Lemma lem7115905 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115906 : term36 = term24.
Proof. exact (EQ_MP (@lem7115905) (@lem940073)). Qed.
Lemma lem7115907 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115908 : term34 = term30.
Proof. exact (MK_COMB (@lem7115907) (@lem7115906)). Qed.
Lemma lem7115909 : term57 = term30.
Proof. exact (TRANS (@lem7115904) (@lem7115908)). Qed.
Lemma lem7115910 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7115911 : term61 = term62.
Proof. exact (MK_COMB (@lem7115910) (@lem7115909)). Qed.
Lemma lem7115912 : term59 = term63.
Proof. exact (MK_COMB (@lem7115911) (@lem7115901)). Qed.
Lemma lem7115913 : term58 = term63.
Proof. exact (TRANS (@lem7115893) (@lem7115912)). Qed.
Lemma lem7115914 : term57 = term63.
Proof. exact (TRANS (@lem7115892) (@lem7115913)). Qed.
Lemma lem7115916 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7115917 : term63 = term30.
Proof. exact (@lem7115916 term30). Qed.
Lemma lem7115918 : term57 = term30.
Proof. exact (TRANS (@lem7115914) (@lem7115917)). Qed.
Lemma lem7115919 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115920 : term64 = term65.
Proof. exact (MK_COMB (@lem7115919) (@lem7115918)). Qed.
Lemma lem7115921 (u : real) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7115922 (u : real) : (term56 u) = (term66 u).
Proof. exact (MK_COMB (@lem7115920) (@lem7115921 u)). Qed.
Lemma lem7115923 (u : real) : (term55 u) = (term66 u).
Proof. exact (TRANS (@lem7115883 u) (@lem7115922 u)). Qed.
Lemma lem7115924 (u : real) : (term66 u) = u.
Proof. exact (@lem1982709 u). Qed.
Lemma lem7115925 (u : real) : (term55 u) = u.
Proof. exact (TRANS (@lem7115923 u) (@lem7115924 u)). Qed.
Lemma lem7115926 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem7115927 (u : real) : (term227 u) = (term229 u).
Proof. exact (MK_COMB (@lem7115926) (@lem7115925 u)). Qed.
Lemma lem7115928 (u : real) : (term229 u) = u.
Proof. exact (@lem1982721 u). Qed.
Lemma lem7115929 (u : real) : (term227 u) = u.
Proof. exact (TRANS (@lem7115927 u) (@lem7115928 u)). Qed.
Lemma lem7115930 (u : real) : (term226 u) = u.
Proof. exact (TRANS (@lem7115882 u) (@lem7115929 u)). Qed.
Lemma lem7115931 (u : real) : (term225 u) = u.
Proof. exact (TRANS (@lem7115881 u) (@lem7115930 u)). Qed.
Lemma lem7115932 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7115933 (u : real) : (term230 u) = (real_gt u).
Proof. exact (MK_COMB (@lem7115932) (@lem7115931 u)). Qed.
Lemma lem7115934 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7115935 (u : real) : (term223 u) = (term70 u).
Proof. exact (MK_COMB (@lem7115933 u) (@lem7115934)). Qed.
Lemma lem7115936 (u : real) : (term222 u) = (term70 u).
Proof. exact (TRANS (@lem7115870 u) (@lem7115935 u)). Qed.
Lemma lem7115937 (u : real) : (term197 u) = (term231 u).
Proof. exact (@lem1988299 term15 u). Qed.
Lemma lem7115943 (u : real) : (term232 u) = (term233 u).
Proof. exact (@lem1982792 term15 u). Qed.
Lemma lem7115948 (u : real) : (term233 u) = (term45 u).
Proof. exact (@lem1982721 (term45 u)). Qed.
Lemma lem7115950 (u : real) : (term232 u) = (term45 u).
Proof. exact (TRANS (@lem7115943 u) (@lem7115948 u)). Qed.
Lemma lem7115951 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7115952 (u : real) : (term234 u) = (term218 u).
Proof. exact (MK_COMB (@lem7115951) (@lem7115950 u)). Qed.
Lemma lem7115953 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7115954 (u : real) : (term231 u) = (term219 u).
Proof. exact (MK_COMB (@lem7115952 u) (@lem7115953)). Qed.
Lemma lem7115955 (u : real) : (term197 u) = (term219 u).
Proof. exact (TRANS (@lem7115937 u) (@lem7115954 u)). Qed.
Lemma lem7115956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7115957 (u : real) : (term235 u) = (term236 u).
Proof. exact (MK_COMB (@lem7115956) (@lem7115936 u)). Qed.
Lemma lem7115958 (u : real) : (term187 u) = (term237 u).
Proof. exact (MK_COMB (@lem7115957 u) (@lem7115955 u)). Qed.
Lemma lem7115959 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7115960 (u : real) : (term192 u) = (term238 u).
Proof. exact (MK_COMB (@lem7115959) (@lem7115869 u)). Qed.
Lemma lem7115961 (u : real) : (term194 u) = (term239 u).
Proof. exact (MK_COMB (@lem7115960 u) (@lem7115958 u)). Qed.
Lemma lem7115962 (u : real) : (term209 u) = (term240 u).
Proof. exact (@lem1988287 u term15). Qed.
Lemma lem7115968 (u : real) : (term16 u) = (term17 u).
Proof. exact (@lem1982792 u term15). Qed.
Lemma lem7115970 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7115971 : term15 = term19.
Proof. exact (@lem7115970 (NUMERAL 0)). Qed.
Lemma lem7115973 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7115974 : term22 = term23.
Proof. exact (@lem7115973 term24). Qed.
Lemma lem7115975 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7115976 : term25 = term26.
Proof. exact (MK_COMB (@lem7115975) (@lem7115974)). Qed.
Lemma lem7115977 : term27 = term28.
Proof. exact (MK_COMB (@lem7115976) (@lem7115971)). Qed.
Lemma lem7115978 : term28 = term29.
Proof. exact (@lem1981613 term22 term15 term30 term30). Qed.
Lemma lem7115980 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7115981 : term33 = term34.
Proof. exact (@lem7115980 term24 term24). Qed.
Lemma lem7115982 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7115983 : term36 = term24.
Proof. exact (EQ_MP (@lem7115982) (@lem940073)). Qed.
Lemma lem7115984 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7115985 : term34 = term30.
Proof. exact (MK_COMB (@lem7115984) (@lem7115983)). Qed.
Lemma lem7115986 : term33 = term30.
Proof. exact (TRANS (@lem7115981) (@lem7115985)). Qed.
Lemma lem7115988 (x : nat) : (term37 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7115989 : term27 = term15.
Proof. exact (@lem7115988 term24). Qed.
Lemma lem7115990 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7115991 : term38 = term39.
Proof. exact (MK_COMB (@lem7115990) (@lem7115989)). Qed.
Lemma lem7115992 : term29 = term19.
Proof. exact (MK_COMB (@lem7115991) (@lem7115986)). Qed.
Lemma lem7115993 : term28 = term19.
Proof. exact (TRANS (@lem7115978) (@lem7115992)). Qed.
Lemma lem7115994 : term27 = term19.
Proof. exact (TRANS (@lem7115977) (@lem7115993)). Qed.
Lemma lem7115996 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7115997 : term19 = term15.
Proof. exact (@lem7115996 term15). Qed.
Lemma lem7115998 : term27 = term15.
Proof. exact (TRANS (@lem7115994) (@lem7115997)). Qed.
Lemma lem7115999 (u : real) : (real_add u) = (real_add u).
Proof. exact (eq_refl (real_add u)). Qed.
Lemma lem7116000 (u : real) : (term17 u) = (term41 u).
Proof. exact (MK_COMB (@lem7115999 u) (@lem7115998)). Qed.
Lemma lem7116001 (u : real) : (term41 u) = u.
Proof. exact (@lem1982723 u). Qed.
Lemma lem7116002 (u : real) : (term17 u) = u.
Proof. exact (TRANS (@lem7116000 u) (@lem7116001 u)). Qed.
Lemma lem7116004 (u : real) : (term16 u) = u.
Proof. exact (TRANS (@lem7115968 u) (@lem7116002 u)). Qed.
Lemma lem7116005 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7116006 (u : real) : (term241 u) = (real_ge u).
Proof. exact (MK_COMB (@lem7116005) (@lem7116004 u)). Qed.
Lemma lem7116007 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7116008 (u : real) : (term240 u) = (term242 u).
Proof. exact (MK_COMB (@lem7116006 u) (@lem7116007)). Qed.
Lemma lem7116009 (u : real) : (term209 u) = (term242 u).
Proof. exact (TRANS (@lem7115962 u) (@lem7116008 u)). Qed.
Lemma lem7116010 (u : real) : (term199 u) = (term243 u).
Proof. exact (@lem1988285 term15 u). Qed.
Lemma lem7116016 (u : real) : (term232 u) = (term233 u).
Proof. exact (@lem1982792 term15 u). Qed.
Lemma lem7116021 (u : real) : (term233 u) = (term45 u).
Proof. exact (@lem1982721 (term45 u)). Qed.
Lemma lem7116023 (u : real) : (term232 u) = (term45 u).
Proof. exact (TRANS (@lem7116016 u) (@lem7116021 u)). Qed.
Lemma lem7116024 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7116025 (u : real) : (term244 u) = (term72 u).
Proof. exact (MK_COMB (@lem7116024) (@lem7116023 u)). Qed.
Lemma lem7116026 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7116027 (u : real) : (term243 u) = (term74 u).
Proof. exact (MK_COMB (@lem7116025 u) (@lem7116026)). Qed.
Lemma lem7116028 (u : real) : (term199 u) = (term74 u).
Proof. exact (TRANS (@lem7116010 u) (@lem7116027 u)). Qed.
Lemma lem7116029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7116030 (u : real) : (term201 u) = (term245 u).
Proof. exact (MK_COMB (@lem7116029) (@lem7116009 u)). Qed.
Lemma lem7116031 (u : real) : (term203 u) = (term246 u).
Proof. exact (MK_COMB (@lem7116030 u) (@lem7116028 u)). Qed.
Lemma lem7116032 (u : real) : (term247 u) = (term243 u).
Proof. exact (@lem1988297 term15 u). Qed.
Lemma lem7116038 (u : real) : (term232 u) = (term233 u).
Proof. exact (@lem1982792 term15 u). Qed.
Lemma lem7116043 (u : real) : (term233 u) = (term45 u).
Proof. exact (@lem1982721 (term45 u)). Qed.
Lemma lem7116045 (u : real) : (term232 u) = (term45 u).
Proof. exact (TRANS (@lem7116038 u) (@lem7116043 u)). Qed.
Lemma lem7116046 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7116047 (u : real) : (term244 u) = (term72 u).
Proof. exact (MK_COMB (@lem7116046) (@lem7116045 u)). Qed.
Lemma lem7116048 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7116049 (u : real) : (term243 u) = (term74 u).
Proof. exact (MK_COMB (@lem7116047 u) (@lem7116048)). Qed.
Lemma lem7116050 (u : real) : (term247 u) = (term74 u).
Proof. exact (TRANS (@lem7116032 u) (@lem7116049 u)). Qed.
Lemma lem7116051 (u : real) : (term210 u) = (term240 u).
Proof. exact (@lem1988295 u term15). Qed.
Lemma lem7116057 (u : real) : (term16 u) = (term17 u).
Proof. exact (@lem1982792 u term15). Qed.
Lemma lem7116059 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116060 : term15 = term19.
Proof. exact (@lem7116059 (NUMERAL 0)). Qed.
Lemma lem7116062 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7116063 : term22 = term23.
Proof. exact (@lem7116062 term24). Qed.
Lemma lem7116064 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7116065 : term25 = term26.
Proof. exact (MK_COMB (@lem7116064) (@lem7116063)). Qed.
Lemma lem7116066 : term27 = term28.
Proof. exact (MK_COMB (@lem7116065) (@lem7116060)). Qed.
Lemma lem7116067 : term28 = term29.
Proof. exact (@lem1981613 term22 term15 term30 term30). Qed.
Lemma lem7116069 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7116070 : term33 = term34.
Proof. exact (@lem7116069 term24 term24). Qed.
Lemma lem7116071 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116072 : term36 = term24.
Proof. exact (EQ_MP (@lem7116071) (@lem940073)). Qed.
Lemma lem7116073 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116074 : term34 = term30.
Proof. exact (MK_COMB (@lem7116073) (@lem7116072)). Qed.
Lemma lem7116075 : term33 = term30.
Proof. exact (TRANS (@lem7116070) (@lem7116074)). Qed.
Lemma lem7116077 (x : nat) : (term37 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7116078 : term27 = term15.
Proof. exact (@lem7116077 term24). Qed.
Lemma lem7116079 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7116080 : term38 = term39.
Proof. exact (MK_COMB (@lem7116079) (@lem7116078)). Qed.
Lemma lem7116081 : term29 = term19.
Proof. exact (MK_COMB (@lem7116080) (@lem7116075)). Qed.
Lemma lem7116082 : term28 = term19.
Proof. exact (TRANS (@lem7116067) (@lem7116081)). Qed.
Lemma lem7116083 : term27 = term19.
Proof. exact (TRANS (@lem7116066) (@lem7116082)). Qed.
Lemma lem7116085 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7116086 : term19 = term15.
Proof. exact (@lem7116085 term15). Qed.
Lemma lem7116087 : term27 = term15.
Proof. exact (TRANS (@lem7116083) (@lem7116086)). Qed.
Lemma lem7116088 (u : real) : (real_add u) = (real_add u).
Proof. exact (eq_refl (real_add u)). Qed.
Lemma lem7116089 (u : real) : (term17 u) = (term41 u).
Proof. exact (MK_COMB (@lem7116088 u) (@lem7116087)). Qed.
Lemma lem7116090 (u : real) : (term41 u) = u.
Proof. exact (@lem1982723 u). Qed.
Lemma lem7116091 (u : real) : (term17 u) = u.
Proof. exact (TRANS (@lem7116089 u) (@lem7116090 u)). Qed.
Lemma lem7116093 (u : real) : (term16 u) = u.
Proof. exact (TRANS (@lem7116057 u) (@lem7116091 u)). Qed.
Lemma lem7116094 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7116095 (u : real) : (term241 u) = (real_ge u).
Proof. exact (MK_COMB (@lem7116094) (@lem7116093 u)). Qed.
Lemma lem7116096 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7116097 (u : real) : (term240 u) = (term242 u).
Proof. exact (MK_COMB (@lem7116095 u) (@lem7116096)). Qed.
Lemma lem7116098 (u : real) : (term210 u) = (term242 u).
Proof. exact (TRANS (@lem7116051 u) (@lem7116097 u)). Qed.
Lemma lem7116099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7116100 (u : real) : (term248 u) = (term249 u).
Proof. exact (MK_COMB (@lem7116099) (@lem7116050 u)). Qed.
Lemma lem7116101 (u : real) : (term200 u) = (term250 u).
Proof. exact (MK_COMB (@lem7116100 u) (@lem7116098 u)). Qed.
Lemma lem7116102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7116103 (u : real) : (term205 u) = (term251 u).
Proof. exact (MK_COMB (@lem7116102) (@lem7116031 u)). Qed.
Lemma lem7116104 (u : real) : (term207 u) = (term252 u).
Proof. exact (MK_COMB (@lem7116103 u) (@lem7116101 u)). Qed.
Lemma lem7116105 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7116106 (u : real) : (term212 u) = (term253 u).
Proof. exact (MK_COMB (@lem7116105) (@lem7115961 u)). Qed.
Lemma lem7116107 (u : real) : (term214 u) = (term254 u).
Proof. exact (MK_COMB (@lem7116106 u) (@lem7116104 u)). Qed.
Lemma lem7116152 (u : real) : (term215 u) = (term254 u).
Proof. exact (TRANS (@lem7115764 u) (@lem7116107 u)). Qed.
Lemma lem7116174 (u : real) (h1 : term254 u) : term254 u.
Proof. exact (h1). Qed.
Lemma lem7116175 (u : real) (h1 : term239 u) : term239 u.
Proof. exact (h1). Qed.
Lemma lem7116176 (u : real) (h1 : term221 u) : term221 u.
Proof. exact (h1). Qed.
Lemma lem7116177 (u : real) (h1 : term221 u) : term70 u.
Proof. exact (proj2 (@lem7116176 u h1)). Qed.
Lemma lem7116178 (u : real) (h1 : term221 u) : term219 u.
Proof. exact (proj1 (@lem7116176 u h1)). Qed.
Lemma lem7116180 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7116181 : term106 = term107.
Proof. exact (@lem7116180 term15 term30). Qed.
Lemma lem7116183 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116184 : term30 = term63.
Proof. exact (@lem7116183 term24). Qed.
Lemma lem7116186 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116187 : term15 = term19.
Proof. exact (@lem7116186 (NUMERAL 0)). Qed.
Lemma lem7116188 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116189 : term108 = term109.
Proof. exact (MK_COMB (@lem7116188) (@lem7116187)). Qed.
Lemma lem7116190 : term107 = term110.
Proof. exact (MK_COMB (@lem7116189) (@lem7116184)). Qed.
Lemma lem7116191 : term111.
Proof. exact (@lem1980255 term15 term30 term30 term30). Qed.
Lemma lem7116193 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116194 : term107 = term113.
Proof. exact (@lem7116193 (NUMERAL 0) term24). Qed.
Lemma lem7116195 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116196 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116197 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116196 h1) (fun h1 : term113 = True => @lem7116195)). Qed.
Lemma lem7116198 : term113 = True.
Proof. exact (EQ_MP (@lem7116197) (@lem7116195)). Qed.
Lemma lem7116199 : term107 = True.
Proof. exact (TRANS (@lem7116194) (@lem7116198)). Qed.
Lemma lem7116200 : True = term107.
Proof. exact (SYM (@lem7116199)). Qed.
Lemma lem7116201 : term107.
Proof. exact (EQ_MP (@lem7116200) (@lem0)). Qed.
Lemma lem7116202 : term115.
Proof. exact (@lem7116191 (@lem7116201)). Qed.
Lemma lem7116204 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116205 : term107 = term113.
Proof. exact (@lem7116204 (NUMERAL 0) term24). Qed.
Lemma lem7116206 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116207 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116208 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116207 h1) (fun h1 : term113 = True => @lem7116206)). Qed.
Lemma lem7116209 : term113 = True.
Proof. exact (EQ_MP (@lem7116208) (@lem7116206)). Qed.
Lemma lem7116210 : term107 = True.
Proof. exact (TRANS (@lem7116205) (@lem7116209)). Qed.
Lemma lem7116211 : True = term107.
Proof. exact (SYM (@lem7116210)). Qed.
Lemma lem7116212 : term107.
Proof. exact (EQ_MP (@lem7116211) (@lem0)). Qed.
Lemma lem7116213 : term110 = term116.
Proof. exact (@lem7116202 (@lem7116212)). Qed.
Lemma lem7116215 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7116216 : term33 = term34.
Proof. exact (@lem7116215 term24 term24). Qed.
Lemma lem7116217 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116218 : term36 = term24.
Proof. exact (EQ_MP (@lem7116217) (@lem940073)). Qed.
Lemma lem7116219 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116220 : term34 = term30.
Proof. exact (MK_COMB (@lem7116219) (@lem7116218)). Qed.
Lemma lem7116221 : term33 = term30.
Proof. exact (TRANS (@lem7116216) (@lem7116220)). Qed.
Lemma lem7116223 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116224 : term118 = term15.
Proof. exact (@lem7116223 term24). Qed.
Lemma lem7116225 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116226 : term119 = term108.
Proof. exact (MK_COMB (@lem7116225) (@lem7116224)). Qed.
Lemma lem7116227 : term116 = term107.
Proof. exact (MK_COMB (@lem7116226) (@lem7116221)). Qed.
Lemma lem7116229 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116230 : term107 = term113.
Proof. exact (@lem7116229 (NUMERAL 0) term24). Qed.
Lemma lem7116231 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116232 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116233 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116232 h1) (fun h1 : term113 = True => @lem7116231)). Qed.
Lemma lem7116234 : term113 = True.
Proof. exact (EQ_MP (@lem7116233) (@lem7116231)). Qed.
Lemma lem7116235 : term107 = True.
Proof. exact (TRANS (@lem7116230) (@lem7116234)). Qed.
Lemma lem7116236 : term116 = True.
Proof. exact (TRANS (@lem7116227) (@lem7116235)). Qed.
Lemma lem7116237 : term110 = True.
Proof. exact (TRANS (@lem7116213) (@lem7116236)). Qed.
Lemma lem7116238 : term107 = True.
Proof. exact (TRANS (@lem7116190) (@lem7116237)). Qed.
Lemma lem7116239 : term106 = True.
Proof. exact (TRANS (@lem7116181) (@lem7116238)). Qed.
Lemma lem7116240 : True = term106.
Proof. exact (SYM (@lem7116239)). Qed.
Lemma lem7116241 : term106.
Proof. exact (EQ_MP (@lem7116240) (@lem0)). Qed.
Lemma lem7116242 (u : real) (h1 : term221 u) : term255 u.
Proof. exact (conj (@lem7116241) (@lem7116178 u h1)). Qed.
Lemma lem7116244 (x : real) (y : real) : term256 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7116245 (u : real) : term257 u.
Proof. exact (@lem7116244 term30 (term45 u)). Qed.
Lemma lem7116246 (u : real) (h1 : term221 u) : term258 u.
Proof. exact (@lem7116245 u (@lem7116242 u h1)). Qed.
Lemma lem7116247 (u : real) : (term124 u) = (term45 u).
Proof. exact (@lem1982733 (term45 u)). Qed.
Lemma lem7116248 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7116249 (u : real) : (term259 u) = (term218 u).
Proof. exact (MK_COMB (@lem7116248) (@lem7116247 u)). Qed.
Lemma lem7116250 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7116251 (u : real) : (term258 u) = (term219 u).
Proof. exact (MK_COMB (@lem7116249 u) (@lem7116250)). Qed.
Lemma lem7116252 (u : real) (h1 : term221 u) : term219 u.
Proof. exact (EQ_MP (@lem7116251 u) (@lem7116246 u h1)). Qed.
Lemma lem7116254 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7116255 : term106 = term107.
Proof. exact (@lem7116254 term15 term30). Qed.
Lemma lem7116257 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116258 : term30 = term63.
Proof. exact (@lem7116257 term24). Qed.
Lemma lem7116260 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116261 : term15 = term19.
Proof. exact (@lem7116260 (NUMERAL 0)). Qed.
Lemma lem7116262 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116263 : term108 = term109.
Proof. exact (MK_COMB (@lem7116262) (@lem7116261)). Qed.
Lemma lem7116264 : term107 = term110.
Proof. exact (MK_COMB (@lem7116263) (@lem7116258)). Qed.
Lemma lem7116265 : term111.
Proof. exact (@lem1980255 term15 term30 term30 term30). Qed.
Lemma lem7116267 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116268 : term107 = term113.
Proof. exact (@lem7116267 (NUMERAL 0) term24). Qed.
Lemma lem7116269 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116270 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116271 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116270 h1) (fun h1 : term113 = True => @lem7116269)). Qed.
Lemma lem7116272 : term113 = True.
Proof. exact (EQ_MP (@lem7116271) (@lem7116269)). Qed.
Lemma lem7116273 : term107 = True.
Proof. exact (TRANS (@lem7116268) (@lem7116272)). Qed.
Lemma lem7116274 : True = term107.
Proof. exact (SYM (@lem7116273)). Qed.
Lemma lem7116275 : term107.
Proof. exact (EQ_MP (@lem7116274) (@lem0)). Qed.
Lemma lem7116276 : term115.
Proof. exact (@lem7116265 (@lem7116275)). Qed.
Lemma lem7116278 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116279 : term107 = term113.
Proof. exact (@lem7116278 (NUMERAL 0) term24). Qed.
Lemma lem7116280 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116281 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116282 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116281 h1) (fun h1 : term113 = True => @lem7116280)). Qed.
Lemma lem7116283 : term113 = True.
Proof. exact (EQ_MP (@lem7116282) (@lem7116280)). Qed.
Lemma lem7116284 : term107 = True.
Proof. exact (TRANS (@lem7116279) (@lem7116283)). Qed.
Lemma lem7116285 : True = term107.
Proof. exact (SYM (@lem7116284)). Qed.
Lemma lem7116286 : term107.
Proof. exact (EQ_MP (@lem7116285) (@lem0)). Qed.
Lemma lem7116287 : term110 = term116.
Proof. exact (@lem7116276 (@lem7116286)). Qed.
Lemma lem7116289 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7116290 : term33 = term34.
Proof. exact (@lem7116289 term24 term24). Qed.
Lemma lem7116291 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116292 : term36 = term24.
Proof. exact (EQ_MP (@lem7116291) (@lem940073)). Qed.
Lemma lem7116293 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116294 : term34 = term30.
Proof. exact (MK_COMB (@lem7116293) (@lem7116292)). Qed.
Lemma lem7116295 : term33 = term30.
Proof. exact (TRANS (@lem7116290) (@lem7116294)). Qed.
Lemma lem7116297 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116298 : term118 = term15.
Proof. exact (@lem7116297 term24). Qed.
Lemma lem7116299 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116300 : term119 = term108.
Proof. exact (MK_COMB (@lem7116299) (@lem7116298)). Qed.
Lemma lem7116301 : term116 = term107.
Proof. exact (MK_COMB (@lem7116300) (@lem7116295)). Qed.
Lemma lem7116303 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116304 : term107 = term113.
Proof. exact (@lem7116303 (NUMERAL 0) term24). Qed.
Lemma lem7116305 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116306 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116307 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116306 h1) (fun h1 : term113 = True => @lem7116305)). Qed.
Lemma lem7116308 : term113 = True.
Proof. exact (EQ_MP (@lem7116307) (@lem7116305)). Qed.
Lemma lem7116309 : term107 = True.
Proof. exact (TRANS (@lem7116304) (@lem7116308)). Qed.
Lemma lem7116310 : term116 = True.
Proof. exact (TRANS (@lem7116301) (@lem7116309)). Qed.
Lemma lem7116311 : term110 = True.
Proof. exact (TRANS (@lem7116287) (@lem7116310)). Qed.
Lemma lem7116312 : term107 = True.
Proof. exact (TRANS (@lem7116264) (@lem7116311)). Qed.
Lemma lem7116313 : term106 = True.
Proof. exact (TRANS (@lem7116255) (@lem7116312)). Qed.
Lemma lem7116314 : True = term106.
Proof. exact (SYM (@lem7116313)). Qed.
Lemma lem7116315 : term106.
Proof. exact (EQ_MP (@lem7116314) (@lem0)). Qed.
Lemma lem7116316 (u : real) (h1 : term221 u) : term166 u.
Proof. exact (conj (@lem7116315) (@lem7116177 u h1)). Qed.
Lemma lem7116318 (x : real) (y : real) : term121 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7116319 (u : real) : term167 u.
Proof. exact (@lem7116318 term30 u). Qed.
Lemma lem7116320 (u : real) (h1 : term221 u) : term168 u.
Proof. exact (@lem7116319 u (@lem7116316 u h1)). Qed.
Lemma lem7116321 (u : real) : (term66 u) = u.
Proof. exact (@lem1982733 u). Qed.
Lemma lem7116322 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7116323 (u : real) : (term169 u) = (real_gt u).
Proof. exact (MK_COMB (@lem7116322) (@lem7116321 u)). Qed.
Lemma lem7116324 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7116325 (u : real) : (term168 u) = (term70 u).
Proof. exact (MK_COMB (@lem7116323 u) (@lem7116324)). Qed.
Lemma lem7116326 (u : real) (h1 : term221 u) : term70 u.
Proof. exact (EQ_MP (@lem7116325 u) (@lem7116320 u h1)). Qed.
Lemma lem7116327 (u : real) (h1 : term221 u) : term237 u.
Proof. exact (conj (@lem7116326 u h1) (@lem7116252 u h1)). Qed.
Lemma lem7116329 (x : real) (y : real) : term260 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem7116330 (u : real) : term261 u.
Proof. exact (@lem7116329 u (term45 u)). Qed.
Lemma lem7116331 (u : real) (h1 : term221 u) : term132 u.
Proof. exact (@lem7116330 u (@lem7116327 u h1)). Qed.
Lemma lem7116332 (u : real) : (term133 u) = (term134 u).
Proof. exact (@lem1982715 term22 u). Qed.
Lemma lem7116334 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116335 : term30 = term63.
Proof. exact (@lem7116334 term24). Qed.
Lemma lem7116337 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7116338 : term22 = term23.
Proof. exact (@lem7116337 term24). Qed.
Lemma lem7116339 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7116340 : term135 = term136.
Proof. exact (MK_COMB (@lem7116339) (@lem7116338)). Qed.
Lemma lem7116341 : term137 = term138.
Proof. exact (MK_COMB (@lem7116340) (@lem7116335)). Qed.
Lemma lem7116342 : term139.
Proof. exact (@lem1981473 term22 term30 term30 term30 term15 term30). Qed.
Lemma lem7116344 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116345 : term107 = term113.
Proof. exact (@lem7116344 (NUMERAL 0) term24). Qed.
Lemma lem7116346 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116347 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116348 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116347 h1) (fun h1 : term113 = True => @lem7116346)). Qed.
Lemma lem7116349 : term113 = True.
Proof. exact (EQ_MP (@lem7116348) (@lem7116346)). Qed.
Lemma lem7116350 : term107 = True.
Proof. exact (TRANS (@lem7116345) (@lem7116349)). Qed.
Lemma lem7116351 : True = term107.
Proof. exact (SYM (@lem7116350)). Qed.
Lemma lem7116352 : term107.
Proof. exact (EQ_MP (@lem7116351) (@lem0)). Qed.
Lemma lem7116353 : term140.
Proof. exact (@lem7116342 (@lem7116352)). Qed.
Lemma lem7116355 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116356 : term107 = term113.
Proof. exact (@lem7116355 (NUMERAL 0) term24). Qed.
Lemma lem7116357 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116358 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116359 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116358 h1) (fun h1 : term113 = True => @lem7116357)). Qed.
Lemma lem7116360 : term113 = True.
Proof. exact (EQ_MP (@lem7116359) (@lem7116357)). Qed.
Lemma lem7116361 : term107 = True.
Proof. exact (TRANS (@lem7116356) (@lem7116360)). Qed.
Lemma lem7116362 : True = term107.
Proof. exact (SYM (@lem7116361)). Qed.
Lemma lem7116363 : term107.
Proof. exact (EQ_MP (@lem7116362) (@lem0)). Qed.
Lemma lem7116364 : term141.
Proof. exact (@lem7116353 (@lem7116363)). Qed.
Lemma lem7116366 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116367 : term107 = term113.
Proof. exact (@lem7116366 (NUMERAL 0) term24). Qed.
Lemma lem7116368 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116369 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116370 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116369 h1) (fun h1 : term113 = True => @lem7116368)). Qed.
Lemma lem7116371 : term113 = True.
Proof. exact (EQ_MP (@lem7116370) (@lem7116368)). Qed.
Lemma lem7116372 : term107 = True.
Proof. exact (TRANS (@lem7116367) (@lem7116371)). Qed.
Lemma lem7116373 : True = term107.
Proof. exact (SYM (@lem7116372)). Qed.
Lemma lem7116374 : term107.
Proof. exact (EQ_MP (@lem7116373) (@lem0)). Qed.
Lemma lem7116375 : term142.
Proof. exact (@lem7116364 (@lem7116374)). Qed.
Lemma lem7116377 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7116378 : term33 = term34.
Proof. exact (@lem7116377 term24 term24). Qed.
Lemma lem7116379 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116380 : term36 = term24.
Proof. exact (EQ_MP (@lem7116379) (@lem940073)). Qed.
Lemma lem7116381 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116382 : term34 = term30.
Proof. exact (MK_COMB (@lem7116381) (@lem7116380)). Qed.
Lemma lem7116383 : term33 = term30.
Proof. exact (TRANS (@lem7116378) (@lem7116382)). Qed.
Lemma lem7116385 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7116386 : term145 = term146.
Proof. exact (@lem7116385 term24 term24). Qed.
Lemma lem7116387 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116388 : term36 = term24.
Proof. exact (EQ_MP (@lem7116387) (@lem940073)). Qed.
Lemma lem7116389 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116390 : term34 = term30.
Proof. exact (MK_COMB (@lem7116389) (@lem7116388)). Qed.
Lemma lem7116391 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7116392 : term146 = term22.
Proof. exact (MK_COMB (@lem7116391) (@lem7116390)). Qed.
Lemma lem7116393 : term145 = term22.
Proof. exact (TRANS (@lem7116386) (@lem7116392)). Qed.
Lemma lem7116394 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7116395 : term147 = term135.
Proof. exact (MK_COMB (@lem7116394) (@lem7116393)). Qed.
Lemma lem7116396 : term148 = term137.
Proof. exact (MK_COMB (@lem7116395) (@lem7116383)). Qed.
Lemma lem7116398 (m : nat) : (term149 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7116399 : term137 = term15.
Proof. exact (@lem7116398 term24). Qed.
Lemma lem7116400 : term148 = term15.
Proof. exact (TRANS (@lem7116396) (@lem7116399)). Qed.
Lemma lem7116401 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7116402 : term150 = term151.
Proof. exact (MK_COMB (@lem7116401) (@lem7116400)). Qed.
Lemma lem7116403 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem7116404 : term152 = term118.
Proof. exact (MK_COMB (@lem7116402) (@lem7116403)). Qed.
Lemma lem7116406 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116407 : term118 = term15.
Proof. exact (@lem7116406 term24). Qed.
Lemma lem7116408 : term152 = term15.
Proof. exact (TRANS (@lem7116404) (@lem7116407)). Qed.
Lemma lem7116410 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7116411 : term33 = term34.
Proof. exact (@lem7116410 term24 term24). Qed.
Lemma lem7116412 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116413 : term36 = term24.
Proof. exact (EQ_MP (@lem7116412) (@lem940073)). Qed.
Lemma lem7116414 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116415 : term34 = term30.
Proof. exact (MK_COMB (@lem7116414) (@lem7116413)). Qed.
Lemma lem7116416 : term33 = term30.
Proof. exact (TRANS (@lem7116411) (@lem7116415)). Qed.
Lemma lem7116417 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7116418 : term153 = term118.
Proof. exact (MK_COMB (@lem7116417) (@lem7116416)). Qed.
Lemma lem7116420 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116421 : term118 = term15.
Proof. exact (@lem7116420 term24). Qed.
Lemma lem7116422 : term153 = term15.
Proof. exact (TRANS (@lem7116418) (@lem7116421)). Qed.
Lemma lem7116423 : term15 = term153.
Proof. exact (SYM (@lem7116422)). Qed.
Lemma lem7116424 : term152 = term153.
Proof. exact (TRANS (@lem7116408) (@lem7116423)). Qed.
Lemma lem7116425 : term138 = term19.
Proof. exact (@lem7116375 (@lem7116424)). Qed.
Lemma lem7116426 : term137 = term19.
Proof. exact (TRANS (@lem7116341) (@lem7116425)). Qed.
Lemma lem7116428 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7116429 : term19 = term15.
Proof. exact (@lem7116428 term15). Qed.
Lemma lem7116430 : term137 = term15.
Proof. exact (TRANS (@lem7116426) (@lem7116429)). Qed.
Lemma lem7116431 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7116432 : term154 = term151.
Proof. exact (MK_COMB (@lem7116431) (@lem7116430)). Qed.
Lemma lem7116433 (u : real) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7116434 (u : real) : (term134 u) = (term155 u).
Proof. exact (MK_COMB (@lem7116432) (@lem7116433 u)). Qed.
Lemma lem7116435 (u : real) : (term133 u) = (term155 u).
Proof. exact (TRANS (@lem7116332 u) (@lem7116434 u)). Qed.
Lemma lem7116436 (u : real) : (term155 u) = term15.
Proof. exact (@lem1982719 u). Qed.
Lemma lem7116437 (u : real) : (term133 u) = term15.
Proof. exact (TRANS (@lem7116435 u) (@lem7116436 u)). Qed.
Lemma lem7116438 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7116439 (u : real) : (term156 u) = term157.
Proof. exact (MK_COMB (@lem7116438) (@lem7116437 u)). Qed.
Lemma lem7116440 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7116441 (u : real) : (term132 u) = term158.
Proof. exact (MK_COMB (@lem7116439 u) (@lem7116440)). Qed.
Lemma lem7116442 (u : real) (h1 : term221 u) : term158.
Proof. exact (EQ_MP (@lem7116441 u) (@lem7116331 u h1)). Qed.
Lemma lem7116444 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7116445 : term158 = term159.
Proof. exact (@lem7116444 term15 term15). Qed.
Lemma lem7116447 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116448 : term15 = term19.
Proof. exact (@lem7116447 (NUMERAL 0)). Qed.
Lemma lem7116450 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116451 : term15 = term19.
Proof. exact (@lem7116450 (NUMERAL 0)). Qed.
Lemma lem7116452 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116453 : term108 = term109.
Proof. exact (MK_COMB (@lem7116452) (@lem7116451)). Qed.
Lemma lem7116454 : term159 = term160.
Proof. exact (MK_COMB (@lem7116453) (@lem7116448)). Qed.
Lemma lem7116455 : term161.
Proof. exact (@lem1980255 term15 term30 term15 term30). Qed.
Lemma lem7116457 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116458 : term107 = term113.
Proof. exact (@lem7116457 (NUMERAL 0) term24). Qed.
Lemma lem7116459 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116460 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116461 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116460 h1) (fun h1 : term113 = True => @lem7116459)). Qed.
Lemma lem7116462 : term113 = True.
Proof. exact (EQ_MP (@lem7116461) (@lem7116459)). Qed.
Lemma lem7116463 : term107 = True.
Proof. exact (TRANS (@lem7116458) (@lem7116462)). Qed.
Lemma lem7116464 : True = term107.
Proof. exact (SYM (@lem7116463)). Qed.
Lemma lem7116465 : term107.
Proof. exact (EQ_MP (@lem7116464) (@lem0)). Qed.
Lemma lem7116466 : term162.
Proof. exact (@lem7116455 (@lem7116465)). Qed.
Lemma lem7116468 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116469 : term107 = term113.
Proof. exact (@lem7116468 (NUMERAL 0) term24). Qed.
Lemma lem7116470 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116471 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116472 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116471 h1) (fun h1 : term113 = True => @lem7116470)). Qed.
Lemma lem7116473 : term113 = True.
Proof. exact (EQ_MP (@lem7116472) (@lem7116470)). Qed.
Lemma lem7116474 : term107 = True.
Proof. exact (TRANS (@lem7116469) (@lem7116473)). Qed.
Lemma lem7116475 : True = term107.
Proof. exact (SYM (@lem7116474)). Qed.
Lemma lem7116476 : term107.
Proof. exact (EQ_MP (@lem7116475) (@lem0)). Qed.
Lemma lem7116477 : term160 = term163.
Proof. exact (@lem7116466 (@lem7116476)). Qed.
Lemma lem7116479 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116480 : term118 = term15.
Proof. exact (@lem7116479 term24). Qed.
Lemma lem7116482 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116483 : term118 = term15.
Proof. exact (@lem7116482 term24). Qed.
Lemma lem7116484 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116485 : term119 = term108.
Proof. exact (MK_COMB (@lem7116484) (@lem7116483)). Qed.
Lemma lem7116486 : term163 = term159.
Proof. exact (MK_COMB (@lem7116485) (@lem7116480)). Qed.
Lemma lem7116488 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116489 : term159 = term164.
Proof. exact (@lem7116488 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7116490 : term164 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7116491 : term159 = False.
Proof. exact (TRANS (@lem7116489) (@lem7116490)). Qed.
Lemma lem7116492 : term163 = False.
Proof. exact (TRANS (@lem7116486) (@lem7116491)). Qed.
Lemma lem7116493 : term160 = False.
Proof. exact (TRANS (@lem7116477) (@lem7116492)). Qed.
Lemma lem7116494 : term159 = False.
Proof. exact (TRANS (@lem7116454) (@lem7116493)). Qed.
Lemma lem7116495 : term158 = False.
Proof. exact (TRANS (@lem7116445) (@lem7116494)). Qed.
Lemma lem7116496 (u : real) (h1 : term221 u) : False.
Proof. exact (EQ_MP (@lem7116495) (@lem7116442 u h1)). Qed.
Lemma lem7116497 (u : real) (h1 : term237 u) : term237 u.
Proof. exact (h1). Qed.
Lemma lem7116498 (u : real) (h1 : term237 u) : term219 u.
Proof. exact (proj2 (@lem7116497 u h1)). Qed.
Lemma lem7116499 (u : real) (h1 : term237 u) : term70 u.
Proof. exact (proj1 (@lem7116497 u h1)). Qed.
Lemma lem7116501 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7116502 : term106 = term107.
Proof. exact (@lem7116501 term15 term30). Qed.
Lemma lem7116504 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116505 : term30 = term63.
Proof. exact (@lem7116504 term24). Qed.
Lemma lem7116507 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116508 : term15 = term19.
Proof. exact (@lem7116507 (NUMERAL 0)). Qed.
Lemma lem7116509 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116510 : term108 = term109.
Proof. exact (MK_COMB (@lem7116509) (@lem7116508)). Qed.
Lemma lem7116511 : term107 = term110.
Proof. exact (MK_COMB (@lem7116510) (@lem7116505)). Qed.
Lemma lem7116512 : term111.
Proof. exact (@lem1980255 term15 term30 term30 term30). Qed.
Lemma lem7116514 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116515 : term107 = term113.
Proof. exact (@lem7116514 (NUMERAL 0) term24). Qed.
Lemma lem7116516 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116517 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116518 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116517 h1) (fun h1 : term113 = True => @lem7116516)). Qed.
Lemma lem7116519 : term113 = True.
Proof. exact (EQ_MP (@lem7116518) (@lem7116516)). Qed.
Lemma lem7116520 : term107 = True.
Proof. exact (TRANS (@lem7116515) (@lem7116519)). Qed.
Lemma lem7116521 : True = term107.
Proof. exact (SYM (@lem7116520)). Qed.
Lemma lem7116522 : term107.
Proof. exact (EQ_MP (@lem7116521) (@lem0)). Qed.
Lemma lem7116523 : term115.
Proof. exact (@lem7116512 (@lem7116522)). Qed.
Lemma lem7116525 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116526 : term107 = term113.
Proof. exact (@lem7116525 (NUMERAL 0) term24). Qed.
Lemma lem7116527 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116528 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116529 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116528 h1) (fun h1 : term113 = True => @lem7116527)). Qed.
Lemma lem7116530 : term113 = True.
Proof. exact (EQ_MP (@lem7116529) (@lem7116527)). Qed.
Lemma lem7116531 : term107 = True.
Proof. exact (TRANS (@lem7116526) (@lem7116530)). Qed.
Lemma lem7116532 : True = term107.
Proof. exact (SYM (@lem7116531)). Qed.
Lemma lem7116533 : term107.
Proof. exact (EQ_MP (@lem7116532) (@lem0)). Qed.
Lemma lem7116534 : term110 = term116.
Proof. exact (@lem7116523 (@lem7116533)). Qed.
Lemma lem7116536 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7116537 : term33 = term34.
Proof. exact (@lem7116536 term24 term24). Qed.
Lemma lem7116538 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116539 : term36 = term24.
Proof. exact (EQ_MP (@lem7116538) (@lem940073)). Qed.
Lemma lem7116540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116541 : term34 = term30.
Proof. exact (MK_COMB (@lem7116540) (@lem7116539)). Qed.
Lemma lem7116542 : term33 = term30.
Proof. exact (TRANS (@lem7116537) (@lem7116541)). Qed.
Lemma lem7116544 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116545 : term118 = term15.
Proof. exact (@lem7116544 term24). Qed.
Lemma lem7116546 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116547 : term119 = term108.
Proof. exact (MK_COMB (@lem7116546) (@lem7116545)). Qed.
Lemma lem7116548 : term116 = term107.
Proof. exact (MK_COMB (@lem7116547) (@lem7116542)). Qed.
Lemma lem7116550 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116551 : term107 = term113.
Proof. exact (@lem7116550 (NUMERAL 0) term24). Qed.
Lemma lem7116552 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116553 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116554 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116553 h1) (fun h1 : term113 = True => @lem7116552)). Qed.
Lemma lem7116555 : term113 = True.
Proof. exact (EQ_MP (@lem7116554) (@lem7116552)). Qed.
Lemma lem7116556 : term107 = True.
Proof. exact (TRANS (@lem7116551) (@lem7116555)). Qed.
Lemma lem7116557 : term116 = True.
Proof. exact (TRANS (@lem7116548) (@lem7116556)). Qed.
Lemma lem7116558 : term110 = True.
Proof. exact (TRANS (@lem7116534) (@lem7116557)). Qed.
Lemma lem7116559 : term107 = True.
Proof. exact (TRANS (@lem7116511) (@lem7116558)). Qed.
Lemma lem7116560 : term106 = True.
Proof. exact (TRANS (@lem7116502) (@lem7116559)). Qed.
Lemma lem7116561 : True = term106.
Proof. exact (SYM (@lem7116560)). Qed.
Lemma lem7116562 : term106.
Proof. exact (EQ_MP (@lem7116561) (@lem0)). Qed.
Lemma lem7116563 (u : real) (h1 : term237 u) : term255 u.
Proof. exact (conj (@lem7116562) (@lem7116498 u h1)). Qed.
Lemma lem7116565 (x : real) (y : real) : term256 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7116566 (u : real) : term257 u.
Proof. exact (@lem7116565 term30 (term45 u)). Qed.
Lemma lem7116567 (u : real) (h1 : term237 u) : term258 u.
Proof. exact (@lem7116566 u (@lem7116563 u h1)). Qed.
Lemma lem7116568 (u : real) : (term124 u) = (term45 u).
Proof. exact (@lem1982733 (term45 u)). Qed.
Lemma lem7116569 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7116570 (u : real) : (term259 u) = (term218 u).
Proof. exact (MK_COMB (@lem7116569) (@lem7116568 u)). Qed.
Lemma lem7116571 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7116572 (u : real) : (term258 u) = (term219 u).
Proof. exact (MK_COMB (@lem7116570 u) (@lem7116571)). Qed.
Lemma lem7116573 (u : real) (h1 : term237 u) : term219 u.
Proof. exact (EQ_MP (@lem7116572 u) (@lem7116567 u h1)). Qed.
Lemma lem7116575 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7116576 : term106 = term107.
Proof. exact (@lem7116575 term15 term30). Qed.
Lemma lem7116578 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116579 : term30 = term63.
Proof. exact (@lem7116578 term24). Qed.
Lemma lem7116581 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116582 : term15 = term19.
Proof. exact (@lem7116581 (NUMERAL 0)). Qed.
Lemma lem7116583 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116584 : term108 = term109.
Proof. exact (MK_COMB (@lem7116583) (@lem7116582)). Qed.
Lemma lem7116585 : term107 = term110.
Proof. exact (MK_COMB (@lem7116584) (@lem7116579)). Qed.
Lemma lem7116586 : term111.
Proof. exact (@lem1980255 term15 term30 term30 term30). Qed.
Lemma lem7116588 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116589 : term107 = term113.
Proof. exact (@lem7116588 (NUMERAL 0) term24). Qed.
Lemma lem7116590 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116591 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116592 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116591 h1) (fun h1 : term113 = True => @lem7116590)). Qed.
Lemma lem7116593 : term113 = True.
Proof. exact (EQ_MP (@lem7116592) (@lem7116590)). Qed.
Lemma lem7116594 : term107 = True.
Proof. exact (TRANS (@lem7116589) (@lem7116593)). Qed.
Lemma lem7116595 : True = term107.
Proof. exact (SYM (@lem7116594)). Qed.
Lemma lem7116596 : term107.
Proof. exact (EQ_MP (@lem7116595) (@lem0)). Qed.
Lemma lem7116597 : term115.
Proof. exact (@lem7116586 (@lem7116596)). Qed.
Lemma lem7116599 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116600 : term107 = term113.
Proof. exact (@lem7116599 (NUMERAL 0) term24). Qed.
Lemma lem7116601 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116602 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116603 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116602 h1) (fun h1 : term113 = True => @lem7116601)). Qed.
Lemma lem7116604 : term113 = True.
Proof. exact (EQ_MP (@lem7116603) (@lem7116601)). Qed.
Lemma lem7116605 : term107 = True.
Proof. exact (TRANS (@lem7116600) (@lem7116604)). Qed.
Lemma lem7116606 : True = term107.
Proof. exact (SYM (@lem7116605)). Qed.
Lemma lem7116607 : term107.
Proof. exact (EQ_MP (@lem7116606) (@lem0)). Qed.
Lemma lem7116608 : term110 = term116.
Proof. exact (@lem7116597 (@lem7116607)). Qed.
Lemma lem7116610 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7116611 : term33 = term34.
Proof. exact (@lem7116610 term24 term24). Qed.
Lemma lem7116612 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116613 : term36 = term24.
Proof. exact (EQ_MP (@lem7116612) (@lem940073)). Qed.
Lemma lem7116614 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116615 : term34 = term30.
Proof. exact (MK_COMB (@lem7116614) (@lem7116613)). Qed.
Lemma lem7116616 : term33 = term30.
Proof. exact (TRANS (@lem7116611) (@lem7116615)). Qed.
Lemma lem7116618 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116619 : term118 = term15.
Proof. exact (@lem7116618 term24). Qed.
Lemma lem7116620 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116621 : term119 = term108.
Proof. exact (MK_COMB (@lem7116620) (@lem7116619)). Qed.
Lemma lem7116622 : term116 = term107.
Proof. exact (MK_COMB (@lem7116621) (@lem7116616)). Qed.
Lemma lem7116624 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116625 : term107 = term113.
Proof. exact (@lem7116624 (NUMERAL 0) term24). Qed.
Lemma lem7116626 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116627 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116628 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116627 h1) (fun h1 : term113 = True => @lem7116626)). Qed.
Lemma lem7116629 : term113 = True.
Proof. exact (EQ_MP (@lem7116628) (@lem7116626)). Qed.
Lemma lem7116630 : term107 = True.
Proof. exact (TRANS (@lem7116625) (@lem7116629)). Qed.
Lemma lem7116631 : term116 = True.
Proof. exact (TRANS (@lem7116622) (@lem7116630)). Qed.
Lemma lem7116632 : term110 = True.
Proof. exact (TRANS (@lem7116608) (@lem7116631)). Qed.
Lemma lem7116633 : term107 = True.
Proof. exact (TRANS (@lem7116585) (@lem7116632)). Qed.
Lemma lem7116634 : term106 = True.
Proof. exact (TRANS (@lem7116576) (@lem7116633)). Qed.
Lemma lem7116635 : True = term106.
Proof. exact (SYM (@lem7116634)). Qed.
Lemma lem7116636 : term106.
Proof. exact (EQ_MP (@lem7116635) (@lem0)). Qed.
Lemma lem7116637 (u : real) (h1 : term237 u) : term166 u.
Proof. exact (conj (@lem7116636) (@lem7116499 u h1)). Qed.
Lemma lem7116639 (x : real) (y : real) : term121 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7116640 (u : real) : term167 u.
Proof. exact (@lem7116639 term30 u). Qed.
Lemma lem7116641 (u : real) (h1 : term237 u) : term168 u.
Proof. exact (@lem7116640 u (@lem7116637 u h1)). Qed.
Lemma lem7116642 (u : real) : (term66 u) = u.
Proof. exact (@lem1982733 u). Qed.
Lemma lem7116643 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7116644 (u : real) : (term169 u) = (real_gt u).
Proof. exact (MK_COMB (@lem7116643) (@lem7116642 u)). Qed.
Lemma lem7116645 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7116646 (u : real) : (term168 u) = (term70 u).
Proof. exact (MK_COMB (@lem7116644 u) (@lem7116645)). Qed.
Lemma lem7116647 (u : real) (h1 : term237 u) : term70 u.
Proof. exact (EQ_MP (@lem7116646 u) (@lem7116641 u h1)). Qed.
Lemma lem7116648 (u : real) (h1 : term237 u) : term237 u.
Proof. exact (conj (@lem7116647 u h1) (@lem7116573 u h1)). Qed.
Lemma lem7116650 (x : real) (y : real) : term260 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem7116651 (u : real) : term261 u.
Proof. exact (@lem7116650 u (term45 u)). Qed.
Lemma lem7116652 (u : real) (h1 : term237 u) : term132 u.
Proof. exact (@lem7116651 u (@lem7116648 u h1)). Qed.
Lemma lem7116653 (u : real) : (term133 u) = (term134 u).
Proof. exact (@lem1982715 term22 u). Qed.
Lemma lem7116655 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116656 : term30 = term63.
Proof. exact (@lem7116655 term24). Qed.
Lemma lem7116658 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7116659 : term22 = term23.
Proof. exact (@lem7116658 term24). Qed.
Lemma lem7116660 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7116661 : term135 = term136.
Proof. exact (MK_COMB (@lem7116660) (@lem7116659)). Qed.
Lemma lem7116662 : term137 = term138.
Proof. exact (MK_COMB (@lem7116661) (@lem7116656)). Qed.
Lemma lem7116663 : term139.
Proof. exact (@lem1981473 term22 term30 term30 term30 term15 term30). Qed.
Lemma lem7116665 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116666 : term107 = term113.
Proof. exact (@lem7116665 (NUMERAL 0) term24). Qed.
Lemma lem7116667 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116668 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116669 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116668 h1) (fun h1 : term113 = True => @lem7116667)). Qed.
Lemma lem7116670 : term113 = True.
Proof. exact (EQ_MP (@lem7116669) (@lem7116667)). Qed.
Lemma lem7116671 : term107 = True.
Proof. exact (TRANS (@lem7116666) (@lem7116670)). Qed.
Lemma lem7116672 : True = term107.
Proof. exact (SYM (@lem7116671)). Qed.
Lemma lem7116673 : term107.
Proof. exact (EQ_MP (@lem7116672) (@lem0)). Qed.
Lemma lem7116674 : term140.
Proof. exact (@lem7116663 (@lem7116673)). Qed.
Lemma lem7116676 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116677 : term107 = term113.
Proof. exact (@lem7116676 (NUMERAL 0) term24). Qed.
Lemma lem7116678 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116679 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116680 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116679 h1) (fun h1 : term113 = True => @lem7116678)). Qed.
Lemma lem7116681 : term113 = True.
Proof. exact (EQ_MP (@lem7116680) (@lem7116678)). Qed.
Lemma lem7116682 : term107 = True.
Proof. exact (TRANS (@lem7116677) (@lem7116681)). Qed.
Lemma lem7116683 : True = term107.
Proof. exact (SYM (@lem7116682)). Qed.
Lemma lem7116684 : term107.
Proof. exact (EQ_MP (@lem7116683) (@lem0)). Qed.
Lemma lem7116685 : term141.
Proof. exact (@lem7116674 (@lem7116684)). Qed.
Lemma lem7116687 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116688 : term107 = term113.
Proof. exact (@lem7116687 (NUMERAL 0) term24). Qed.
Lemma lem7116689 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116690 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116691 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116690 h1) (fun h1 : term113 = True => @lem7116689)). Qed.
Lemma lem7116692 : term113 = True.
Proof. exact (EQ_MP (@lem7116691) (@lem7116689)). Qed.
Lemma lem7116693 : term107 = True.
Proof. exact (TRANS (@lem7116688) (@lem7116692)). Qed.
Lemma lem7116694 : True = term107.
Proof. exact (SYM (@lem7116693)). Qed.
Lemma lem7116695 : term107.
Proof. exact (EQ_MP (@lem7116694) (@lem0)). Qed.
Lemma lem7116696 : term142.
Proof. exact (@lem7116685 (@lem7116695)). Qed.
Lemma lem7116698 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7116699 : term33 = term34.
Proof. exact (@lem7116698 term24 term24). Qed.
Lemma lem7116700 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116701 : term36 = term24.
Proof. exact (EQ_MP (@lem7116700) (@lem940073)). Qed.
Lemma lem7116702 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116703 : term34 = term30.
Proof. exact (MK_COMB (@lem7116702) (@lem7116701)). Qed.
Lemma lem7116704 : term33 = term30.
Proof. exact (TRANS (@lem7116699) (@lem7116703)). Qed.
Lemma lem7116706 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7116707 : term145 = term146.
Proof. exact (@lem7116706 term24 term24). Qed.
Lemma lem7116708 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116709 : term36 = term24.
Proof. exact (EQ_MP (@lem7116708) (@lem940073)). Qed.
Lemma lem7116710 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116711 : term34 = term30.
Proof. exact (MK_COMB (@lem7116710) (@lem7116709)). Qed.
Lemma lem7116712 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7116713 : term146 = term22.
Proof. exact (MK_COMB (@lem7116712) (@lem7116711)). Qed.
Lemma lem7116714 : term145 = term22.
Proof. exact (TRANS (@lem7116707) (@lem7116713)). Qed.
Lemma lem7116715 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7116716 : term147 = term135.
Proof. exact (MK_COMB (@lem7116715) (@lem7116714)). Qed.
Lemma lem7116717 : term148 = term137.
Proof. exact (MK_COMB (@lem7116716) (@lem7116704)). Qed.
Lemma lem7116719 (m : nat) : (term149 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7116720 : term137 = term15.
Proof. exact (@lem7116719 term24). Qed.
Lemma lem7116721 : term148 = term15.
Proof. exact (TRANS (@lem7116717) (@lem7116720)). Qed.
Lemma lem7116722 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7116723 : term150 = term151.
Proof. exact (MK_COMB (@lem7116722) (@lem7116721)). Qed.
Lemma lem7116724 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem7116725 : term152 = term118.
Proof. exact (MK_COMB (@lem7116723) (@lem7116724)). Qed.
Lemma lem7116727 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116728 : term118 = term15.
Proof. exact (@lem7116727 term24). Qed.
Lemma lem7116729 : term152 = term15.
Proof. exact (TRANS (@lem7116725) (@lem7116728)). Qed.
Lemma lem7116731 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7116732 : term33 = term34.
Proof. exact (@lem7116731 term24 term24). Qed.
Lemma lem7116733 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116734 : term36 = term24.
Proof. exact (EQ_MP (@lem7116733) (@lem940073)). Qed.
Lemma lem7116735 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116736 : term34 = term30.
Proof. exact (MK_COMB (@lem7116735) (@lem7116734)). Qed.
Lemma lem7116737 : term33 = term30.
Proof. exact (TRANS (@lem7116732) (@lem7116736)). Qed.
Lemma lem7116738 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7116739 : term153 = term118.
Proof. exact (MK_COMB (@lem7116738) (@lem7116737)). Qed.
Lemma lem7116741 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116742 : term118 = term15.
Proof. exact (@lem7116741 term24). Qed.
Lemma lem7116743 : term153 = term15.
Proof. exact (TRANS (@lem7116739) (@lem7116742)). Qed.
Lemma lem7116744 : term15 = term153.
Proof. exact (SYM (@lem7116743)). Qed.
Lemma lem7116745 : term152 = term153.
Proof. exact (TRANS (@lem7116729) (@lem7116744)). Qed.
Lemma lem7116746 : term138 = term19.
Proof. exact (@lem7116696 (@lem7116745)). Qed.
Lemma lem7116747 : term137 = term19.
Proof. exact (TRANS (@lem7116662) (@lem7116746)). Qed.
Lemma lem7116749 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7116750 : term19 = term15.
Proof. exact (@lem7116749 term15). Qed.
Lemma lem7116751 : term137 = term15.
Proof. exact (TRANS (@lem7116747) (@lem7116750)). Qed.
Lemma lem7116752 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7116753 : term154 = term151.
Proof. exact (MK_COMB (@lem7116752) (@lem7116751)). Qed.
Lemma lem7116754 (u : real) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7116755 (u : real) : (term134 u) = (term155 u).
Proof. exact (MK_COMB (@lem7116753) (@lem7116754 u)). Qed.
Lemma lem7116756 (u : real) : (term133 u) = (term155 u).
Proof. exact (TRANS (@lem7116653 u) (@lem7116755 u)). Qed.
Lemma lem7116757 (u : real) : (term155 u) = term15.
Proof. exact (@lem1982719 u). Qed.
Lemma lem7116758 (u : real) : (term133 u) = term15.
Proof. exact (TRANS (@lem7116756 u) (@lem7116757 u)). Qed.
Lemma lem7116759 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7116760 (u : real) : (term156 u) = term157.
Proof. exact (MK_COMB (@lem7116759) (@lem7116758 u)). Qed.
Lemma lem7116761 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7116762 (u : real) : (term132 u) = term158.
Proof. exact (MK_COMB (@lem7116760 u) (@lem7116761)). Qed.
Lemma lem7116763 (u : real) (h1 : term237 u) : term158.
Proof. exact (EQ_MP (@lem7116762 u) (@lem7116652 u h1)). Qed.
Lemma lem7116765 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7116766 : term158 = term159.
Proof. exact (@lem7116765 term15 term15). Qed.
Lemma lem7116768 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116769 : term15 = term19.
Proof. exact (@lem7116768 (NUMERAL 0)). Qed.
Lemma lem7116771 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116772 : term15 = term19.
Proof. exact (@lem7116771 (NUMERAL 0)). Qed.
Lemma lem7116773 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116774 : term108 = term109.
Proof. exact (MK_COMB (@lem7116773) (@lem7116772)). Qed.
Lemma lem7116775 : term159 = term160.
Proof. exact (MK_COMB (@lem7116774) (@lem7116769)). Qed.
Lemma lem7116776 : term161.
Proof. exact (@lem1980255 term15 term30 term15 term30). Qed.
Lemma lem7116778 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116779 : term107 = term113.
Proof. exact (@lem7116778 (NUMERAL 0) term24). Qed.
Lemma lem7116780 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116781 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116782 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116781 h1) (fun h1 : term113 = True => @lem7116780)). Qed.
Lemma lem7116783 : term113 = True.
Proof. exact (EQ_MP (@lem7116782) (@lem7116780)). Qed.
Lemma lem7116784 : term107 = True.
Proof. exact (TRANS (@lem7116779) (@lem7116783)). Qed.
Lemma lem7116785 : True = term107.
Proof. exact (SYM (@lem7116784)). Qed.
Lemma lem7116786 : term107.
Proof. exact (EQ_MP (@lem7116785) (@lem0)). Qed.
Lemma lem7116787 : term162.
Proof. exact (@lem7116776 (@lem7116786)). Qed.
Lemma lem7116789 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116790 : term107 = term113.
Proof. exact (@lem7116789 (NUMERAL 0) term24). Qed.
Lemma lem7116791 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116792 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116793 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116792 h1) (fun h1 : term113 = True => @lem7116791)). Qed.
Lemma lem7116794 : term113 = True.
Proof. exact (EQ_MP (@lem7116793) (@lem7116791)). Qed.
Lemma lem7116795 : term107 = True.
Proof. exact (TRANS (@lem7116790) (@lem7116794)). Qed.
Lemma lem7116796 : True = term107.
Proof. exact (SYM (@lem7116795)). Qed.
Lemma lem7116797 : term107.
Proof. exact (EQ_MP (@lem7116796) (@lem0)). Qed.
Lemma lem7116798 : term160 = term163.
Proof. exact (@lem7116787 (@lem7116797)). Qed.
Lemma lem7116800 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116801 : term118 = term15.
Proof. exact (@lem7116800 term24). Qed.
Lemma lem7116803 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116804 : term118 = term15.
Proof. exact (@lem7116803 term24). Qed.
Lemma lem7116805 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116806 : term119 = term108.
Proof. exact (MK_COMB (@lem7116805) (@lem7116804)). Qed.
Lemma lem7116807 : term163 = term159.
Proof. exact (MK_COMB (@lem7116806) (@lem7116801)). Qed.
Lemma lem7116809 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116810 : term159 = term164.
Proof. exact (@lem7116809 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7116811 : term164 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7116812 : term159 = False.
Proof. exact (TRANS (@lem7116810) (@lem7116811)). Qed.
Lemma lem7116813 : term163 = False.
Proof. exact (TRANS (@lem7116807) (@lem7116812)). Qed.
Lemma lem7116814 : term160 = False.
Proof. exact (TRANS (@lem7116798) (@lem7116813)). Qed.
Lemma lem7116815 : term159 = False.
Proof. exact (TRANS (@lem7116775) (@lem7116814)). Qed.
Lemma lem7116816 : term158 = False.
Proof. exact (TRANS (@lem7116766) (@lem7116815)). Qed.
Lemma lem7116817 (u : real) (h1 : term237 u) : False.
Proof. exact (EQ_MP (@lem7116816) (@lem7116763 u h1)). Qed.
Lemma lem7116818 (u : real) (h1 : term239 u) : False.
Proof. exact (or_elim (@lem7116175 u h1) (fun h0 : term221 u => @lem7116496 u h0) (fun h0 : term237 u => @lem7116817 u h0)). Qed.
Lemma lem7116819 (u : real) (h1 : term252 u) : term252 u.
Proof. exact (h1). Qed.
Lemma lem7116820 (u : real) (h1 : term246 u) : term246 u.
Proof. exact (h1). Qed.
Lemma lem7116821 (u : real) (h1 : term246 u) : term74 u.
Proof. exact (proj2 (@lem7116820 u h1)). Qed.
Lemma lem7116822 (u : real) (h1 : term246 u) : term242 u.
Proof. exact (proj1 (@lem7116820 u h1)). Qed.
Lemma lem7116824 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7116825 : term106 = term107.
Proof. exact (@lem7116824 term15 term30). Qed.
Lemma lem7116827 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116828 : term30 = term63.
Proof. exact (@lem7116827 term24). Qed.
Lemma lem7116830 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116831 : term15 = term19.
Proof. exact (@lem7116830 (NUMERAL 0)). Qed.
Lemma lem7116832 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116833 : term108 = term109.
Proof. exact (MK_COMB (@lem7116832) (@lem7116831)). Qed.
Lemma lem7116834 : term107 = term110.
Proof. exact (MK_COMB (@lem7116833) (@lem7116828)). Qed.
Lemma lem7116835 : term111.
Proof. exact (@lem1980255 term15 term30 term30 term30). Qed.
Lemma lem7116837 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116838 : term107 = term113.
Proof. exact (@lem7116837 (NUMERAL 0) term24). Qed.
Lemma lem7116839 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116840 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116841 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116840 h1) (fun h1 : term113 = True => @lem7116839)). Qed.
Lemma lem7116842 : term113 = True.
Proof. exact (EQ_MP (@lem7116841) (@lem7116839)). Qed.
Lemma lem7116843 : term107 = True.
Proof. exact (TRANS (@lem7116838) (@lem7116842)). Qed.
Lemma lem7116844 : True = term107.
Proof. exact (SYM (@lem7116843)). Qed.
Lemma lem7116845 : term107.
Proof. exact (EQ_MP (@lem7116844) (@lem0)). Qed.
Lemma lem7116846 : term115.
Proof. exact (@lem7116835 (@lem7116845)). Qed.
Lemma lem7116848 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116849 : term107 = term113.
Proof. exact (@lem7116848 (NUMERAL 0) term24). Qed.
Lemma lem7116850 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116851 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116852 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116851 h1) (fun h1 : term113 = True => @lem7116850)). Qed.
Lemma lem7116853 : term113 = True.
Proof. exact (EQ_MP (@lem7116852) (@lem7116850)). Qed.
Lemma lem7116854 : term107 = True.
Proof. exact (TRANS (@lem7116849) (@lem7116853)). Qed.
Lemma lem7116855 : True = term107.
Proof. exact (SYM (@lem7116854)). Qed.
Lemma lem7116856 : term107.
Proof. exact (EQ_MP (@lem7116855) (@lem0)). Qed.
Lemma lem7116857 : term110 = term116.
Proof. exact (@lem7116846 (@lem7116856)). Qed.
Lemma lem7116859 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7116860 : term33 = term34.
Proof. exact (@lem7116859 term24 term24). Qed.
Lemma lem7116861 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116862 : term36 = term24.
Proof. exact (EQ_MP (@lem7116861) (@lem940073)). Qed.
Lemma lem7116863 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116864 : term34 = term30.
Proof. exact (MK_COMB (@lem7116863) (@lem7116862)). Qed.
Lemma lem7116865 : term33 = term30.
Proof. exact (TRANS (@lem7116860) (@lem7116864)). Qed.
Lemma lem7116867 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116868 : term118 = term15.
Proof. exact (@lem7116867 term24). Qed.
Lemma lem7116869 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116870 : term119 = term108.
Proof. exact (MK_COMB (@lem7116869) (@lem7116868)). Qed.
Lemma lem7116871 : term116 = term107.
Proof. exact (MK_COMB (@lem7116870) (@lem7116865)). Qed.
Lemma lem7116873 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116874 : term107 = term113.
Proof. exact (@lem7116873 (NUMERAL 0) term24). Qed.
Lemma lem7116875 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116876 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116877 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116876 h1) (fun h1 : term113 = True => @lem7116875)). Qed.
Lemma lem7116878 : term113 = True.
Proof. exact (EQ_MP (@lem7116877) (@lem7116875)). Qed.
Lemma lem7116879 : term107 = True.
Proof. exact (TRANS (@lem7116874) (@lem7116878)). Qed.
Lemma lem7116880 : term116 = True.
Proof. exact (TRANS (@lem7116871) (@lem7116879)). Qed.
Lemma lem7116881 : term110 = True.
Proof. exact (TRANS (@lem7116857) (@lem7116880)). Qed.
Lemma lem7116882 : term107 = True.
Proof. exact (TRANS (@lem7116834) (@lem7116881)). Qed.
Lemma lem7116883 : term106 = True.
Proof. exact (TRANS (@lem7116825) (@lem7116882)). Qed.
Lemma lem7116884 : True = term106.
Proof. exact (SYM (@lem7116883)). Qed.
Lemma lem7116885 : term106.
Proof. exact (EQ_MP (@lem7116884) (@lem0)). Qed.
Lemma lem7116886 (u : real) (h1 : term246 u) : term262 u.
Proof. exact (conj (@lem7116885) (@lem7116822 u h1)). Qed.
Lemma lem7116888 (x : real) (y : real) : term256 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7116889 (u : real) : term263 u.
Proof. exact (@lem7116888 term30 u). Qed.
Lemma lem7116890 (u : real) (h1 : term246 u) : term264 u.
Proof. exact (@lem7116889 u (@lem7116886 u h1)). Qed.
Lemma lem7116891 (u : real) : (term66 u) = u.
Proof. exact (@lem1982733 u). Qed.
Lemma lem7116892 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7116893 (u : real) : (term265 u) = (real_ge u).
Proof. exact (MK_COMB (@lem7116892) (@lem7116891 u)). Qed.
Lemma lem7116894 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7116895 (u : real) : (term264 u) = (term242 u).
Proof. exact (MK_COMB (@lem7116893 u) (@lem7116894)). Qed.
Lemma lem7116896 (u : real) (h1 : term246 u) : term242 u.
Proof. exact (EQ_MP (@lem7116895 u) (@lem7116890 u h1)). Qed.
Lemma lem7116898 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7116899 : term106 = term107.
Proof. exact (@lem7116898 term15 term30). Qed.
Lemma lem7116901 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116902 : term30 = term63.
Proof. exact (@lem7116901 term24). Qed.
Lemma lem7116904 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116905 : term15 = term19.
Proof. exact (@lem7116904 (NUMERAL 0)). Qed.
Lemma lem7116906 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116907 : term108 = term109.
Proof. exact (MK_COMB (@lem7116906) (@lem7116905)). Qed.
Lemma lem7116908 : term107 = term110.
Proof. exact (MK_COMB (@lem7116907) (@lem7116902)). Qed.
Lemma lem7116909 : term111.
Proof. exact (@lem1980255 term15 term30 term30 term30). Qed.
Lemma lem7116911 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116912 : term107 = term113.
Proof. exact (@lem7116911 (NUMERAL 0) term24). Qed.
Lemma lem7116913 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116914 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116915 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116914 h1) (fun h1 : term113 = True => @lem7116913)). Qed.
Lemma lem7116916 : term113 = True.
Proof. exact (EQ_MP (@lem7116915) (@lem7116913)). Qed.
Lemma lem7116917 : term107 = True.
Proof. exact (TRANS (@lem7116912) (@lem7116916)). Qed.
Lemma lem7116918 : True = term107.
Proof. exact (SYM (@lem7116917)). Qed.
Lemma lem7116919 : term107.
Proof. exact (EQ_MP (@lem7116918) (@lem0)). Qed.
Lemma lem7116920 : term115.
Proof. exact (@lem7116909 (@lem7116919)). Qed.
Lemma lem7116922 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116923 : term107 = term113.
Proof. exact (@lem7116922 (NUMERAL 0) term24). Qed.
Lemma lem7116924 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116925 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116926 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116925 h1) (fun h1 : term113 = True => @lem7116924)). Qed.
Lemma lem7116927 : term113 = True.
Proof. exact (EQ_MP (@lem7116926) (@lem7116924)). Qed.
Lemma lem7116928 : term107 = True.
Proof. exact (TRANS (@lem7116923) (@lem7116927)). Qed.
Lemma lem7116929 : True = term107.
Proof. exact (SYM (@lem7116928)). Qed.
Lemma lem7116930 : term107.
Proof. exact (EQ_MP (@lem7116929) (@lem0)). Qed.
Lemma lem7116931 : term110 = term116.
Proof. exact (@lem7116920 (@lem7116930)). Qed.
Lemma lem7116933 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7116934 : term33 = term34.
Proof. exact (@lem7116933 term24 term24). Qed.
Lemma lem7116935 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7116936 : term36 = term24.
Proof. exact (EQ_MP (@lem7116935) (@lem940073)). Qed.
Lemma lem7116937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7116938 : term34 = term30.
Proof. exact (MK_COMB (@lem7116937) (@lem7116936)). Qed.
Lemma lem7116939 : term33 = term30.
Proof. exact (TRANS (@lem7116934) (@lem7116938)). Qed.
Lemma lem7116941 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7116942 : term118 = term15.
Proof. exact (@lem7116941 term24). Qed.
Lemma lem7116943 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7116944 : term119 = term108.
Proof. exact (MK_COMB (@lem7116943) (@lem7116942)). Qed.
Lemma lem7116945 : term116 = term107.
Proof. exact (MK_COMB (@lem7116944) (@lem7116939)). Qed.
Lemma lem7116947 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116948 : term107 = term113.
Proof. exact (@lem7116947 (NUMERAL 0) term24). Qed.
Lemma lem7116949 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116950 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116951 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116950 h1) (fun h1 : term113 = True => @lem7116949)). Qed.
Lemma lem7116952 : term113 = True.
Proof. exact (EQ_MP (@lem7116951) (@lem7116949)). Qed.
Lemma lem7116953 : term107 = True.
Proof. exact (TRANS (@lem7116948) (@lem7116952)). Qed.
Lemma lem7116954 : term116 = True.
Proof. exact (TRANS (@lem7116945) (@lem7116953)). Qed.
Lemma lem7116955 : term110 = True.
Proof. exact (TRANS (@lem7116931) (@lem7116954)). Qed.
Lemma lem7116956 : term107 = True.
Proof. exact (TRANS (@lem7116908) (@lem7116955)). Qed.
Lemma lem7116957 : term106 = True.
Proof. exact (TRANS (@lem7116899) (@lem7116956)). Qed.
Lemma lem7116958 : True = term106.
Proof. exact (SYM (@lem7116957)). Qed.
Lemma lem7116959 : term106.
Proof. exact (EQ_MP (@lem7116958) (@lem0)). Qed.
Lemma lem7116960 (u : real) (h1 : term246 u) : term120 u.
Proof. exact (conj (@lem7116959) (@lem7116821 u h1)). Qed.
Lemma lem7116962 (x : real) (y : real) : term121 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7116963 (u : real) : term122 u.
Proof. exact (@lem7116962 term30 (term45 u)). Qed.
Lemma lem7116964 (u : real) (h1 : term246 u) : term123 u.
Proof. exact (@lem7116963 u (@lem7116960 u h1)). Qed.
Lemma lem7116965 (u : real) : (term124 u) = (term45 u).
Proof. exact (@lem1982733 (term45 u)). Qed.
Lemma lem7116966 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7116967 (u : real) : (term125 u) = (term72 u).
Proof. exact (MK_COMB (@lem7116966) (@lem7116965 u)). Qed.
Lemma lem7116968 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7116969 (u : real) : (term123 u) = (term74 u).
Proof. exact (MK_COMB (@lem7116967 u) (@lem7116968)). Qed.
Lemma lem7116970 (u : real) (h1 : term246 u) : term74 u.
Proof. exact (EQ_MP (@lem7116969 u) (@lem7116964 u h1)). Qed.
Lemma lem7116971 (u : real) (h1 : term246 u) : term250 u.
Proof. exact (conj (@lem7116970 u h1) (@lem7116896 u h1)). Qed.
Lemma lem7116973 (x : real) (y : real) : term260 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem7116974 (u : real) : term266 u.
Proof. exact (@lem7116973 (term45 u) u). Qed.
Lemma lem7116975 (u : real) (h1 : term246 u) : term173 u.
Proof. exact (@lem7116974 u (@lem7116971 u h1)). Qed.
Lemma lem7116976 (u : real) : (term174 u) = (term134 u).
Proof. exact (@lem1982713 term22 u). Qed.
Lemma lem7116978 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7116979 : term30 = term63.
Proof. exact (@lem7116978 term24). Qed.
Lemma lem7116981 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7116982 : term22 = term23.
Proof. exact (@lem7116981 term24). Qed.
Lemma lem7116983 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7116984 : term135 = term136.
Proof. exact (MK_COMB (@lem7116983) (@lem7116982)). Qed.
Lemma lem7116985 : term137 = term138.
Proof. exact (MK_COMB (@lem7116984) (@lem7116979)). Qed.
Lemma lem7116986 : term139.
Proof. exact (@lem1981473 term22 term30 term30 term30 term15 term30). Qed.
Lemma lem7116988 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7116989 : term107 = term113.
Proof. exact (@lem7116988 (NUMERAL 0) term24). Qed.
Lemma lem7116990 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7116991 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7116992 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7116991 h1) (fun h1 : term113 = True => @lem7116990)). Qed.
Lemma lem7116993 : term113 = True.
Proof. exact (EQ_MP (@lem7116992) (@lem7116990)). Qed.
Lemma lem7116994 : term107 = True.
Proof. exact (TRANS (@lem7116989) (@lem7116993)). Qed.
Lemma lem7116995 : True = term107.
Proof. exact (SYM (@lem7116994)). Qed.
Lemma lem7116996 : term107.
Proof. exact (EQ_MP (@lem7116995) (@lem0)). Qed.
Lemma lem7116997 : term140.
Proof. exact (@lem7116986 (@lem7116996)). Qed.
Lemma lem7116999 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117000 : term107 = term113.
Proof. exact (@lem7116999 (NUMERAL 0) term24). Qed.
Lemma lem7117001 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117002 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117003 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117002 h1) (fun h1 : term113 = True => @lem7117001)). Qed.
Lemma lem7117004 : term113 = True.
Proof. exact (EQ_MP (@lem7117003) (@lem7117001)). Qed.
Lemma lem7117005 : term107 = True.
Proof. exact (TRANS (@lem7117000) (@lem7117004)). Qed.
Lemma lem7117006 : True = term107.
Proof. exact (SYM (@lem7117005)). Qed.
Lemma lem7117007 : term107.
Proof. exact (EQ_MP (@lem7117006) (@lem0)). Qed.
Lemma lem7117008 : term141.
Proof. exact (@lem7116997 (@lem7117007)). Qed.
Lemma lem7117010 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117011 : term107 = term113.
Proof. exact (@lem7117010 (NUMERAL 0) term24). Qed.
Lemma lem7117012 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117013 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117014 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117013 h1) (fun h1 : term113 = True => @lem7117012)). Qed.
Lemma lem7117015 : term113 = True.
Proof. exact (EQ_MP (@lem7117014) (@lem7117012)). Qed.
Lemma lem7117016 : term107 = True.
Proof. exact (TRANS (@lem7117011) (@lem7117015)). Qed.
Lemma lem7117017 : True = term107.
Proof. exact (SYM (@lem7117016)). Qed.
Lemma lem7117018 : term107.
Proof. exact (EQ_MP (@lem7117017) (@lem0)). Qed.
Lemma lem7117019 : term142.
Proof. exact (@lem7117008 (@lem7117018)). Qed.
Lemma lem7117021 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7117022 : term33 = term34.
Proof. exact (@lem7117021 term24 term24). Qed.
Lemma lem7117023 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7117024 : term36 = term24.
Proof. exact (EQ_MP (@lem7117023) (@lem940073)). Qed.
Lemma lem7117025 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7117026 : term34 = term30.
Proof. exact (MK_COMB (@lem7117025) (@lem7117024)). Qed.
Lemma lem7117027 : term33 = term30.
Proof. exact (TRANS (@lem7117022) (@lem7117026)). Qed.
Lemma lem7117029 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7117030 : term145 = term146.
Proof. exact (@lem7117029 term24 term24). Qed.
Lemma lem7117031 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7117032 : term36 = term24.
Proof. exact (EQ_MP (@lem7117031) (@lem940073)). Qed.
Lemma lem7117033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7117034 : term34 = term30.
Proof. exact (MK_COMB (@lem7117033) (@lem7117032)). Qed.
Lemma lem7117035 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7117036 : term146 = term22.
Proof. exact (MK_COMB (@lem7117035) (@lem7117034)). Qed.
Lemma lem7117037 : term145 = term22.
Proof. exact (TRANS (@lem7117030) (@lem7117036)). Qed.
Lemma lem7117038 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7117039 : term147 = term135.
Proof. exact (MK_COMB (@lem7117038) (@lem7117037)). Qed.
Lemma lem7117040 : term148 = term137.
Proof. exact (MK_COMB (@lem7117039) (@lem7117027)). Qed.
Lemma lem7117042 (m : nat) : (term149 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7117043 : term137 = term15.
Proof. exact (@lem7117042 term24). Qed.
Lemma lem7117044 : term148 = term15.
Proof. exact (TRANS (@lem7117040) (@lem7117043)). Qed.
Lemma lem7117045 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7117046 : term150 = term151.
Proof. exact (MK_COMB (@lem7117045) (@lem7117044)). Qed.
Lemma lem7117047 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem7117048 : term152 = term118.
Proof. exact (MK_COMB (@lem7117046) (@lem7117047)). Qed.
Lemma lem7117050 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7117051 : term118 = term15.
Proof. exact (@lem7117050 term24). Qed.
Lemma lem7117052 : term152 = term15.
Proof. exact (TRANS (@lem7117048) (@lem7117051)). Qed.
Lemma lem7117054 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7117055 : term33 = term34.
Proof. exact (@lem7117054 term24 term24). Qed.
Lemma lem7117056 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7117057 : term36 = term24.
Proof. exact (EQ_MP (@lem7117056) (@lem940073)). Qed.
Lemma lem7117058 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7117059 : term34 = term30.
Proof. exact (MK_COMB (@lem7117058) (@lem7117057)). Qed.
Lemma lem7117060 : term33 = term30.
Proof. exact (TRANS (@lem7117055) (@lem7117059)). Qed.
Lemma lem7117061 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7117062 : term153 = term118.
Proof. exact (MK_COMB (@lem7117061) (@lem7117060)). Qed.
Lemma lem7117064 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7117065 : term118 = term15.
Proof. exact (@lem7117064 term24). Qed.
Lemma lem7117066 : term153 = term15.
Proof. exact (TRANS (@lem7117062) (@lem7117065)). Qed.
Lemma lem7117067 : term15 = term153.
Proof. exact (SYM (@lem7117066)). Qed.
Lemma lem7117068 : term152 = term153.
Proof. exact (TRANS (@lem7117052) (@lem7117067)). Qed.
Lemma lem7117069 : term138 = term19.
Proof. exact (@lem7117019 (@lem7117068)). Qed.
Lemma lem7117070 : term137 = term19.
Proof. exact (TRANS (@lem7116985) (@lem7117069)). Qed.
Lemma lem7117072 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7117073 : term19 = term15.
Proof. exact (@lem7117072 term15). Qed.
Lemma lem7117074 : term137 = term15.
Proof. exact (TRANS (@lem7117070) (@lem7117073)). Qed.
Lemma lem7117075 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7117076 : term154 = term151.
Proof. exact (MK_COMB (@lem7117075) (@lem7117074)). Qed.
Lemma lem7117077 (u : real) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7117078 (u : real) : (term134 u) = (term155 u).
Proof. exact (MK_COMB (@lem7117076) (@lem7117077 u)). Qed.
Lemma lem7117079 (u : real) : (term174 u) = (term155 u).
Proof. exact (TRANS (@lem7116976 u) (@lem7117078 u)). Qed.
Lemma lem7117080 (u : real) : (term155 u) = term15.
Proof. exact (@lem1982719 u). Qed.
Lemma lem7117081 (u : real) : (term174 u) = term15.
Proof. exact (TRANS (@lem7117079 u) (@lem7117080 u)). Qed.
Lemma lem7117082 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7117083 (u : real) : (term175 u) = term157.
Proof. exact (MK_COMB (@lem7117082) (@lem7117081 u)). Qed.
Lemma lem7117084 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7117085 (u : real) : (term173 u) = term158.
Proof. exact (MK_COMB (@lem7117083 u) (@lem7117084)). Qed.
Lemma lem7117086 (u : real) (h1 : term246 u) : term158.
Proof. exact (EQ_MP (@lem7117085 u) (@lem7116975 u h1)). Qed.
Lemma lem7117088 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7117089 : term158 = term159.
Proof. exact (@lem7117088 term15 term15). Qed.
Lemma lem7117091 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7117092 : term15 = term19.
Proof. exact (@lem7117091 (NUMERAL 0)). Qed.
Lemma lem7117094 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7117095 : term15 = term19.
Proof. exact (@lem7117094 (NUMERAL 0)). Qed.
Lemma lem7117096 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7117097 : term108 = term109.
Proof. exact (MK_COMB (@lem7117096) (@lem7117095)). Qed.
Lemma lem7117098 : term159 = term160.
Proof. exact (MK_COMB (@lem7117097) (@lem7117092)). Qed.
Lemma lem7117099 : term161.
Proof. exact (@lem1980255 term15 term30 term15 term30). Qed.
Lemma lem7117101 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117102 : term107 = term113.
Proof. exact (@lem7117101 (NUMERAL 0) term24). Qed.
Lemma lem7117103 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117104 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117105 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117104 h1) (fun h1 : term113 = True => @lem7117103)). Qed.
Lemma lem7117106 : term113 = True.
Proof. exact (EQ_MP (@lem7117105) (@lem7117103)). Qed.
Lemma lem7117107 : term107 = True.
Proof. exact (TRANS (@lem7117102) (@lem7117106)). Qed.
Lemma lem7117108 : True = term107.
Proof. exact (SYM (@lem7117107)). Qed.
Lemma lem7117109 : term107.
Proof. exact (EQ_MP (@lem7117108) (@lem0)). Qed.
Lemma lem7117110 : term162.
Proof. exact (@lem7117099 (@lem7117109)). Qed.
Lemma lem7117112 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117113 : term107 = term113.
Proof. exact (@lem7117112 (NUMERAL 0) term24). Qed.
Lemma lem7117114 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117115 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117116 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117115 h1) (fun h1 : term113 = True => @lem7117114)). Qed.
Lemma lem7117117 : term113 = True.
Proof. exact (EQ_MP (@lem7117116) (@lem7117114)). Qed.
Lemma lem7117118 : term107 = True.
Proof. exact (TRANS (@lem7117113) (@lem7117117)). Qed.
Lemma lem7117119 : True = term107.
Proof. exact (SYM (@lem7117118)). Qed.
Lemma lem7117120 : term107.
Proof. exact (EQ_MP (@lem7117119) (@lem0)). Qed.
Lemma lem7117121 : term160 = term163.
Proof. exact (@lem7117110 (@lem7117120)). Qed.
Lemma lem7117123 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7117124 : term118 = term15.
Proof. exact (@lem7117123 term24). Qed.
Lemma lem7117126 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7117127 : term118 = term15.
Proof. exact (@lem7117126 term24). Qed.
Lemma lem7117128 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7117129 : term119 = term108.
Proof. exact (MK_COMB (@lem7117128) (@lem7117127)). Qed.
Lemma lem7117130 : term163 = term159.
Proof. exact (MK_COMB (@lem7117129) (@lem7117124)). Qed.
Lemma lem7117132 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117133 : term159 = term164.
Proof. exact (@lem7117132 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7117134 : term164 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7117135 : term159 = False.
Proof. exact (TRANS (@lem7117133) (@lem7117134)). Qed.
Lemma lem7117136 : term163 = False.
Proof. exact (TRANS (@lem7117130) (@lem7117135)). Qed.
Lemma lem7117137 : term160 = False.
Proof. exact (TRANS (@lem7117121) (@lem7117136)). Qed.
Lemma lem7117138 : term159 = False.
Proof. exact (TRANS (@lem7117098) (@lem7117137)). Qed.
Lemma lem7117139 : term158 = False.
Proof. exact (TRANS (@lem7117089) (@lem7117138)). Qed.
Lemma lem7117140 (u : real) (h1 : term246 u) : False.
Proof. exact (EQ_MP (@lem7117139) (@lem7117086 u h1)). Qed.
Lemma lem7117141 (u : real) (h1 : term250 u) : term250 u.
Proof. exact (h1). Qed.
Lemma lem7117142 (u : real) (h1 : term250 u) : term242 u.
Proof. exact (proj2 (@lem7117141 u h1)). Qed.
Lemma lem7117143 (u : real) (h1 : term250 u) : term74 u.
Proof. exact (proj1 (@lem7117141 u h1)). Qed.
Lemma lem7117145 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7117146 : term106 = term107.
Proof. exact (@lem7117145 term15 term30). Qed.
Lemma lem7117148 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7117149 : term30 = term63.
Proof. exact (@lem7117148 term24). Qed.
Lemma lem7117151 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7117152 : term15 = term19.
Proof. exact (@lem7117151 (NUMERAL 0)). Qed.
Lemma lem7117153 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7117154 : term108 = term109.
Proof. exact (MK_COMB (@lem7117153) (@lem7117152)). Qed.
Lemma lem7117155 : term107 = term110.
Proof. exact (MK_COMB (@lem7117154) (@lem7117149)). Qed.
Lemma lem7117156 : term111.
Proof. exact (@lem1980255 term15 term30 term30 term30). Qed.
Lemma lem7117158 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117159 : term107 = term113.
Proof. exact (@lem7117158 (NUMERAL 0) term24). Qed.
Lemma lem7117160 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117161 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117162 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117161 h1) (fun h1 : term113 = True => @lem7117160)). Qed.
Lemma lem7117163 : term113 = True.
Proof. exact (EQ_MP (@lem7117162) (@lem7117160)). Qed.
Lemma lem7117164 : term107 = True.
Proof. exact (TRANS (@lem7117159) (@lem7117163)). Qed.
Lemma lem7117165 : True = term107.
Proof. exact (SYM (@lem7117164)). Qed.
Lemma lem7117166 : term107.
Proof. exact (EQ_MP (@lem7117165) (@lem0)). Qed.
Lemma lem7117167 : term115.
Proof. exact (@lem7117156 (@lem7117166)). Qed.
Lemma lem7117169 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117170 : term107 = term113.
Proof. exact (@lem7117169 (NUMERAL 0) term24). Qed.
Lemma lem7117171 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117172 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117173 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117172 h1) (fun h1 : term113 = True => @lem7117171)). Qed.
Lemma lem7117174 : term113 = True.
Proof. exact (EQ_MP (@lem7117173) (@lem7117171)). Qed.
Lemma lem7117175 : term107 = True.
Proof. exact (TRANS (@lem7117170) (@lem7117174)). Qed.
Lemma lem7117176 : True = term107.
Proof. exact (SYM (@lem7117175)). Qed.
Lemma lem7117177 : term107.
Proof. exact (EQ_MP (@lem7117176) (@lem0)). Qed.
Lemma lem7117178 : term110 = term116.
Proof. exact (@lem7117167 (@lem7117177)). Qed.
Lemma lem7117180 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7117181 : term33 = term34.
Proof. exact (@lem7117180 term24 term24). Qed.
Lemma lem7117182 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7117183 : term36 = term24.
Proof. exact (EQ_MP (@lem7117182) (@lem940073)). Qed.
Lemma lem7117184 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7117185 : term34 = term30.
Proof. exact (MK_COMB (@lem7117184) (@lem7117183)). Qed.
Lemma lem7117186 : term33 = term30.
Proof. exact (TRANS (@lem7117181) (@lem7117185)). Qed.
Lemma lem7117188 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7117189 : term118 = term15.
Proof. exact (@lem7117188 term24). Qed.
Lemma lem7117190 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7117191 : term119 = term108.
Proof. exact (MK_COMB (@lem7117190) (@lem7117189)). Qed.
Lemma lem7117192 : term116 = term107.
Proof. exact (MK_COMB (@lem7117191) (@lem7117186)). Qed.
Lemma lem7117194 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117195 : term107 = term113.
Proof. exact (@lem7117194 (NUMERAL 0) term24). Qed.
Lemma lem7117196 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117197 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117198 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117197 h1) (fun h1 : term113 = True => @lem7117196)). Qed.
Lemma lem7117199 : term113 = True.
Proof. exact (EQ_MP (@lem7117198) (@lem7117196)). Qed.
Lemma lem7117200 : term107 = True.
Proof. exact (TRANS (@lem7117195) (@lem7117199)). Qed.
Lemma lem7117201 : term116 = True.
Proof. exact (TRANS (@lem7117192) (@lem7117200)). Qed.
Lemma lem7117202 : term110 = True.
Proof. exact (TRANS (@lem7117178) (@lem7117201)). Qed.
Lemma lem7117203 : term107 = True.
Proof. exact (TRANS (@lem7117155) (@lem7117202)). Qed.
Lemma lem7117204 : term106 = True.
Proof. exact (TRANS (@lem7117146) (@lem7117203)). Qed.
Lemma lem7117205 : True = term106.
Proof. exact (SYM (@lem7117204)). Qed.
Lemma lem7117206 : term106.
Proof. exact (EQ_MP (@lem7117205) (@lem0)). Qed.
Lemma lem7117207 (u : real) (h1 : term250 u) : term262 u.
Proof. exact (conj (@lem7117206) (@lem7117142 u h1)). Qed.
Lemma lem7117209 (x : real) (y : real) : term256 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7117210 (u : real) : term263 u.
Proof. exact (@lem7117209 term30 u). Qed.
Lemma lem7117211 (u : real) (h1 : term250 u) : term264 u.
Proof. exact (@lem7117210 u (@lem7117207 u h1)). Qed.
Lemma lem7117212 (u : real) : (term66 u) = u.
Proof. exact (@lem1982733 u). Qed.
Lemma lem7117213 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7117214 (u : real) : (term265 u) = (real_ge u).
Proof. exact (MK_COMB (@lem7117213) (@lem7117212 u)). Qed.
Lemma lem7117215 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7117216 (u : real) : (term264 u) = (term242 u).
Proof. exact (MK_COMB (@lem7117214 u) (@lem7117215)). Qed.
Lemma lem7117217 (u : real) (h1 : term250 u) : term242 u.
Proof. exact (EQ_MP (@lem7117216 u) (@lem7117211 u h1)). Qed.
Lemma lem7117219 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7117220 : term106 = term107.
Proof. exact (@lem7117219 term15 term30). Qed.
Lemma lem7117222 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7117223 : term30 = term63.
Proof. exact (@lem7117222 term24). Qed.
Lemma lem7117225 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7117226 : term15 = term19.
Proof. exact (@lem7117225 (NUMERAL 0)). Qed.
Lemma lem7117227 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7117228 : term108 = term109.
Proof. exact (MK_COMB (@lem7117227) (@lem7117226)). Qed.
Lemma lem7117229 : term107 = term110.
Proof. exact (MK_COMB (@lem7117228) (@lem7117223)). Qed.
Lemma lem7117230 : term111.
Proof. exact (@lem1980255 term15 term30 term30 term30). Qed.
Lemma lem7117232 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117233 : term107 = term113.
Proof. exact (@lem7117232 (NUMERAL 0) term24). Qed.
Lemma lem7117234 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117235 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117236 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117235 h1) (fun h1 : term113 = True => @lem7117234)). Qed.
Lemma lem7117237 : term113 = True.
Proof. exact (EQ_MP (@lem7117236) (@lem7117234)). Qed.
Lemma lem7117238 : term107 = True.
Proof. exact (TRANS (@lem7117233) (@lem7117237)). Qed.
Lemma lem7117239 : True = term107.
Proof. exact (SYM (@lem7117238)). Qed.
Lemma lem7117240 : term107.
Proof. exact (EQ_MP (@lem7117239) (@lem0)). Qed.
Lemma lem7117241 : term115.
Proof. exact (@lem7117230 (@lem7117240)). Qed.
Lemma lem7117243 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117244 : term107 = term113.
Proof. exact (@lem7117243 (NUMERAL 0) term24). Qed.
Lemma lem7117245 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117246 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117247 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117246 h1) (fun h1 : term113 = True => @lem7117245)). Qed.
Lemma lem7117248 : term113 = True.
Proof. exact (EQ_MP (@lem7117247) (@lem7117245)). Qed.
Lemma lem7117249 : term107 = True.
Proof. exact (TRANS (@lem7117244) (@lem7117248)). Qed.
Lemma lem7117250 : True = term107.
Proof. exact (SYM (@lem7117249)). Qed.
Lemma lem7117251 : term107.
Proof. exact (EQ_MP (@lem7117250) (@lem0)). Qed.
Lemma lem7117252 : term110 = term116.
Proof. exact (@lem7117241 (@lem7117251)). Qed.
Lemma lem7117254 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7117255 : term33 = term34.
Proof. exact (@lem7117254 term24 term24). Qed.
Lemma lem7117256 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7117257 : term36 = term24.
Proof. exact (EQ_MP (@lem7117256) (@lem940073)). Qed.
Lemma lem7117258 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7117259 : term34 = term30.
Proof. exact (MK_COMB (@lem7117258) (@lem7117257)). Qed.
Lemma lem7117260 : term33 = term30.
Proof. exact (TRANS (@lem7117255) (@lem7117259)). Qed.
Lemma lem7117262 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7117263 : term118 = term15.
Proof. exact (@lem7117262 term24). Qed.
Lemma lem7117264 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7117265 : term119 = term108.
Proof. exact (MK_COMB (@lem7117264) (@lem7117263)). Qed.
Lemma lem7117266 : term116 = term107.
Proof. exact (MK_COMB (@lem7117265) (@lem7117260)). Qed.
Lemma lem7117268 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117269 : term107 = term113.
Proof. exact (@lem7117268 (NUMERAL 0) term24). Qed.
Lemma lem7117270 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117271 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117272 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117271 h1) (fun h1 : term113 = True => @lem7117270)). Qed.
Lemma lem7117273 : term113 = True.
Proof. exact (EQ_MP (@lem7117272) (@lem7117270)). Qed.
Lemma lem7117274 : term107 = True.
Proof. exact (TRANS (@lem7117269) (@lem7117273)). Qed.
Lemma lem7117275 : term116 = True.
Proof. exact (TRANS (@lem7117266) (@lem7117274)). Qed.
Lemma lem7117276 : term110 = True.
Proof. exact (TRANS (@lem7117252) (@lem7117275)). Qed.
Lemma lem7117277 : term107 = True.
Proof. exact (TRANS (@lem7117229) (@lem7117276)). Qed.
Lemma lem7117278 : term106 = True.
Proof. exact (TRANS (@lem7117220) (@lem7117277)). Qed.
Lemma lem7117279 : True = term106.
Proof. exact (SYM (@lem7117278)). Qed.
Lemma lem7117280 : term106.
Proof. exact (EQ_MP (@lem7117279) (@lem0)). Qed.
Lemma lem7117281 (u : real) (h1 : term250 u) : term120 u.
Proof. exact (conj (@lem7117280) (@lem7117143 u h1)). Qed.
Lemma lem7117283 (x : real) (y : real) : term121 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem7117284 (u : real) : term122 u.
Proof. exact (@lem7117283 term30 (term45 u)). Qed.
Lemma lem7117285 (u : real) (h1 : term250 u) : term123 u.
Proof. exact (@lem7117284 u (@lem7117281 u h1)). Qed.
Lemma lem7117286 (u : real) : (term124 u) = (term45 u).
Proof. exact (@lem1982733 (term45 u)). Qed.
Lemma lem7117287 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7117288 (u : real) : (term125 u) = (term72 u).
Proof. exact (MK_COMB (@lem7117287) (@lem7117286 u)). Qed.
Lemma lem7117289 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7117290 (u : real) : (term123 u) = (term74 u).
Proof. exact (MK_COMB (@lem7117288 u) (@lem7117289)). Qed.
Lemma lem7117291 (u : real) (h1 : term250 u) : term74 u.
Proof. exact (EQ_MP (@lem7117290 u) (@lem7117285 u h1)). Qed.
Lemma lem7117292 (u : real) (h1 : term250 u) : term250 u.
Proof. exact (conj (@lem7117291 u h1) (@lem7117217 u h1)). Qed.
Lemma lem7117294 (x : real) (y : real) : term260 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem7117295 (u : real) : term266 u.
Proof. exact (@lem7117294 (term45 u) u). Qed.
Lemma lem7117296 (u : real) (h1 : term250 u) : term173 u.
Proof. exact (@lem7117295 u (@lem7117292 u h1)). Qed.
Lemma lem7117297 (u : real) : (term174 u) = (term134 u).
Proof. exact (@lem1982713 term22 u). Qed.
Lemma lem7117299 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7117300 : term30 = term63.
Proof. exact (@lem7117299 term24). Qed.
Lemma lem7117302 (x : nat) : (term20 x) = (term21 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7117303 : term22 = term23.
Proof. exact (@lem7117302 term24). Qed.
Lemma lem7117304 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7117305 : term135 = term136.
Proof. exact (MK_COMB (@lem7117304) (@lem7117303)). Qed.
Lemma lem7117306 : term137 = term138.
Proof. exact (MK_COMB (@lem7117305) (@lem7117300)). Qed.
Lemma lem7117307 : term139.
Proof. exact (@lem1981473 term22 term30 term30 term30 term15 term30). Qed.
Lemma lem7117309 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117310 : term107 = term113.
Proof. exact (@lem7117309 (NUMERAL 0) term24). Qed.
Lemma lem7117311 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117312 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117313 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117312 h1) (fun h1 : term113 = True => @lem7117311)). Qed.
Lemma lem7117314 : term113 = True.
Proof. exact (EQ_MP (@lem7117313) (@lem7117311)). Qed.
Lemma lem7117315 : term107 = True.
Proof. exact (TRANS (@lem7117310) (@lem7117314)). Qed.
Lemma lem7117316 : True = term107.
Proof. exact (SYM (@lem7117315)). Qed.
Lemma lem7117317 : term107.
Proof. exact (EQ_MP (@lem7117316) (@lem0)). Qed.
Lemma lem7117318 : term140.
Proof. exact (@lem7117307 (@lem7117317)). Qed.
Lemma lem7117320 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117321 : term107 = term113.
Proof. exact (@lem7117320 (NUMERAL 0) term24). Qed.
Lemma lem7117322 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117323 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117324 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117323 h1) (fun h1 : term113 = True => @lem7117322)). Qed.
Lemma lem7117325 : term113 = True.
Proof. exact (EQ_MP (@lem7117324) (@lem7117322)). Qed.
Lemma lem7117326 : term107 = True.
Proof. exact (TRANS (@lem7117321) (@lem7117325)). Qed.
Lemma lem7117327 : True = term107.
Proof. exact (SYM (@lem7117326)). Qed.
Lemma lem7117328 : term107.
Proof. exact (EQ_MP (@lem7117327) (@lem0)). Qed.
Lemma lem7117329 : term141.
Proof. exact (@lem7117318 (@lem7117328)). Qed.
Lemma lem7117331 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117332 : term107 = term113.
Proof. exact (@lem7117331 (NUMERAL 0) term24). Qed.
Lemma lem7117333 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117334 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117335 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117334 h1) (fun h1 : term113 = True => @lem7117333)). Qed.
Lemma lem7117336 : term113 = True.
Proof. exact (EQ_MP (@lem7117335) (@lem7117333)). Qed.
Lemma lem7117337 : term107 = True.
Proof. exact (TRANS (@lem7117332) (@lem7117336)). Qed.
Lemma lem7117338 : True = term107.
Proof. exact (SYM (@lem7117337)). Qed.
Lemma lem7117339 : term107.
Proof. exact (EQ_MP (@lem7117338) (@lem0)). Qed.
Lemma lem7117340 : term142.
Proof. exact (@lem7117329 (@lem7117339)). Qed.
Lemma lem7117342 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7117343 : term33 = term34.
Proof. exact (@lem7117342 term24 term24). Qed.
Lemma lem7117344 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7117345 : term36 = term24.
Proof. exact (EQ_MP (@lem7117344) (@lem940073)). Qed.
Lemma lem7117346 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7117347 : term34 = term30.
Proof. exact (MK_COMB (@lem7117346) (@lem7117345)). Qed.
Lemma lem7117348 : term33 = term30.
Proof. exact (TRANS (@lem7117343) (@lem7117347)). Qed.
Lemma lem7117350 (m : nat) (n : nat) : (term143 m n) = (term144 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7117351 : term145 = term146.
Proof. exact (@lem7117350 term24 term24). Qed.
Lemma lem7117352 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7117353 : term36 = term24.
Proof. exact (EQ_MP (@lem7117352) (@lem940073)). Qed.
Lemma lem7117354 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7117355 : term34 = term30.
Proof. exact (MK_COMB (@lem7117354) (@lem7117353)). Qed.
Lemma lem7117356 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7117357 : term146 = term22.
Proof. exact (MK_COMB (@lem7117356) (@lem7117355)). Qed.
Lemma lem7117358 : term145 = term22.
Proof. exact (TRANS (@lem7117351) (@lem7117357)). Qed.
Lemma lem7117359 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7117360 : term147 = term135.
Proof. exact (MK_COMB (@lem7117359) (@lem7117358)). Qed.
Lemma lem7117361 : term148 = term137.
Proof. exact (MK_COMB (@lem7117360) (@lem7117348)). Qed.
Lemma lem7117363 (m : nat) : (term149 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7117364 : term137 = term15.
Proof. exact (@lem7117363 term24). Qed.
Lemma lem7117365 : term148 = term15.
Proof. exact (TRANS (@lem7117361) (@lem7117364)). Qed.
Lemma lem7117366 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7117367 : term150 = term151.
Proof. exact (MK_COMB (@lem7117366) (@lem7117365)). Qed.
Lemma lem7117368 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem7117369 : term152 = term118.
Proof. exact (MK_COMB (@lem7117367) (@lem7117368)). Qed.
Lemma lem7117371 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7117372 : term118 = term15.
Proof. exact (@lem7117371 term24). Qed.
Lemma lem7117373 : term152 = term15.
Proof. exact (TRANS (@lem7117369) (@lem7117372)). Qed.
Lemma lem7117375 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7117376 : term33 = term34.
Proof. exact (@lem7117375 term24 term24). Qed.
Lemma lem7117377 : (term35 = (BIT1 0)) = (term36 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7117378 : term36 = term24.
Proof. exact (EQ_MP (@lem7117377) (@lem940073)). Qed.
Lemma lem7117379 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7117380 : term34 = term30.
Proof. exact (MK_COMB (@lem7117379) (@lem7117378)). Qed.
Lemma lem7117381 : term33 = term30.
Proof. exact (TRANS (@lem7117376) (@lem7117380)). Qed.
Lemma lem7117382 : term151 = term151.
Proof. exact (eq_refl term151). Qed.
Lemma lem7117383 : term153 = term118.
Proof. exact (MK_COMB (@lem7117382) (@lem7117381)). Qed.
Lemma lem7117385 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7117386 : term118 = term15.
Proof. exact (@lem7117385 term24). Qed.
Lemma lem7117387 : term153 = term15.
Proof. exact (TRANS (@lem7117383) (@lem7117386)). Qed.
Lemma lem7117388 : term15 = term153.
Proof. exact (SYM (@lem7117387)). Qed.
Lemma lem7117389 : term152 = term153.
Proof. exact (TRANS (@lem7117373) (@lem7117388)). Qed.
Lemma lem7117390 : term138 = term19.
Proof. exact (@lem7117340 (@lem7117389)). Qed.
Lemma lem7117391 : term137 = term19.
Proof. exact (TRANS (@lem7117306) (@lem7117390)). Qed.
Lemma lem7117393 (x : real) : (term40 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7117394 : term19 = term15.
Proof. exact (@lem7117393 term15). Qed.
Lemma lem7117395 : term137 = term15.
Proof. exact (TRANS (@lem7117391) (@lem7117394)). Qed.
Lemma lem7117396 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7117397 : term154 = term151.
Proof. exact (MK_COMB (@lem7117396) (@lem7117395)). Qed.
Lemma lem7117398 (u : real) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7117399 (u : real) : (term134 u) = (term155 u).
Proof. exact (MK_COMB (@lem7117397) (@lem7117398 u)). Qed.
Lemma lem7117400 (u : real) : (term174 u) = (term155 u).
Proof. exact (TRANS (@lem7117297 u) (@lem7117399 u)). Qed.
Lemma lem7117401 (u : real) : (term155 u) = term15.
Proof. exact (@lem1982719 u). Qed.
Lemma lem7117402 (u : real) : (term174 u) = term15.
Proof. exact (TRANS (@lem7117400 u) (@lem7117401 u)). Qed.
Lemma lem7117403 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7117404 (u : real) : (term175 u) = term157.
Proof. exact (MK_COMB (@lem7117403) (@lem7117402 u)). Qed.
Lemma lem7117405 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7117406 (u : real) : (term173 u) = term158.
Proof. exact (MK_COMB (@lem7117404 u) (@lem7117405)). Qed.
Lemma lem7117407 (u : real) (h1 : term250 u) : term158.
Proof. exact (EQ_MP (@lem7117406 u) (@lem7117296 u h1)). Qed.
Lemma lem7117409 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7117410 : term158 = term159.
Proof. exact (@lem7117409 term15 term15). Qed.
Lemma lem7117412 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7117413 : term15 = term19.
Proof. exact (@lem7117412 (NUMERAL 0)). Qed.
Lemma lem7117415 (x : nat) : (real_of_num x) = (term18 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7117416 : term15 = term19.
Proof. exact (@lem7117415 (NUMERAL 0)). Qed.
Lemma lem7117417 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7117418 : term108 = term109.
Proof. exact (MK_COMB (@lem7117417) (@lem7117416)). Qed.
Lemma lem7117419 : term159 = term160.
Proof. exact (MK_COMB (@lem7117418) (@lem7117413)). Qed.
Lemma lem7117420 : term161.
Proof. exact (@lem1980255 term15 term30 term15 term30). Qed.
Lemma lem7117422 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117423 : term107 = term113.
Proof. exact (@lem7117422 (NUMERAL 0) term24). Qed.
Lemma lem7117424 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117425 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117426 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117425 h1) (fun h1 : term113 = True => @lem7117424)). Qed.
Lemma lem7117427 : term113 = True.
Proof. exact (EQ_MP (@lem7117426) (@lem7117424)). Qed.
Lemma lem7117428 : term107 = True.
Proof. exact (TRANS (@lem7117423) (@lem7117427)). Qed.
Lemma lem7117429 : True = term107.
Proof. exact (SYM (@lem7117428)). Qed.
Lemma lem7117430 : term107.
Proof. exact (EQ_MP (@lem7117429) (@lem0)). Qed.
Lemma lem7117431 : term162.
Proof. exact (@lem7117420 (@lem7117430)). Qed.
Lemma lem7117433 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117434 : term107 = term113.
Proof. exact (@lem7117433 (NUMERAL 0) term24). Qed.
Lemma lem7117435 : term114 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7117436 (h1 : term114 = (BIT1 0)) : term113 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7117437 : (term114 = (BIT1 0)) = (term113 = True).
Proof. exact (prop_ext (fun h1 : term114 = (BIT1 0) => @lem7117436 h1) (fun h1 : term113 = True => @lem7117435)). Qed.
Lemma lem7117438 : term113 = True.
Proof. exact (EQ_MP (@lem7117437) (@lem7117435)). Qed.
Lemma lem7117439 : term107 = True.
Proof. exact (TRANS (@lem7117434) (@lem7117438)). Qed.
Lemma lem7117440 : True = term107.
Proof. exact (SYM (@lem7117439)). Qed.
Lemma lem7117441 : term107.
Proof. exact (EQ_MP (@lem7117440) (@lem0)). Qed.
Lemma lem7117442 : term160 = term163.
Proof. exact (@lem7117431 (@lem7117441)). Qed.
Lemma lem7117444 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7117445 : term118 = term15.
Proof. exact (@lem7117444 term24). Qed.
Lemma lem7117447 (x : nat) : (term117 x) = term15.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7117448 : term118 = term15.
Proof. exact (@lem7117447 term24). Qed.
Lemma lem7117449 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7117450 : term119 = term108.
Proof. exact (MK_COMB (@lem7117449) (@lem7117448)). Qed.
Lemma lem7117451 : term163 = term159.
Proof. exact (MK_COMB (@lem7117450) (@lem7117445)). Qed.
Lemma lem7117453 (m : nat) (n : nat) : (term112 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7117454 : term159 = term164.
Proof. exact (@lem7117453 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7117455 : term164 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7117456 : term159 = False.
Proof. exact (TRANS (@lem7117454) (@lem7117455)). Qed.
Lemma lem7117457 : term163 = False.
Proof. exact (TRANS (@lem7117451) (@lem7117456)). Qed.
Lemma lem7117458 : term160 = False.
Proof. exact (TRANS (@lem7117442) (@lem7117457)). Qed.
Lemma lem7117459 : term159 = False.
Proof. exact (TRANS (@lem7117419) (@lem7117458)). Qed.
Lemma lem7117460 : term158 = False.
Proof. exact (TRANS (@lem7117410) (@lem7117459)). Qed.
Lemma lem7117461 (u : real) (h1 : term250 u) : False.
Proof. exact (EQ_MP (@lem7117460) (@lem7117407 u h1)). Qed.
Lemma lem7117462 (u : real) (h1 : term252 u) : False.
Proof. exact (or_elim (@lem7116819 u h1) (fun h0 : term246 u => @lem7117140 u h0) (fun h0 : term250 u => @lem7117461 u h0)). Qed.
Lemma lem7117463 (u : real) (h1 : term254 u) : False.
Proof. exact (or_elim (@lem7116174 u h1) (fun h0 : term239 u => @lem7116818 u h0) (fun h0 : term252 u => @lem7117462 u h0)). Qed.
Lemma lem7117465 (u : real) (h1 : term254 u) : term254 u.
Proof. exact (h1). Qed.
Lemma lem7117466 (u : real) (h1 : term254 u) : (term254 u) = False.
Proof. exact (prop_ext (fun h2 : term254 u => @lem7117463 u h1) (fun h2 : False => @lem7117465 u h1)). Qed.
Lemma lem7117467 (u : real) (h1 : term254 u) : False.
Proof. exact (EQ_MP (@lem7117466 u h1) (@lem7117465 u h1)). Qed.
Lemma lem7117468 (u : real) (h1 : term215 u) : term215 u.
Proof. exact (h1). Qed.
Lemma lem7117469 (u : real) (h1 : term215 u) : term254 u.
Proof. exact (EQ_MP (@lem7116152 u) (@lem7117468 u h1)). Qed.
Lemma lem7117470 (u : real) (h1 : term215 u) : (term254 u) = False.
Proof. exact (prop_ext (fun h2 : term254 u => @lem7117467 u h2) (fun h2 : False => @lem7117469 u h1)). Qed.
Lemma lem7117471 (u : real) (h1 : term215 u) : False.
Proof. exact (EQ_MP (@lem7117470 u h1) (@lem7117469 u h1)). Qed.
Lemma lem7117472 (u : real) : term267 u.
Proof. exact (fun h0 : term215 u => @lem7117471 u h0). Qed.
Lemma lem7117473 (u : real) : term268 u.
Proof. exact (@lem1386578 (term269 u)). Qed.
Lemma lem7117476 (u : real) : term269 u.
Proof. exact (@lem7117473 u (@lem7117472 u)). Qed.
Lemma lem7117487 : term270.
Proof. exact (fun u : real => @lem7117476 u). Qed.
Lemma lem7117489 (p : Prop) : p = (term271 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7117490 {A : Type'} (s : A -> Prop) (u : A -> real) : (term272 A s u) = (term273 A s u).
Proof. exact (@lem7117489 (term272 A s u)). Qed.
Lemma lem7117491 {A : Type'} (s : A -> Prop) (u : A -> real) : (term273 A s u) = (term272 A s u).
Proof. exact (SYM (@lem7117490 A s u)). Qed.
Lemma lem7117492 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term274 A s u) : term274 A s u.
Proof. exact (h1). Qed.
Lemma lem7117495 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term275 A s u) : term275 A s u.
Proof. exact (h1). Qed.
Lemma lem7117496 {A : Type'} (s : A -> Prop) (u : A -> real) : term276 A s u.
Proof. exact (fun h0 : term275 A s u => @lem7117495 A s u h0). Qed.
Lemma lem7117497 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term276 A s u) : term276 A s u.
Proof. exact (h1). Qed.
Lemma lem7117498 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term275 A s u) : term275 A s u.
Proof. exact (h1). Qed.
Lemma lem7117499 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term275 A s u) (h2 : term276 A s u) : term275 A s u.
Proof. exact (@lem7117497 A s u h2 (@lem7117498 A s u h1)). Qed.
Lemma lem7117500 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term275 A s u) : term277 A s u.
Proof. exact (fun h0 : term276 A s u => @lem7117499 A s u h1 h0). Qed.
Lemma lem7117501 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term276 A s u) : term276 A s u.
Proof. exact (h1). Qed.
Lemma lem7117502 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term275 A s u) (h2 : term276 A s u) : term275 A s u.
Proof. exact (@lem7117500 A s u h1 (@lem7117501 A s u h2)). Qed.
Lemma lem7117503 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term276 A s u) : term276 A s u.
Proof. exact (fun h0 : term275 A s u => @lem7117502 A s u h0 h1). Qed.
Lemma lem7117504 {A : Type'} (s : A -> Prop) (u : A -> real) : term278 A s u.
Proof. exact (fun h0 : term276 A s u => @lem7117503 A s u h0). Qed.
Lemma lem7117507 {A : Type'} (s : A -> Prop) (u : A -> real) : term276 A s u.
Proof. exact (@lem7117504 A s u (@lem7117496 A s u)). Qed.
Lemma lem7117508 {A : Type'} (s : A -> Prop) (u : A -> real) : term276 A s u.
Proof. exact (@lem7117507 A s u). Qed.
Lemma lem7117526 {A : Type'} (P : Prop) (Q : A -> Prop) : (term279 A P Q) = (term280 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem7117527 {A : Type'} (P : Prop) (Q : A -> Prop) : (term279 A P Q) = (term280 A P Q).
Proof. exact (@lem7117526 A P Q). Qed.
Lemma lem7117528 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term281 A j s u) = (term282 A j s u).
Proof. exact (@lem7117527 A (@IN A j s) (term283 A j s u)). Qed.
Lemma lem7117529 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) (k : A) : (term284 A j s u k) = (term285 A j s u k).
Proof. exact (eq_refl (term284 A j s u k)). Qed.
Lemma lem7117530 {A : Type'} (j : A) (s : A -> Prop) : (term286 A j s) = (term286 A j s).
Proof. exact (eq_refl (term286 A j s)). Qed.
Lemma lem7117531 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) (k : A) : (term287 A j s u k) = (term288 A j s u k).
Proof. exact (MK_COMB (@lem7117530 A j s) (@lem7117529 A j s u k)). Qed.
Lemma lem7117532 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term289 A j s u) = (term290 A j s u).
Proof. exact (fun_ext (fun k : A => @lem7117531 A j s u k)). Qed.
Lemma lem7117533 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7117534 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term281 A j s u) = (term291 A j s u).
Proof. exact (MK_COMB (@lem7117533 A) (@lem7117532 A j s u)). Qed.
Lemma lem7117535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7117536 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term292 A j s u) = (term293 A j s u).
Proof. exact (MK_COMB (@lem7117535) (@lem7117534 A j s u)). Qed.
Lemma lem7117537 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) (k : A) : (term284 A j s u k) = (term285 A j s u k).
Proof. exact (eq_refl (term284 A j s u k)). Qed.
Lemma lem7117538 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term294 A j s u) = (term283 A j s u).
Proof. exact (fun_ext (fun k : A => @lem7117537 A j s u k)). Qed.
Lemma lem7117539 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7117540 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term295 A j s u) = (term296 A j s u).
Proof. exact (MK_COMB (@lem7117539 A) (@lem7117538 A j s u)). Qed.
Lemma lem7117541 {A : Type'} (j : A) (s : A -> Prop) : (term286 A j s) = (term286 A j s).
Proof. exact (eq_refl (term286 A j s)). Qed.
Lemma lem7117542 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term282 A j s u) = (term297 A j s u).
Proof. exact (MK_COMB (@lem7117541 A j s) (@lem7117540 A j s u)). Qed.
Lemma lem7117543 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : ((term281 A j s u) = (term282 A j s u)) = ((term291 A j s u) = (term297 A j s u)).
Proof. exact (MK_COMB (@lem7117536 A j s u) (@lem7117542 A j s u)). Qed.
Lemma lem7117544 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term291 A j s u) = (term297 A j s u).
Proof. exact (EQ_MP (@lem7117543 A j s u) (@lem7117528 A j s u)). Qed.
Lemma lem7117548 {A : Type'} (P : Prop) (Q : A -> Prop) : (term279 A P Q) = (term280 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem7117549 {A : Type'} (P : Prop) (Q : A -> Prop) : (term279 A P Q) = (term280 A P Q).
Proof. exact (@lem7117548 A P Q). Qed.
Lemma lem7117550 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term298 A j s u) = (term299 A j s u).
Proof. exact (@lem7117549 A (term300 A u j) (term301 A s u)). Qed.
Lemma lem7117551 {A : Type'} (s : A -> Prop) (u : A -> real) (k : A) : (term302 A s u k) = (term303 A s u k).
Proof. exact (eq_refl (term302 A s u k)). Qed.
Lemma lem7117552 {A : Type'} (u : A -> real) (j : A) : (term304 A u j) = (term304 A u j).
Proof. exact (eq_refl (term304 A u j)). Qed.
Lemma lem7117553 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) (k : A) : (term305 A j s u k) = (term285 A j s u k).
Proof. exact (MK_COMB (@lem7117552 A u j) (@lem7117551 A s u k)). Qed.
Lemma lem7117554 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term306 A j s u) = (term283 A j s u).
Proof. exact (fun_ext (fun k : A => @lem7117553 A j s u k)). Qed.
Lemma lem7117555 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7117556 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term298 A j s u) = (term296 A j s u).
Proof. exact (MK_COMB (@lem7117555 A) (@lem7117554 A j s u)). Qed.
Lemma lem7117557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7117558 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term307 A j s u) = (term308 A j s u).
Proof. exact (MK_COMB (@lem7117557) (@lem7117556 A j s u)). Qed.
Lemma lem7117559 {A : Type'} (s : A -> Prop) (u : A -> real) (k : A) : (term302 A s u k) = (term303 A s u k).
Proof. exact (eq_refl (term302 A s u k)). Qed.
Lemma lem7117560 {A : Type'} (s : A -> Prop) (u : A -> real) : (term309 A s u) = (term301 A s u).
Proof. exact (fun_ext (fun k : A => @lem7117559 A s u k)). Qed.
Lemma lem7117561 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7117562 {A : Type'} (s : A -> Prop) (u : A -> real) : (term310 A s u) = (term311 A s u).
Proof. exact (MK_COMB (@lem7117561 A) (@lem7117560 A s u)). Qed.
Lemma lem7117563 {A : Type'} (u : A -> real) (j : A) : (term304 A u j) = (term304 A u j).
Proof. exact (eq_refl (term304 A u j)). Qed.
Lemma lem7117564 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term299 A j s u) = (term312 A j s u).
Proof. exact (MK_COMB (@lem7117563 A u j) (@lem7117562 A s u)). Qed.
Lemma lem7117565 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : ((term298 A j s u) = (term299 A j s u)) = ((term296 A j s u) = (term312 A j s u)).
Proof. exact (MK_COMB (@lem7117558 A j s u) (@lem7117564 A j s u)). Qed.
Lemma lem7117566 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term296 A j s u) = (term312 A j s u).
Proof. exact (EQ_MP (@lem7117565 A j s u) (@lem7117550 A j s u)). Qed.
Lemma lem7117619 {A : Type'} (j : A) (s : A -> Prop) : (term286 A j s) = (term286 A j s).
Proof. exact (eq_refl (term286 A j s)). Qed.
Lemma lem7117620 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term297 A j s u) = (term313 A j s u).
Proof. exact (MK_COMB (@lem7117619 A j s) (@lem7117566 A j s u)). Qed.
Lemma lem7117623 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term291 A j s u) = (term313 A j s u).
Proof. exact (TRANS (@lem7117544 A j s u) (@lem7117620 A j s u)). Qed.
Lemma lem7117624 {A : Type'} (s : A -> Prop) (u : A -> real) : (term314 A s u) = (term315 A s u).
Proof. exact (fun_ext (fun j : A => @lem7117623 A j s u)). Qed.
Lemma lem7117625 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7117626 {A : Type'} (s : A -> Prop) (u : A -> real) : (term316 A s u) = (term317 A s u).
Proof. exact (MK_COMB (@lem7117625 A) (@lem7117624 A s u)). Qed.
Lemma lem7117675 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7117676 {A : Type'} (s : A -> Prop) (u : A -> real) : (term318 A s u) = (term319 A s u).
Proof. exact (MK_COMB (@lem7117675) (@lem7117626 A s u)). Qed.
Lemma lem7117691 {A : Type'} (s : A -> Prop) (u : A -> real) : (term320 A s u) = (term320 A s u).
Proof. exact (eq_refl (term320 A s u)). Qed.
Lemma lem7117692 {A : Type'} (s : A -> Prop) (u : A -> real) : (term272 A s u) = (term321 A s u).
Proof. exact (MK_COMB (@lem7117676 A s u) (@lem7117691 A s u)). Qed.
Lemma lem7117695 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7117696 {A : Type'} (s : A -> Prop) (u : A -> real) : (term274 A s u) = (term322 A s u).
Proof. exact (MK_COMB (@lem7117695) (@lem7117692 A s u)). Qed.
Lemma lem7117697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7117698 {A : Type'} (s : A -> Prop) (u : A -> real) : (term323 A s u) = (term324 A s u).
Proof. exact (MK_COMB (@lem7117697) (@lem7117696 A s u)). Qed.
Lemma lem7117700 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7117701 : term325 = term326.
Proof. exact (@lem7117700 term270). Qed.
Lemma lem7117703 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term327 A P Q) = (term328 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem7117704 (P : real -> Prop) (Q : real -> Prop) : (term329 P Q) = (term330 P Q).
Proof. exact (@lem7117703 real P Q). Qed.
Lemma lem7117705 : term331 = term332.
Proof. exact (@lem7117704 term333 term334). Qed.
Lemma lem7117706 (u : real) : (term335 u) = ((term196 u) = (term197 u)).
Proof. exact (eq_refl (term335 u)). Qed.
Lemma lem7117707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7117708 (u : real) : (term336 u) = (term337 u).
Proof. exact (MK_COMB (@lem7117707) (@lem7117706 u)). Qed.
Lemma lem7117709 (u : real) : (term338 u) = ((term209 u) = (term210 u)).
Proof. exact (eq_refl (term338 u)). Qed.
Lemma lem7117710 (u : real) : (term339 u) = (term269 u).
Proof. exact (MK_COMB (@lem7117708 u) (@lem7117709 u)). Qed.
Lemma lem7117711 : term340 = term341.
Proof. exact (fun_ext (fun u : real => @lem7117710 u)). Qed.
Lemma lem7117712 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7117713 : term331 = term270.
Proof. exact (MK_COMB (@lem7117712) (@lem7117711)). Qed.
Lemma lem7117714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7117715 : term342 = term343.
Proof. exact (MK_COMB (@lem7117714) (@lem7117713)). Qed.
Lemma lem7117716 (u : real) : (term335 u) = ((term196 u) = (term197 u)).
Proof. exact (eq_refl (term335 u)). Qed.
Lemma lem7117717 : term344 = term333.
Proof. exact (fun_ext (fun u : real => @lem7117716 u)). Qed.
Lemma lem7117718 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7117719 : term345 = term346.
Proof. exact (MK_COMB (@lem7117718) (@lem7117717)). Qed.
Lemma lem7117720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7117721 : term347 = term348.
Proof. exact (MK_COMB (@lem7117720) (@lem7117719)). Qed.
Lemma lem7117722 (u : real) : (term338 u) = ((term209 u) = (term210 u)).
Proof. exact (eq_refl (term338 u)). Qed.
Lemma lem7117723 : term349 = term334.
Proof. exact (fun_ext (fun u : real => @lem7117722 u)). Qed.
Lemma lem7117724 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7117725 : term350 = term351.
Proof. exact (MK_COMB (@lem7117724) (@lem7117723)). Qed.
Lemma lem7117726 : term332 = term352.
Proof. exact (MK_COMB (@lem7117721) (@lem7117725)). Qed.
Lemma lem7117727 : (term331 = term332) = (term270 = term352).
Proof. exact (MK_COMB (@lem7117715) (@lem7117726)). Qed.
Lemma lem7117728 : term270 = term352.
Proof. exact (EQ_MP (@lem7117727) (@lem7117705)). Qed.
Lemma lem7117739 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7117740 : term326 = term353.
Proof. exact (MK_COMB (@lem7117739) (@lem7117728)). Qed.
Lemma lem7117741 : term325 = term353.
Proof. exact (TRANS (@lem7117701) (@lem7117740)). Qed.
Lemma lem7117742 {A : Type'} (s : A -> Prop) (u : A -> real) : (term275 A s u) = (term354 A s u).
Proof. exact (MK_COMB (@lem7117698 A s u) (@lem7117741)). Qed.
Lemma lem7117745 {A : Type'} (u : A -> real) : (term355 A u) = (term356 A u).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7117742 A s u)). Qed.
Lemma lem7117746 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7117747 {A : Type'} (u : A -> real) : (term357 A u) = (term358 A u).
Proof. exact (MK_COMB (@lem7117746 A) (@lem7117745 A u)). Qed.
Lemma lem7117752 {A : Type'} : (term359 A) = (term360 A).
Proof. exact (fun_ext (fun u : A -> real => @lem7117747 A u)). Qed.
Lemma lem7117753 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7117762 {A : Type'} : (term361 A) = (term362 A).
Proof. exact (MK_COMB (@lem7117753 A) (@lem7117752 A)). Qed.
Lemma lem7117769 (u : real) : ((term209 u) = (term210 u)) = ((term209 u) = (term210 u)).
Proof. exact (eq_refl ((term209 u) = (term210 u))). Qed.
Lemma lem7117770 : term334 = term334.
Proof. exact (fun_ext (fun u : real => @lem7117769 u)). Qed.
Lemma lem7117771 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7117772 : term351 = term351.
Proof. exact (MK_COMB (@lem7117771) (@lem7117770)). Qed.
Lemma lem7117779 (u : real) : ((term196 u) = (term197 u)) = ((term196 u) = (term197 u)).
Proof. exact (eq_refl ((term196 u) = (term197 u))). Qed.
Lemma lem7117780 : term333 = term333.
Proof. exact (fun_ext (fun u : real => @lem7117779 u)). Qed.
Lemma lem7117781 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7117782 : term346 = term346.
Proof. exact (MK_COMB (@lem7117781) (@lem7117780)). Qed.
Lemma lem7117783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7117784 : term348 = term348.
Proof. exact (MK_COMB (@lem7117783) (@lem7117782)). Qed.
Lemma lem7117785 : term352 = term352.
Proof. exact (MK_COMB (@lem7117784) (@lem7117772)). Qed.
Lemma lem7117786 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7117787 : term353 = term353.
Proof. exact (MK_COMB (@lem7117786) (@lem7117785)). Qed.
Lemma lem7117792 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term363 A s u i) = (term363 A s u i).
Proof. exact (eq_refl (term363 A s u i)). Qed.
Lemma lem7117793 {A : Type'} (s : A -> Prop) (u : A -> real) : (term364 A s u) = (term364 A s u).
Proof. exact (fun_ext (fun i : A => @lem7117792 A s u i)). Qed.
Lemma lem7117794 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7117795 {A : Type'} (s : A -> Prop) (u : A -> real) : (term365 A s u) = (term365 A s u).
Proof. exact (MK_COMB (@lem7117794 A) (@lem7117793 A s u)). Qed.
Lemma lem7117800 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term366 A s u i) = (term366 A s u i).
Proof. exact (eq_refl (term366 A s u i)). Qed.
Lemma lem7117801 {A : Type'} (s : A -> Prop) (u : A -> real) : (term367 A s u) = (term367 A s u).
Proof. exact (fun_ext (fun i : A => @lem7117800 A s u i)). Qed.
Lemma lem7117802 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7117803 {A : Type'} (s : A -> Prop) (u : A -> real) : (term368 A s u) = (term368 A s u).
Proof. exact (MK_COMB (@lem7117802 A) (@lem7117801 A s u)). Qed.
Lemma lem7117804 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7117805 {A : Type'} (s : A -> Prop) (u : A -> real) : (term369 A s u) = (term369 A s u).
Proof. exact (MK_COMB (@lem7117804) (@lem7117803 A s u)). Qed.
Lemma lem7117806 {A : Type'} (s : A -> Prop) (u : A -> real) : (term320 A s u) = (term320 A s u).
Proof. exact (MK_COMB (@lem7117805 A s u) (@lem7117795 A s u)). Qed.
Lemma lem7117811 {A : Type'} (s : A -> Prop) (u : A -> real) (k : A) : (term303 A s u k) = (term303 A s u k).
Proof. exact (eq_refl (term303 A s u k)). Qed.
Lemma lem7117812 {A : Type'} (s : A -> Prop) (u : A -> real) : (term301 A s u) = (term301 A s u).
Proof. exact (fun_ext (fun k : A => @lem7117811 A s u k)). Qed.
Lemma lem7117813 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7117814 {A : Type'} (s : A -> Prop) (u : A -> real) : (term311 A s u) = (term311 A s u).
Proof. exact (MK_COMB (@lem7117813 A) (@lem7117812 A s u)). Qed.
Lemma lem7117817 {A : Type'} (u : A -> real) (j : A) : (term304 A u j) = (term304 A u j).
Proof. exact (eq_refl (term304 A u j)). Qed.
Lemma lem7117818 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term312 A j s u) = (term312 A j s u).
Proof. exact (MK_COMB (@lem7117817 A u j) (@lem7117814 A s u)). Qed.
Lemma lem7117821 {A : Type'} (j : A) (s : A -> Prop) : (term286 A j s) = (term286 A j s).
Proof. exact (eq_refl (term286 A j s)). Qed.
Lemma lem7117822 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term313 A j s u) = (term313 A j s u).
Proof. exact (MK_COMB (@lem7117821 A j s) (@lem7117818 A j s u)). Qed.
Lemma lem7117823 {A : Type'} (s : A -> Prop) (u : A -> real) : (term315 A s u) = (term315 A s u).
Proof. exact (fun_ext (fun j : A => @lem7117822 A j s u)). Qed.
Lemma lem7117824 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7117825 {A : Type'} (s : A -> Prop) (u : A -> real) : (term317 A s u) = (term317 A s u).
Proof. exact (MK_COMB (@lem7117824 A) (@lem7117823 A s u)). Qed.
Lemma lem7117826 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7117827 {A : Type'} (s : A -> Prop) (u : A -> real) : (term319 A s u) = (term319 A s u).
Proof. exact (MK_COMB (@lem7117826) (@lem7117825 A s u)). Qed.
Lemma lem7117828 {A : Type'} (s : A -> Prop) (u : A -> real) : (term321 A s u) = (term321 A s u).
Proof. exact (MK_COMB (@lem7117827 A s u) (@lem7117806 A s u)). Qed.
Lemma lem7117829 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7117830 {A : Type'} (s : A -> Prop) (u : A -> real) : (term322 A s u) = (term322 A s u).
Proof. exact (MK_COMB (@lem7117829) (@lem7117828 A s u)). Qed.
Lemma lem7117831 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7117832 {A : Type'} (s : A -> Prop) (u : A -> real) : (term324 A s u) = (term324 A s u).
Proof. exact (MK_COMB (@lem7117831) (@lem7117830 A s u)). Qed.
Lemma lem7117833 {A : Type'} (s : A -> Prop) (u : A -> real) : (term354 A s u) = (term354 A s u).
Proof. exact (MK_COMB (@lem7117832 A s u) (@lem7117787)). Qed.
Lemma lem7117834 {A : Type'} (u : A -> real) : (term356 A u) = (term356 A u).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7117833 A s u)). Qed.
Lemma lem7117835 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7117836 {A : Type'} (u : A -> real) : (term358 A u) = (term358 A u).
Proof. exact (MK_COMB (@lem7117835 A) (@lem7117834 A u)). Qed.
Lemma lem7117837 {A : Type'} : (term360 A) = (term360 A).
Proof. exact (fun_ext (fun u : A -> real => @lem7117836 A u)). Qed.
Lemma lem7117838 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7117839 {A : Type'} : (term362 A) = (term362 A).
Proof. exact (MK_COMB (@lem7117838 A) (@lem7117837 A)). Qed.
Lemma lem7117908 {A : Type'} : (term361 A) = (term362 A).
Proof. exact (TRANS (@lem7117762 A) (@lem7117839 A)). Qed.
Lemma lem7117909 {A : Type'} : (term362 A) = (term361 A).
Proof. exact (SYM (@lem7117908 A)). Qed.
Lemma lem7117910 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term322 A s u) : term322 A s u.
Proof. exact (h1). Qed.
Lemma lem7117911 (h1 : term352) : term352.
Proof. exact (h1). Qed.
Lemma lem7117920 {A : Type'} (s : A -> Prop) (u : A -> real) (k : A) : (term370 A s u k) = (term371 A s u k).
Proof. exact (@lem17045 (@IN A k s) (term372 A u k)). Qed.
Lemma lem7117921 {A : Type'} (P : A -> Prop) : (term373 A P) = (term374 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem7117922 {A : Type'} (s : A -> Prop) (u : A -> real) : (term375 A s u) = (term376 A s u).
Proof. exact (@lem7117921 A (term301 A s u)). Qed.
Lemma lem7117923 {A : Type'} (s : A -> Prop) (u : A -> real) (k : A) : (term302 A s u k) = (term303 A s u k).
Proof. exact (eq_refl (term302 A s u k)). Qed.
Lemma lem7117924 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7117925 {A : Type'} (s : A -> Prop) (u : A -> real) (k : A) : (term377 A s u k) = (term370 A s u k).
Proof. exact (MK_COMB (@lem7117924) (@lem7117923 A s u k)). Qed.
Lemma lem7117926 {A : Type'} (s : A -> Prop) (u : A -> real) (k : A) : (term377 A s u k) = (term371 A s u k).
Proof. exact (TRANS (@lem7117925 A s u k) (@lem7117920 A s u k)). Qed.
Lemma lem7117927 {A : Type'} (s : A -> Prop) (u : A -> real) : (term378 A s u) = (term379 A s u).
Proof. exact (fun_ext (fun k : A => @lem7117926 A s u k)). Qed.
Lemma lem7117928 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7117929 {A : Type'} (s : A -> Prop) (u : A -> real) : (term376 A s u) = (term380 A s u).
Proof. exact (MK_COMB (@lem7117928 A) (@lem7117927 A s u)). Qed.
Lemma lem7117930 {A : Type'} (s : A -> Prop) (u : A -> real) : (term375 A s u) = (term380 A s u).
Proof. exact (TRANS (@lem7117922 A s u) (@lem7117929 A s u)). Qed.
Lemma lem7117932 {A : Type'} (u : A -> real) (j : A) : (term381 A u j) = (term381 A u j).
Proof. exact (eq_refl (term381 A u j)). Qed.
Lemma lem7117933 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term382 A j s u) = (term383 A j s u).
Proof. exact (MK_COMB (@lem7117932 A u j) (@lem7117930 A s u)). Qed.
Lemma lem7117934 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term384 A j s u) = (term382 A j s u).
Proof. exact (@lem17045 (term300 A u j) (term311 A s u)). Qed.
Lemma lem7117935 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term384 A j s u) = (term383 A j s u).
Proof. exact (TRANS (@lem7117934 A j s u) (@lem7117933 A j s u)). Qed.
Lemma lem7117937 {A : Type'} (j : A) (s : A -> Prop) : (term385 A j s) = (term385 A j s).
Proof. exact (eq_refl (term385 A j s)). Qed.
Lemma lem7117938 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term386 A j s u) = (term387 A j s u).
Proof. exact (MK_COMB (@lem7117937 A j s) (@lem7117935 A j s u)). Qed.
Lemma lem7117939 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term388 A j s u) = (term386 A j s u).
Proof. exact (@lem17045 (@IN A j s) (term312 A j s u)). Qed.
Lemma lem7117940 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term388 A j s u) = (term387 A j s u).
Proof. exact (TRANS (@lem7117939 A j s u) (@lem7117938 A j s u)). Qed.
Lemma lem7117941 {A : Type'} (P : A -> Prop) : (term373 A P) = (term374 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem7117942 {A : Type'} (s : A -> Prop) (u : A -> real) : (term389 A s u) = (term390 A s u).
Proof. exact (@lem7117941 A (term315 A s u)). Qed.
Lemma lem7117943 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term391 A s u j) = (term313 A j s u).
Proof. exact (eq_refl (term391 A s u j)). Qed.
Lemma lem7117944 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7117945 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term392 A s u j) = (term388 A j s u).
Proof. exact (MK_COMB (@lem7117944) (@lem7117943 A j s u)). Qed.
Lemma lem7117946 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term392 A s u j) = (term387 A j s u).
Proof. exact (TRANS (@lem7117945 A j s u) (@lem7117940 A j s u)). Qed.
Lemma lem7117947 {A : Type'} (s : A -> Prop) (u : A -> real) : (term393 A s u) = (term394 A s u).
Proof. exact (fun_ext (fun j : A => @lem7117946 A j s u)). Qed.
Lemma lem7117948 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7117949 {A : Type'} (s : A -> Prop) (u : A -> real) : (term390 A s u) = (term395 A s u).
Proof. exact (MK_COMB (@lem7117948 A) (@lem7117947 A s u)). Qed.
Lemma lem7117950 {A : Type'} (s : A -> Prop) (u : A -> real) : (term389 A s u) = (term395 A s u).
Proof. exact (TRANS (@lem7117942 A s u) (@lem7117949 A s u)). Qed.
Lemma lem7117957 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term396 A s u i) = (term397 A s u i).
Proof. exact (@lem17362 (@IN A i s) (term398 A u i)). Qed.
Lemma lem7117958 {A : Type'} (P : A -> Prop) : (term399 A P) = (term400 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7117959 {A : Type'} (s : A -> Prop) (u : A -> real) : (term401 A s u) = (term402 A s u).
Proof. exact (@lem7117958 A (term367 A s u)). Qed.
Lemma lem7117960 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term403 A s u i) = (term366 A s u i).
Proof. exact (eq_refl (term403 A s u i)). Qed.
Lemma lem7117961 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7117962 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term404 A s u i) = (term396 A s u i).
Proof. exact (MK_COMB (@lem7117961) (@lem7117960 A s u i)). Qed.
Lemma lem7117963 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term404 A s u i) = (term397 A s u i).
Proof. exact (TRANS (@lem7117962 A s u i) (@lem7117957 A s u i)). Qed.
Lemma lem7117964 {A : Type'} (s : A -> Prop) (u : A -> real) : (term405 A s u) = (term406 A s u).
Proof. exact (fun_ext (fun i : A => @lem7117963 A s u i)). Qed.
Lemma lem7117965 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7117966 {A : Type'} (s : A -> Prop) (u : A -> real) : (term402 A s u) = (term407 A s u).
Proof. exact (MK_COMB (@lem7117965 A) (@lem7117964 A s u)). Qed.
Lemma lem7117967 {A : Type'} (s : A -> Prop) (u : A -> real) : (term401 A s u) = (term407 A s u).
Proof. exact (TRANS (@lem7117959 A s u) (@lem7117966 A s u)). Qed.
Lemma lem7117974 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term408 A s u i) = (term409 A s u i).
Proof. exact (@lem17362 (@IN A i s) (term410 A u i)). Qed.
Lemma lem7117975 {A : Type'} (P : A -> Prop) : (term399 A P) = (term400 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7117976 {A : Type'} (s : A -> Prop) (u : A -> real) : (term411 A s u) = (term412 A s u).
Proof. exact (@lem7117975 A (term364 A s u)). Qed.
Lemma lem7117977 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term413 A s u i) = (term363 A s u i).
Proof. exact (eq_refl (term413 A s u i)). Qed.
Lemma lem7117978 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7117979 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term414 A s u i) = (term408 A s u i).
Proof. exact (MK_COMB (@lem7117978) (@lem7117977 A s u i)). Qed.
Lemma lem7117980 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term414 A s u i) = (term409 A s u i).
Proof. exact (TRANS (@lem7117979 A s u i) (@lem7117974 A s u i)). Qed.
Lemma lem7117981 {A : Type'} (s : A -> Prop) (u : A -> real) : (term415 A s u) = (term416 A s u).
Proof. exact (fun_ext (fun i : A => @lem7117980 A s u i)). Qed.
Lemma lem7117982 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7117983 {A : Type'} (s : A -> Prop) (u : A -> real) : (term412 A s u) = (term417 A s u).
Proof. exact (MK_COMB (@lem7117982 A) (@lem7117981 A s u)). Qed.
Lemma lem7117984 {A : Type'} (s : A -> Prop) (u : A -> real) : (term411 A s u) = (term417 A s u).
Proof. exact (TRANS (@lem7117976 A s u) (@lem7117983 A s u)). Qed.
Lemma lem7117985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7117986 {A : Type'} (s : A -> Prop) (u : A -> real) : (term418 A s u) = (term419 A s u).
Proof. exact (MK_COMB (@lem7117985) (@lem7117967 A s u)). Qed.
Lemma lem7117987 {A : Type'} (s : A -> Prop) (u : A -> real) : (term420 A s u) = (term421 A s u).
Proof. exact (MK_COMB (@lem7117986 A s u) (@lem7117984 A s u)). Qed.
Lemma lem7117988 {A : Type'} (s : A -> Prop) (u : A -> real) : (term422 A s u) = (term420 A s u).
Proof. exact (@lem17160 (term368 A s u) (term365 A s u)). Qed.
Lemma lem7117989 {A : Type'} (s : A -> Prop) (u : A -> real) : (term422 A s u) = (term421 A s u).
Proof. exact (TRANS (@lem7117988 A s u) (@lem7117987 A s u)). Qed.
Lemma lem7117990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7117991 {A : Type'} (s : A -> Prop) (u : A -> real) : (term423 A s u) = (term424 A s u).
Proof. exact (MK_COMB (@lem7117990) (@lem7117950 A s u)). Qed.
Lemma lem7117992 {A : Type'} (s : A -> Prop) (u : A -> real) : (term425 A s u) = (term426 A s u).
Proof. exact (MK_COMB (@lem7117991 A s u) (@lem7117989 A s u)). Qed.
Lemma lem7117993 {A : Type'} (s : A -> Prop) (u : A -> real) : (term322 A s u) = (term425 A s u).
Proof. exact (@lem17160 (term317 A s u) (term320 A s u)). Qed.
Lemma lem7117994 {A : Type'} (s : A -> Prop) (u : A -> real) : (term322 A s u) = (term426 A s u).
Proof. exact (TRANS (@lem7117993 A s u) (@lem7117992 A s u)). Qed.
Lemma lem7118189 {A : Type'} (P : A -> Prop) (Q : Prop) : (term427 A P Q) = (term428 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7118190 {A : Type'} (P : A -> Prop) (Q : Prop) : (term427 A P Q) = (term428 A P Q).
Proof. exact (@lem7118189 A P Q). Qed.
Lemma lem7118191 {A : Type'} (s : A -> Prop) (u : A -> real) : (term429 A s u) = (term430 A s u).
Proof. exact (@lem7118190 A (term406 A s u) (term417 A s u)). Qed.
Lemma lem7118192 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term431 A s u i) = (term397 A s u i).
Proof. exact (eq_refl (term431 A s u i)). Qed.
Lemma lem7118193 {A : Type'} (s : A -> Prop) (u : A -> real) : (term432 A s u) = (term406 A s u).
Proof. exact (fun_ext (fun i : A => @lem7118192 A s u i)). Qed.
Lemma lem7118194 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7118195 {A : Type'} (s : A -> Prop) (u : A -> real) : (term433 A s u) = (term407 A s u).
Proof. exact (MK_COMB (@lem7118194 A) (@lem7118193 A s u)). Qed.
Lemma lem7118196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118197 {A : Type'} (s : A -> Prop) (u : A -> real) : (term434 A s u) = (term419 A s u).
Proof. exact (MK_COMB (@lem7118196) (@lem7118195 A s u)). Qed.
Lemma lem7118198 {A : Type'} (s : A -> Prop) (u : A -> real) : (term417 A s u) = (term417 A s u).
Proof. exact (eq_refl (term417 A s u)). Qed.
Lemma lem7118199 {A : Type'} (s : A -> Prop) (u : A -> real) : (term429 A s u) = (term421 A s u).
Proof. exact (MK_COMB (@lem7118197 A s u) (@lem7118198 A s u)). Qed.
Lemma lem7118200 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7118201 {A : Type'} (s : A -> Prop) (u : A -> real) : (term435 A s u) = (term436 A s u).
Proof. exact (MK_COMB (@lem7118200) (@lem7118199 A s u)). Qed.
Lemma lem7118202 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term431 A s u i) = (term397 A s u i).
Proof. exact (eq_refl (term431 A s u i)). Qed.
Lemma lem7118203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118204 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term437 A s u i) = (term438 A s u i).
Proof. exact (MK_COMB (@lem7118203) (@lem7118202 A s u i)). Qed.
Lemma lem7118205 {A : Type'} (s : A -> Prop) (u : A -> real) : (term417 A s u) = (term417 A s u).
Proof. exact (eq_refl (term417 A s u)). Qed.
Lemma lem7118206 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term439 A i s u) = (term440 A i s u).
Proof. exact (MK_COMB (@lem7118204 A s u i) (@lem7118205 A s u)). Qed.
Lemma lem7118207 {A : Type'} (s : A -> Prop) (u : A -> real) : (term441 A s u) = (term442 A s u).
Proof. exact (fun_ext (fun i : A => @lem7118206 A i s u)). Qed.
Lemma lem7118208 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7118209 {A : Type'} (s : A -> Prop) (u : A -> real) : (term430 A s u) = (term443 A s u).
Proof. exact (MK_COMB (@lem7118208 A) (@lem7118207 A s u)). Qed.
Lemma lem7118210 {A : Type'} (s : A -> Prop) (u : A -> real) : ((term429 A s u) = (term430 A s u)) = ((term421 A s u) = (term443 A s u)).
Proof. exact (MK_COMB (@lem7118201 A s u) (@lem7118209 A s u)). Qed.
Lemma lem7118211 {A : Type'} (s : A -> Prop) (u : A -> real) : (term421 A s u) = (term443 A s u).
Proof. exact (EQ_MP (@lem7118210 A s u) (@lem7118191 A s u)). Qed.
Lemma lem7118213 {A : Type'} (P : Prop) (Q : A -> Prop) : (term280 A P Q) = (term279 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7118214 {A : Type'} (P : Prop) (Q : A -> Prop) : (term280 A P Q) = (term279 A P Q).
Proof. exact (@lem7118213 A P Q). Qed.
Lemma lem7118215 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term444 A i s u) = (term445 A i s u).
Proof. exact (@lem7118214 A (term397 A s u i) (term416 A s u)). Qed.
Lemma lem7118216 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term446 A s u i) = (term409 A s u i).
Proof. exact (eq_refl (term446 A s u i)). Qed.
Lemma lem7118217 {A : Type'} (s : A -> Prop) (u : A -> real) : (term447 A s u) = (term416 A s u).
Proof. exact (fun_ext (fun i : A => @lem7118216 A s u i)). Qed.
Lemma lem7118218 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7118219 {A : Type'} (s : A -> Prop) (u : A -> real) : (term448 A s u) = (term417 A s u).
Proof. exact (MK_COMB (@lem7118218 A) (@lem7118217 A s u)). Qed.
Lemma lem7118220 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term438 A s u i) = (term438 A s u i).
Proof. exact (eq_refl (term438 A s u i)). Qed.
Lemma lem7118221 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term444 A i s u) = (term440 A i s u).
Proof. exact (MK_COMB (@lem7118220 A s u i) (@lem7118219 A s u)). Qed.
Lemma lem7118222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7118223 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term449 A i s u) = (term450 A i s u).
Proof. exact (MK_COMB (@lem7118222) (@lem7118221 A i s u)). Qed.
Lemma lem7118224 {A : Type'} (s : A -> Prop) (u : A -> real) (i' : A) : (term446 A s u i') = (term409 A s u i').
Proof. exact (eq_refl (term446 A s u i')). Qed.
Lemma lem7118225 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term438 A s u i) = (term438 A s u i).
Proof. exact (eq_refl (term438 A s u i)). Qed.
Lemma lem7118226 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) : (term451 A i s u i') = (term452 A i s u i').
Proof. exact (MK_COMB (@lem7118225 A s u i) (@lem7118224 A s u i')). Qed.
Lemma lem7118227 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term453 A i s u) = (term454 A i s u).
Proof. exact (fun_ext (fun i' : A => @lem7118226 A i s u i')). Qed.
Lemma lem7118228 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7118229 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term445 A i s u) = (term455 A i s u).
Proof. exact (MK_COMB (@lem7118228 A) (@lem7118227 A i s u)). Qed.
Lemma lem7118230 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : ((term444 A i s u) = (term445 A i s u)) = ((term440 A i s u) = (term455 A i s u)).
Proof. exact (MK_COMB (@lem7118223 A i s u) (@lem7118229 A i s u)). Qed.
Lemma lem7118231 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term440 A i s u) = (term455 A i s u).
Proof. exact (EQ_MP (@lem7118230 A i s u) (@lem7118215 A i s u)). Qed.
Lemma lem7118232 {A : Type'} (s : A -> Prop) (u : A -> real) : (term442 A s u) = (term456 A s u).
Proof. exact (fun_ext (fun i : A => @lem7118231 A i s u)). Qed.
Lemma lem7118233 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7118234 {A : Type'} (s : A -> Prop) (u : A -> real) : (term443 A s u) = (term457 A s u).
Proof. exact (MK_COMB (@lem7118233 A) (@lem7118232 A s u)). Qed.
Lemma lem7118235 {A : Type'} (s : A -> Prop) (u : A -> real) : (term421 A s u) = (term457 A s u).
Proof. exact (TRANS (@lem7118211 A s u) (@lem7118234 A s u)). Qed.
Lemma lem7118236 {A : Type'} (s : A -> Prop) (u : A -> real) : (term424 A s u) = (term424 A s u).
Proof. exact (eq_refl (term424 A s u)). Qed.
Lemma lem7118237 {A : Type'} (s : A -> Prop) (u : A -> real) : (term426 A s u) = (term458 A s u).
Proof. exact (MK_COMB (@lem7118236 A s u) (@lem7118235 A s u)). Qed.
Lemma lem7118239 {A : Type'} (P : Prop) (Q : A -> Prop) : (term280 A P Q) = (term279 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7118240 {A : Type'} (P : Prop) (Q : A -> Prop) : (term280 A P Q) = (term279 A P Q).
Proof. exact (@lem7118239 A P Q). Qed.
Lemma lem7118241 {A : Type'} (s : A -> Prop) (u : A -> real) : (term459 A s u) = (term460 A s u).
Proof. exact (@lem7118240 A (term395 A s u) (term456 A s u)). Qed.
Lemma lem7118242 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term461 A s u i) = (term455 A i s u).
Proof. exact (eq_refl (term461 A s u i)). Qed.
Lemma lem7118243 {A : Type'} (s : A -> Prop) (u : A -> real) : (term462 A s u) = (term456 A s u).
Proof. exact (fun_ext (fun i : A => @lem7118242 A i s u)). Qed.
Lemma lem7118244 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7118245 {A : Type'} (s : A -> Prop) (u : A -> real) : (term463 A s u) = (term457 A s u).
Proof. exact (MK_COMB (@lem7118244 A) (@lem7118243 A s u)). Qed.
Lemma lem7118246 {A : Type'} (s : A -> Prop) (u : A -> real) : (term424 A s u) = (term424 A s u).
Proof. exact (eq_refl (term424 A s u)). Qed.
Lemma lem7118247 {A : Type'} (s : A -> Prop) (u : A -> real) : (term459 A s u) = (term458 A s u).
Proof. exact (MK_COMB (@lem7118246 A s u) (@lem7118245 A s u)). Qed.
Lemma lem7118248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7118249 {A : Type'} (s : A -> Prop) (u : A -> real) : (term464 A s u) = (term465 A s u).
Proof. exact (MK_COMB (@lem7118248) (@lem7118247 A s u)). Qed.
Lemma lem7118250 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term461 A s u i) = (term455 A i s u).
Proof. exact (eq_refl (term461 A s u i)). Qed.
Lemma lem7118251 {A : Type'} (s : A -> Prop) (u : A -> real) : (term424 A s u) = (term424 A s u).
Proof. exact (eq_refl (term424 A s u)). Qed.
Lemma lem7118252 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term466 A s u i) = (term467 A i s u).
Proof. exact (MK_COMB (@lem7118251 A s u) (@lem7118250 A i s u)). Qed.
Lemma lem7118253 {A : Type'} (s : A -> Prop) (u : A -> real) : (term468 A s u) = (term469 A s u).
Proof. exact (fun_ext (fun i : A => @lem7118252 A i s u)). Qed.
Lemma lem7118254 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7118255 {A : Type'} (s : A -> Prop) (u : A -> real) : (term460 A s u) = (term470 A s u).
Proof. exact (MK_COMB (@lem7118254 A) (@lem7118253 A s u)). Qed.
Lemma lem7118256 {A : Type'} (s : A -> Prop) (u : A -> real) : ((term459 A s u) = (term460 A s u)) = ((term458 A s u) = (term470 A s u)).
Proof. exact (MK_COMB (@lem7118249 A s u) (@lem7118255 A s u)). Qed.
Lemma lem7118257 {A : Type'} (s : A -> Prop) (u : A -> real) : (term458 A s u) = (term470 A s u).
Proof. exact (EQ_MP (@lem7118256 A s u) (@lem7118241 A s u)). Qed.
Lemma lem7118259 {A : Type'} (P : Prop) (Q : A -> Prop) : (term280 A P Q) = (term279 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7118260 {A : Type'} (P : Prop) (Q : A -> Prop) : (term280 A P Q) = (term279 A P Q).
Proof. exact (@lem7118259 A P Q). Qed.
Lemma lem7118261 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term471 A i s u) = (term472 A i s u).
Proof. exact (@lem7118260 A (term395 A s u) (term454 A i s u)). Qed.
Lemma lem7118262 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) : (term473 A i s u i') = (term452 A i s u i').
Proof. exact (eq_refl (term473 A i s u i')). Qed.
Lemma lem7118263 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term474 A i s u) = (term454 A i s u).
Proof. exact (fun_ext (fun i' : A => @lem7118262 A i s u i')). Qed.
Lemma lem7118264 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7118265 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term475 A i s u) = (term455 A i s u).
Proof. exact (MK_COMB (@lem7118264 A) (@lem7118263 A i s u)). Qed.
Lemma lem7118266 {A : Type'} (s : A -> Prop) (u : A -> real) : (term424 A s u) = (term424 A s u).
Proof. exact (eq_refl (term424 A s u)). Qed.
Lemma lem7118267 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term471 A i s u) = (term467 A i s u).
Proof. exact (MK_COMB (@lem7118266 A s u) (@lem7118265 A i s u)). Qed.
Lemma lem7118268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7118269 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term476 A i s u) = (term477 A i s u).
Proof. exact (MK_COMB (@lem7118268) (@lem7118267 A i s u)). Qed.
Lemma lem7118270 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) : (term473 A i s u i') = (term452 A i s u i').
Proof. exact (eq_refl (term473 A i s u i')). Qed.
Lemma lem7118271 {A : Type'} (s : A -> Prop) (u : A -> real) : (term424 A s u) = (term424 A s u).
Proof. exact (eq_refl (term424 A s u)). Qed.
Lemma lem7118272 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) : (term478 A i s u i') = (term479 A i s u i').
Proof. exact (MK_COMB (@lem7118271 A s u) (@lem7118270 A i s u i')). Qed.
Lemma lem7118273 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term480 A i s u) = (term481 A i s u).
Proof. exact (fun_ext (fun i' : A => @lem7118272 A i s u i')). Qed.
Lemma lem7118274 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7118275 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term472 A i s u) = (term482 A i s u).
Proof. exact (MK_COMB (@lem7118274 A) (@lem7118273 A i s u)). Qed.
Lemma lem7118276 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : ((term471 A i s u) = (term472 A i s u)) = ((term467 A i s u) = (term482 A i s u)).
Proof. exact (MK_COMB (@lem7118269 A i s u) (@lem7118275 A i s u)). Qed.
Lemma lem7118277 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) : (term467 A i s u) = (term482 A i s u).
Proof. exact (EQ_MP (@lem7118276 A i s u) (@lem7118261 A i s u)). Qed.
Lemma lem7118278 {A : Type'} (s : A -> Prop) (u : A -> real) : (term469 A s u) = (term483 A s u).
Proof. exact (fun_ext (fun i : A => @lem7118277 A i s u)). Qed.
Lemma lem7118279 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7118280 {A : Type'} (s : A -> Prop) (u : A -> real) : (term470 A s u) = (term484 A s u).
Proof. exact (MK_COMB (@lem7118279 A) (@lem7118278 A s u)). Qed.
Lemma lem7118281 {A : Type'} (s : A -> Prop) (u : A -> real) : (term458 A s u) = (term484 A s u).
Proof. exact (TRANS (@lem7118257 A s u) (@lem7118280 A s u)). Qed.
Lemma lem7118283 {A : Type'} (s : A -> Prop) (u : A -> real) : (term426 A s u) = (term484 A s u).
Proof. exact (TRANS (@lem7118237 A s u) (@lem7118281 A s u)). Qed.
Lemma lem7118284 {A : Type'} (s : A -> Prop) (u : A -> real) : (term322 A s u) = (term484 A s u).
Proof. exact (TRANS (@lem7117994 A s u) (@lem7118283 A s u)). Qed.
Lemma lem7118285 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term322 A s u) : term484 A s u.
Proof. exact (EQ_MP (@lem7118284 A s u) (@lem7117910 A s u h1)). Qed.
Lemma lem7118291 (u : real) : (term186 u) = (term70 u).
Proof. exact (@lem16933 (term70 u)). Qed.
Lemma lem7118294 (u : real) : (term485 u) = (term485 u).
Proof. exact (eq_refl (term485 u)). Qed.
Lemma lem7118296 (u : real) : (term486 u) = (term486 u).
Proof. exact (eq_refl (term486 u)). Qed.
Lemma lem7118297 (u : real) : (term487 u) = (term488 u).
Proof. exact (MK_COMB (@lem7118296 u) (@lem7118291 u)). Qed.
Lemma lem7118298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118299 (u : real) : (term489 u) = (term490 u).
Proof. exact (MK_COMB (@lem7118298) (@lem7118297 u)). Qed.
Lemma lem7118300 (u : real) : (term491 u) = (term492 u).
Proof. exact (MK_COMB (@lem7118299 u) (@lem7118294 u)). Qed.
Lemma lem7118301 (u : real) : ((term196 u) = (term197 u)) = (term491 u).
Proof. exact (@lem17784 (term196 u) (term197 u)). Qed.
Lemma lem7118302 (u : real) : ((term196 u) = (term197 u)) = (term492 u).
Proof. exact (TRANS (@lem7118301 u) (@lem7118300 u)). Qed.
Lemma lem7118303 : term333 = term493.
Proof. exact (fun_ext (fun u : real => @lem7118302 u)). Qed.
Lemma lem7118304 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118305 : term346 = term494.
Proof. exact (MK_COMB (@lem7118304) (@lem7118303)). Qed.
Lemma lem7118311 (u : real) : (term198 u) = (term199 u).
Proof. exact (@lem16933 (term199 u)). Qed.
Lemma lem7118314 (u : real) : (term495 u) = (term495 u).
Proof. exact (eq_refl (term495 u)). Qed.
Lemma lem7118316 (u : real) : (term496 u) = (term496 u).
Proof. exact (eq_refl (term496 u)). Qed.
Lemma lem7118317 (u : real) : (term497 u) = (term498 u).
Proof. exact (MK_COMB (@lem7118316 u) (@lem7118311 u)). Qed.
Lemma lem7118318 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118319 (u : real) : (term499 u) = (term500 u).
Proof. exact (MK_COMB (@lem7118318) (@lem7118317 u)). Qed.
Lemma lem7118320 (u : real) : (term501 u) = (term502 u).
Proof. exact (MK_COMB (@lem7118319 u) (@lem7118314 u)). Qed.
Lemma lem7118321 (u : real) : ((term209 u) = (term210 u)) = (term501 u).
Proof. exact (@lem17784 (term209 u) (term210 u)). Qed.
Lemma lem7118322 (u : real) : ((term209 u) = (term210 u)) = (term502 u).
Proof. exact (TRANS (@lem7118321 u) (@lem7118320 u)). Qed.
Lemma lem7118323 : term334 = term503.
Proof. exact (fun_ext (fun u : real => @lem7118322 u)). Qed.
Lemma lem7118324 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118325 : term351 = term504.
Proof. exact (MK_COMB (@lem7118324) (@lem7118323)). Qed.
Lemma lem7118326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118327 : term348 = term505.
Proof. exact (MK_COMB (@lem7118326) (@lem7118305)). Qed.
Lemma lem7118328 : term352 = term506.
Proof. exact (MK_COMB (@lem7118327) (@lem7118325)). Qed.
Lemma lem7118330 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term327 A P Q) = (term328 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7118331 (P : real -> Prop) (Q : real -> Prop) : (term329 P Q) = (term330 P Q).
Proof. exact (@lem7118330 real P Q). Qed.
Lemma lem7118332 : term507 = term508.
Proof. exact (@lem7118331 term509 term510). Qed.
Lemma lem7118333 (u : real) : (term511 u) = (term488 u).
Proof. exact (eq_refl (term511 u)). Qed.
Lemma lem7118334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118335 (u : real) : (term512 u) = (term490 u).
Proof. exact (MK_COMB (@lem7118334) (@lem7118333 u)). Qed.
Lemma lem7118336 (u : real) : (term513 u) = (term485 u).
Proof. exact (eq_refl (term513 u)). Qed.
Lemma lem7118337 (u : real) : (term514 u) = (term492 u).
Proof. exact (MK_COMB (@lem7118335 u) (@lem7118336 u)). Qed.
Lemma lem7118338 : term515 = term493.
Proof. exact (fun_ext (fun u : real => @lem7118337 u)). Qed.
Lemma lem7118339 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118340 : term507 = term494.
Proof. exact (MK_COMB (@lem7118339) (@lem7118338)). Qed.
Lemma lem7118341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7118342 : term516 = term517.
Proof. exact (MK_COMB (@lem7118341) (@lem7118340)). Qed.
Lemma lem7118343 (u : real) : (term511 u) = (term488 u).
Proof. exact (eq_refl (term511 u)). Qed.
Lemma lem7118344 : term518 = term509.
Proof. exact (fun_ext (fun u : real => @lem7118343 u)). Qed.
Lemma lem7118345 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118346 : term519 = term520.
Proof. exact (MK_COMB (@lem7118345) (@lem7118344)). Qed.
Lemma lem7118347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118348 : term521 = term522.
Proof. exact (MK_COMB (@lem7118347) (@lem7118346)). Qed.
Lemma lem7118349 (u : real) : (term513 u) = (term485 u).
Proof. exact (eq_refl (term513 u)). Qed.
Lemma lem7118350 : term523 = term510.
Proof. exact (fun_ext (fun u : real => @lem7118349 u)). Qed.
Lemma lem7118351 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118352 : term524 = term525.
Proof. exact (MK_COMB (@lem7118351) (@lem7118350)). Qed.
Lemma lem7118353 : term508 = term526.
Proof. exact (MK_COMB (@lem7118348) (@lem7118352)). Qed.
Lemma lem7118354 : (term507 = term508) = (term494 = term526).
Proof. exact (MK_COMB (@lem7118342) (@lem7118353)). Qed.
Lemma lem7118355 : term494 = term526.
Proof. exact (EQ_MP (@lem7118354) (@lem7118332)). Qed.
Lemma lem7118452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118453 : term505 = term527.
Proof. exact (MK_COMB (@lem7118452) (@lem7118355)). Qed.
Lemma lem7118455 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term327 A P Q) = (term328 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7118456 (P : real -> Prop) (Q : real -> Prop) : (term329 P Q) = (term330 P Q).
Proof. exact (@lem7118455 real P Q). Qed.
Lemma lem7118457 : term528 = term529.
Proof. exact (@lem7118456 term530 term531). Qed.
Lemma lem7118458 (u : real) : (term532 u) = (term498 u).
Proof. exact (eq_refl (term532 u)). Qed.
Lemma lem7118459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118460 (u : real) : (term533 u) = (term500 u).
Proof. exact (MK_COMB (@lem7118459) (@lem7118458 u)). Qed.
Lemma lem7118461 (u : real) : (term534 u) = (term495 u).
Proof. exact (eq_refl (term534 u)). Qed.
Lemma lem7118462 (u : real) : (term535 u) = (term502 u).
Proof. exact (MK_COMB (@lem7118460 u) (@lem7118461 u)). Qed.
Lemma lem7118463 : term536 = term503.
Proof. exact (fun_ext (fun u : real => @lem7118462 u)). Qed.
Lemma lem7118464 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118465 : term528 = term504.
Proof. exact (MK_COMB (@lem7118464) (@lem7118463)). Qed.
Lemma lem7118466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7118467 : term537 = term538.
Proof. exact (MK_COMB (@lem7118466) (@lem7118465)). Qed.
Lemma lem7118468 (u : real) : (term532 u) = (term498 u).
Proof. exact (eq_refl (term532 u)). Qed.
Lemma lem7118469 : term539 = term530.
Proof. exact (fun_ext (fun u : real => @lem7118468 u)). Qed.
Lemma lem7118470 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118471 : term540 = term541.
Proof. exact (MK_COMB (@lem7118470) (@lem7118469)). Qed.
Lemma lem7118472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118473 : term542 = term543.
Proof. exact (MK_COMB (@lem7118472) (@lem7118471)). Qed.
Lemma lem7118474 (u : real) : (term534 u) = (term495 u).
Proof. exact (eq_refl (term534 u)). Qed.
Lemma lem7118475 : term544 = term531.
Proof. exact (fun_ext (fun u : real => @lem7118474 u)). Qed.
Lemma lem7118476 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118477 : term545 = term546.
Proof. exact (MK_COMB (@lem7118476) (@lem7118475)). Qed.
Lemma lem7118478 : term529 = term547.
Proof. exact (MK_COMB (@lem7118473) (@lem7118477)). Qed.
Lemma lem7118479 : (term528 = term529) = (term504 = term547).
Proof. exact (MK_COMB (@lem7118467) (@lem7118478)). Qed.
Lemma lem7118480 : term504 = term547.
Proof. exact (EQ_MP (@lem7118479) (@lem7118457)). Qed.
Lemma lem7118579 : term506 = term548.
Proof. exact (MK_COMB (@lem7118453) (@lem7118480)). Qed.
Lemma lem7118580 : term352 = term548.
Proof. exact (TRANS (@lem7118328) (@lem7118579)). Qed.
Lemma lem7118581 (h1 : term352) : term548.
Proof. exact (EQ_MP (@lem7118580) (@lem7117911 h1)). Qed.
Lemma lem7118582 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (h1 : term482 A i s u) : term482 A i s u.
Proof. exact (h1). Qed.
Lemma lem7118583 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term479 A i s u i'.
Proof. exact (h1). Qed.
Lemma lem7118608 (u : real) : (term495 u) = (term495 u).
Proof. exact (eq_refl (term495 u)). Qed.
Lemma lem7118609 : term531 = term531.
Proof. exact (fun_ext (fun u : real => @lem7118608 u)). Qed.
Lemma lem7118610 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118611 : term546 = term546.
Proof. exact (MK_COMB (@lem7118610) (@lem7118609)). Qed.
Lemma lem7118632 (u : real) : (term498 u) = (term498 u).
Proof. exact (eq_refl (term498 u)). Qed.
Lemma lem7118633 : term530 = term530.
Proof. exact (fun_ext (fun u : real => @lem7118632 u)). Qed.
Lemma lem7118634 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118635 : term541 = term541.
Proof. exact (MK_COMB (@lem7118634) (@lem7118633)). Qed.
Lemma lem7118636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118637 : term543 = term543.
Proof. exact (MK_COMB (@lem7118636) (@lem7118635)). Qed.
Lemma lem7118638 : term547 = term547.
Proof. exact (MK_COMB (@lem7118637) (@lem7118611)). Qed.
Lemma lem7118665 (u : real) : (term485 u) = (term485 u).
Proof. exact (eq_refl (term485 u)). Qed.
Lemma lem7118666 : term510 = term510.
Proof. exact (fun_ext (fun u : real => @lem7118665 u)). Qed.
Lemma lem7118667 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118668 : term525 = term525.
Proof. exact (MK_COMB (@lem7118667) (@lem7118666)). Qed.
Lemma lem7118691 (u : real) : (term488 u) = (term488 u).
Proof. exact (eq_refl (term488 u)). Qed.
Lemma lem7118692 : term509 = term509.
Proof. exact (fun_ext (fun u : real => @lem7118691 u)). Qed.
Lemma lem7118693 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118694 : term520 = term520.
Proof. exact (MK_COMB (@lem7118693) (@lem7118692)). Qed.
Lemma lem7118695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118696 : term522 = term522.
Proof. exact (MK_COMB (@lem7118695) (@lem7118694)). Qed.
Lemma lem7118697 : term526 = term526.
Proof. exact (MK_COMB (@lem7118696) (@lem7118668)). Qed.
Lemma lem7118698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118699 : term527 = term527.
Proof. exact (MK_COMB (@lem7118698) (@lem7118697)). Qed.
Lemma lem7118700 : term548 = term548.
Proof. exact (MK_COMB (@lem7118699) (@lem7118638)). Qed.
Lemma lem7118701 (h1 : term352) : term548.
Proof. exact (EQ_MP (@lem7118700) (@lem7118581 h1)). Qed.
Lemma lem7118748 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) : (term452 A i s u i') = (term452 A i s u i').
Proof. exact (eq_refl (term452 A i s u i')). Qed.
Lemma lem7118771 {A : Type'} (s : A -> Prop) (u : A -> real) (k : A) : (term371 A s u k) = (term371 A s u k).
Proof. exact (eq_refl (term371 A s u k)). Qed.
Lemma lem7118772 {A : Type'} (s : A -> Prop) (u : A -> real) : (term379 A s u) = (term379 A s u).
Proof. exact (fun_ext (fun k : A => @lem7118771 A s u k)). Qed.
Lemma lem7118773 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7118774 {A : Type'} (s : A -> Prop) (u : A -> real) : (term380 A s u) = (term380 A s u).
Proof. exact (MK_COMB (@lem7118773 A) (@lem7118772 A s u)). Qed.
Lemma lem7118789 {A : Type'} (u : A -> real) (j : A) : (term381 A u j) = (term381 A u j).
Proof. exact (eq_refl (term381 A u j)). Qed.
Lemma lem7118790 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term383 A j s u) = (term383 A j s u).
Proof. exact (MK_COMB (@lem7118789 A u j) (@lem7118774 A s u)). Qed.
Lemma lem7118799 {A : Type'} (j : A) (s : A -> Prop) : (term385 A j s) = (term385 A j s).
Proof. exact (eq_refl (term385 A j s)). Qed.
Lemma lem7118800 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term387 A j s u) = (term387 A j s u).
Proof. exact (MK_COMB (@lem7118799 A j s) (@lem7118790 A j s u)). Qed.
Lemma lem7118801 {A : Type'} (s : A -> Prop) (u : A -> real) : (term394 A s u) = (term394 A s u).
Proof. exact (fun_ext (fun j : A => @lem7118800 A j s u)). Qed.
Lemma lem7118802 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7118803 {A : Type'} (s : A -> Prop) (u : A -> real) : (term395 A s u) = (term395 A s u).
Proof. exact (MK_COMB (@lem7118802 A) (@lem7118801 A s u)). Qed.
Lemma lem7118804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7118805 {A : Type'} (s : A -> Prop) (u : A -> real) : (term424 A s u) = (term424 A s u).
Proof. exact (MK_COMB (@lem7118804) (@lem7118803 A s u)). Qed.
Lemma lem7118806 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) : (term479 A i s u i') = (term479 A i s u i').
Proof. exact (MK_COMB (@lem7118805 A s u) (@lem7118748 A i s u i')). Qed.
Lemma lem7118807 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term479 A i s u i'.
Proof. exact (EQ_MP (@lem7118806 A i s u i') (@lem7118583 A i s u i' h1)). Qed.
Lemma lem7118808 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term452 A i s u i'.
Proof. exact (proj2 (@lem7118807 A i s u i' h1)). Qed.
Lemma lem7118809 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term395 A s u.
Proof. exact (proj1 (@lem7118807 A i s u i' h1)). Qed.
Lemma lem7118810 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term409 A s u i'.
Proof. exact (proj2 (@lem7118808 A i s u i' h1)). Qed.
Lemma lem7118811 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term397 A s u i.
Proof. exact (proj1 (@lem7118808 A i s u i' h1)). Qed.
Lemma lem7118816 (h1 : term352) : term547.
Proof. exact (proj2 (@lem7118701 h1)). Qed.
Lemma lem7118817 (h1 : term352) : term526.
Proof. exact (proj1 (@lem7118701 h1)). Qed.
Lemma lem7118819 (h1 : term352) : term541.
Proof. exact (proj1 (@lem7118816 h1)). Qed.
Lemma lem7118821 (h1 : term352) : term520.
Proof. exact (proj1 (@lem7118817 h1)). Qed.
Lemma lem7118823 {A : Type'} (P : Prop) (Q : A -> Prop) : (term549 A P Q) = (term550 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7118824 {A : Type'} (P : Prop) (Q : A -> Prop) : (term549 A P Q) = (term550 A P Q).
Proof. exact (@lem7118823 A P Q). Qed.
Lemma lem7118825 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term551 A j s u) = (term552 A j s u).
Proof. exact (@lem7118824 A (term553 A u j) (term379 A s u)). Qed.
Lemma lem7118826 {A : Type'} (s : A -> Prop) (u : A -> real) (k : A) : (term554 A s u k) = (term371 A s u k).
Proof. exact (eq_refl (term554 A s u k)). Qed.
Lemma lem7118827 {A : Type'} (s : A -> Prop) (u : A -> real) : (term555 A s u) = (term379 A s u).
Proof. exact (fun_ext (fun k : A => @lem7118826 A s u k)). Qed.
Lemma lem7118828 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7118829 {A : Type'} (s : A -> Prop) (u : A -> real) : (term556 A s u) = (term380 A s u).
Proof. exact (MK_COMB (@lem7118828 A) (@lem7118827 A s u)). Qed.
Lemma lem7118830 {A : Type'} (u : A -> real) (j : A) : (term381 A u j) = (term381 A u j).
Proof. exact (eq_refl (term381 A u j)). Qed.
Lemma lem7118831 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term551 A j s u) = (term383 A j s u).
Proof. exact (MK_COMB (@lem7118830 A u j) (@lem7118829 A s u)). Qed.
Lemma lem7118832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7118833 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term557 A j s u) = (term558 A j s u).
Proof. exact (MK_COMB (@lem7118832) (@lem7118831 A j s u)). Qed.
Lemma lem7118834 {A : Type'} (s : A -> Prop) (u : A -> real) (k : A) : (term554 A s u k) = (term371 A s u k).
Proof. exact (eq_refl (term554 A s u k)). Qed.
Lemma lem7118835 {A : Type'} (u : A -> real) (j : A) : (term381 A u j) = (term381 A u j).
Proof. exact (eq_refl (term381 A u j)). Qed.
Lemma lem7118836 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) (k : A) : (term559 A j s u k) = (term560 A j s u k).
Proof. exact (MK_COMB (@lem7118835 A u j) (@lem7118834 A s u k)). Qed.
Lemma lem7118837 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term561 A j s u) = (term562 A j s u).
Proof. exact (fun_ext (fun k : A => @lem7118836 A j s u k)). Qed.
Lemma lem7118838 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7118839 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term552 A j s u) = (term563 A j s u).
Proof. exact (MK_COMB (@lem7118838 A) (@lem7118837 A j s u)). Qed.
Lemma lem7118840 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : ((term551 A j s u) = (term552 A j s u)) = ((term383 A j s u) = (term563 A j s u)).
Proof. exact (MK_COMB (@lem7118833 A j s u) (@lem7118839 A j s u)). Qed.
Lemma lem7118841 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term383 A j s u) = (term563 A j s u).
Proof. exact (EQ_MP (@lem7118840 A j s u) (@lem7118825 A j s u)). Qed.
Lemma lem7118842 {A : Type'} (j : A) (s : A -> Prop) : (term385 A j s) = (term385 A j s).
Proof. exact (eq_refl (term385 A j s)). Qed.
Lemma lem7118843 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term387 A j s u) = (term564 A j s u).
Proof. exact (MK_COMB (@lem7118842 A j s) (@lem7118841 A j s u)). Qed.
Lemma lem7118845 {A : Type'} (P : Prop) (Q : A -> Prop) : (term549 A P Q) = (term550 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7118846 {A : Type'} (P : Prop) (Q : A -> Prop) : (term549 A P Q) = (term550 A P Q).
Proof. exact (@lem7118845 A P Q). Qed.
Lemma lem7118847 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term565 A j s u) = (term566 A j s u).
Proof. exact (@lem7118846 A (term567 A j s) (term562 A j s u)). Qed.
Lemma lem7118848 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) (k : A) : (term568 A j s u k) = (term560 A j s u k).
Proof. exact (eq_refl (term568 A j s u k)). Qed.
Lemma lem7118849 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term569 A j s u) = (term562 A j s u).
Proof. exact (fun_ext (fun k : A => @lem7118848 A j s u k)). Qed.
Lemma lem7118850 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7118851 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term570 A j s u) = (term563 A j s u).
Proof. exact (MK_COMB (@lem7118850 A) (@lem7118849 A j s u)). Qed.
Lemma lem7118852 {A : Type'} (j : A) (s : A -> Prop) : (term385 A j s) = (term385 A j s).
Proof. exact (eq_refl (term385 A j s)). Qed.
Lemma lem7118853 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term565 A j s u) = (term564 A j s u).
Proof. exact (MK_COMB (@lem7118852 A j s) (@lem7118851 A j s u)). Qed.
Lemma lem7118854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7118855 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term571 A j s u) = (term572 A j s u).
Proof. exact (MK_COMB (@lem7118854) (@lem7118853 A j s u)). Qed.
Lemma lem7118856 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) (k : A) : (term568 A j s u k) = (term560 A j s u k).
Proof. exact (eq_refl (term568 A j s u k)). Qed.
Lemma lem7118857 {A : Type'} (j : A) (s : A -> Prop) : (term385 A j s) = (term385 A j s).
Proof. exact (eq_refl (term385 A j s)). Qed.
Lemma lem7118858 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) (k : A) : (term573 A j s u k) = (term574 A j s u k).
Proof. exact (MK_COMB (@lem7118857 A j s) (@lem7118856 A j s u k)). Qed.
Lemma lem7118859 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term575 A j s u) = (term576 A j s u).
Proof. exact (fun_ext (fun k : A => @lem7118858 A j s u k)). Qed.
Lemma lem7118860 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7118861 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term566 A j s u) = (term577 A j s u).
Proof. exact (MK_COMB (@lem7118860 A) (@lem7118859 A j s u)). Qed.
Lemma lem7118862 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : ((term565 A j s u) = (term566 A j s u)) = ((term564 A j s u) = (term577 A j s u)).
Proof. exact (MK_COMB (@lem7118855 A j s u) (@lem7118861 A j s u)). Qed.
Lemma lem7118863 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term564 A j s u) = (term577 A j s u).
Proof. exact (EQ_MP (@lem7118862 A j s u) (@lem7118847 A j s u)). Qed.
Lemma lem7118864 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term387 A j s u) = (term577 A j s u).
Proof. exact (TRANS (@lem7118843 A j s u) (@lem7118863 A j s u)). Qed.
Lemma lem7118865 {A : Type'} (s : A -> Prop) (u : A -> real) : (term394 A s u) = (term578 A s u).
Proof. exact (fun_ext (fun j : A => @lem7118864 A j s u)). Qed.
Lemma lem7118866 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7118867 {A : Type'} (s : A -> Prop) (u : A -> real) : (term395 A s u) = (term579 A s u).
Proof. exact (MK_COMB (@lem7118866 A) (@lem7118865 A s u)). Qed.
Lemma lem7118886 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) (k : A) : (term574 A j s u k) = (term574 A j s u k).
Proof. exact (eq_refl (term574 A j s u k)). Qed.
Lemma lem7118887 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term576 A j s u) = (term576 A j s u).
Proof. exact (fun_ext (fun k : A => @lem7118886 A j s u k)). Qed.
Lemma lem7118888 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7118889 {A : Type'} (j : A) (s : A -> Prop) (u : A -> real) : (term577 A j s u) = (term577 A j s u).
Proof. exact (MK_COMB (@lem7118888 A) (@lem7118887 A j s u)). Qed.
Lemma lem7118890 {A : Type'} (s : A -> Prop) (u : A -> real) : (term578 A s u) = (term578 A s u).
Proof. exact (fun_ext (fun j : A => @lem7118889 A j s u)). Qed.
Lemma lem7118891 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7118892 {A : Type'} (s : A -> Prop) (u : A -> real) : (term579 A s u) = (term579 A s u).
Proof. exact (MK_COMB (@lem7118891 A) (@lem7118890 A s u)). Qed.
Lemma lem7118893 {A : Type'} (s : A -> Prop) (u : A -> real) : (term395 A s u) = (term579 A s u).
Proof. exact (TRANS (@lem7118867 A s u) (@lem7118892 A s u)). Qed.
Lemma lem7118894 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term579 A s u.
Proof. exact (EQ_MP (@lem7118893 A s u) (@lem7118809 A i s u i' h1)). Qed.
Lemma lem7118918 (u : real) : (term498 u) = (term498 u).
Proof. exact (eq_refl (term498 u)). Qed.
Lemma lem7118919 : term530 = term530.
Proof. exact (fun_ext (fun u : real => @lem7118918 u)). Qed.
Lemma lem7118920 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118922 : term541 = term541.
Proof. exact (MK_COMB (@lem7118920) (@lem7118919)). Qed.
Lemma lem7118923 (h1 : term352) : term541.
Proof. exact (EQ_MP (@lem7118922) (@lem7118819 h1)). Qed.
Lemma lem7118944 (u : real) : (term488 u) = (term488 u).
Proof. exact (eq_refl (term488 u)). Qed.
Lemma lem7118945 : term509 = term509.
Proof. exact (fun_ext (fun u : real => @lem7118944 u)). Qed.
Lemma lem7118946 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7118948 : term520 = term520.
Proof. exact (MK_COMB (@lem7118946) (@lem7118945)). Qed.
Lemma lem7118949 (h1 : term352) : term520.
Proof. exact (EQ_MP (@lem7118948) (@lem7118821 h1)). Qed.
Lemma lem7118963 {A : Type'} (_95064 : A) (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term580 A s u _95064.
Proof. exact (@lem7118894 A i s u i' h1 _95064). Qed.
Lemma lem7118964 {A : Type'} (_95064 : A) (s : A -> Prop) (u : A -> real) : (term580 A s u _95064) = (term577 A _95064 s u).
Proof. exact (eq_refl (term580 A s u _95064)). Qed.
Lemma lem7118965 {A : Type'} (_95064 : A) (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term577 A _95064 s u.
Proof. exact (EQ_MP (@lem7118964 A _95064 s u) (@lem7118963 A _95064 i s u i' h1)). Qed.
Lemma lem7118966 {A : Type'} (_95064 : A) (_95065 : A) (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term581 A _95064 s u _95065.
Proof. exact (@lem7118965 A _95064 i s u i' h1 _95065). Qed.
Lemma lem7118967 {A : Type'} (_95064 : A) (s : A -> Prop) (u : A -> real) (_95065 : A) : (term581 A _95064 s u _95065) = (term574 A _95064 s u _95065).
Proof. exact (eq_refl (term581 A _95064 s u _95065)). Qed.
Lemma lem7118969 (_95066 : real) (h1 : term352) : term532 _95066.
Proof. exact (@lem7118923 h1 _95066). Qed.
Lemma lem7118970 (_95066 : real) : (term532 _95066) = (term498 _95066).
Proof. exact (eq_refl (term532 _95066)). Qed.
Lemma lem7118975 (_95068 : real) (h1 : term352) : term511 _95068.
Proof. exact (@lem7118949 h1 _95068). Qed.
Lemma lem7118976 (_95068 : real) : (term511 _95068) = (term488 _95068).
Proof. exact (eq_refl (term511 _95068)). Qed.
Lemma lem7118994 {A : Type'} (_95064 : A) (_95065 : A) (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term574 A _95064 s u _95065.
Proof. exact (EQ_MP (@lem7118967 A _95064 s u _95065) (@lem7118966 A _95064 _95065 i s u i' h1)). Qed.
Lemma lem7119002 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term582 A u i.
Proof. exact (proj2 (@lem7118811 A i s u i' h1)). Qed.
Lemma lem7119008 (_95066 : real) (h1 : term352) : term498 _95066.
Proof. exact (EQ_MP (@lem7118970 _95066) (@lem7118969 _95066 h1)). Qed.
Lemma lem7119020 (_95068 : real) (h1 : term352) : term488 _95068.
Proof. exact (EQ_MP (@lem7118976 _95068) (@lem7118975 _95068 h1)). Qed.
Lemma lem7119028 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : @IN A i s.
Proof. exact (proj1 (@lem7118811 A i s u i' h1)). Qed.
Lemma lem7119029 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term583 A i s.
Proof. exact (fun h0 : term567 A i s => @lem7119028 A i s u i' h1). Qed.
Lemma lem7119031 (p : Prop) : (term584 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7119032 {A : Type'} (i : A) (s : A -> Prop) : (term583 A i s) = (@IN A i s).
Proof. exact (@lem7119031 (@IN A i s)). Qed.
Lemma lem7119033 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : @IN A i s.
Proof. exact (EQ_MP (@lem7119032 A i s) (@lem7119029 A i s u i' h1)). Qed.
Lemma lem7119035 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : @IN A i' s.
Proof. exact (proj1 (@lem7118810 A i s u i' h1)). Qed.
Lemma lem7119036 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term583 A i' s.
Proof. exact (fun h0 : term567 A i' s => @lem7119035 A i s u i' h1). Qed.
Lemma lem7119038 (p : Prop) : (term584 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7119039 {A : Type'} (i' : A) (s : A -> Prop) : (term583 A i' s) = (@IN A i' s).
Proof. exact (@lem7119038 (@IN A i' s)). Qed.
Lemma lem7119040 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : @IN A i' s.
Proof. exact (EQ_MP (@lem7119039 A i' s) (@lem7119036 A i s u i' h1)). Qed.
Lemma lem7119042 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term585 A u i'.
Proof. exact (proj2 (@lem7118810 A i s u i' h1)). Qed.
Lemma lem7119043 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term586 A u i'.
Proof. exact (fun h0 : term410 A u i' => @lem7119042 A i s u i' h1). Qed.
Lemma lem7119045 (p : Prop) : (term587 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7119046 {A : Type'} (u : A -> real) (i' : A) : (term586 A u i') = (term585 A u i').
Proof. exact (@lem7119045 (term410 A u i')). Qed.
Lemma lem7119047 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term585 A u i'.
Proof. exact (EQ_MP (@lem7119046 A u i') (@lem7119043 A i s u i' h1)). Qed.
Lemma lem7119053 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7119054 (_95068 : real) : (term488 _95068) = (term588 _95068).
Proof. exact (@lem7119053 (term70 _95068) (term196 _95068)). Qed.
Lemma lem7119060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7119061 (_95068 : real) : (term589 _95068) = (term590 _95068).
Proof. exact (MK_COMB (@lem7119060) (@lem7119054 _95068)). Qed.
Lemma lem7119067 (_95068 : real) : (term588 _95068) = (term588 _95068).
Proof. exact (eq_refl (term588 _95068)). Qed.
Lemma lem7119068 (_95068 : real) : ((term488 _95068) = (term588 _95068)) = ((term588 _95068) = (term588 _95068)).
Proof. exact (MK_COMB (@lem7119061 _95068) (@lem7119067 _95068)). Qed.
Lemma lem7119070 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7119071 (x : Prop) : (x = x) = True.
Proof. exact (@lem7119070 Prop x). Qed.
Lemma lem7119072 (_95068 : real) : ((term588 _95068) = (term588 _95068)) = True.
Proof. exact (@lem7119071 (term588 _95068)). Qed.
Lemma lem7119073 (_95068 : real) : ((term488 _95068) = (term588 _95068)) = True.
Proof. exact (TRANS (@lem7119068 _95068) (@lem7119072 _95068)). Qed.
Lemma lem7119074 (_95068 : real) : True = ((term488 _95068) = (term588 _95068)).
Proof. exact (SYM (@lem7119073 _95068)). Qed.
Lemma lem7119075 (_95068 : real) : (term488 _95068) = (term588 _95068).
Proof. exact (EQ_MP (@lem7119074 _95068) (@lem0)). Qed.
Lemma lem7119076 (_95068 : real) (h1 : term352) : term588 _95068.
Proof. exact (EQ_MP (@lem7119075 _95068) (@lem7119020 _95068 h1)). Qed.
Lemma lem7119078 (b : Prop) (a : Prop) : (a \/ b) = (term591 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7119081 (_95068 : real) : (term588 _95068) = (term592 _95068).
Proof. exact (@lem7119078 (term196 _95068) (term70 _95068)). Qed.
Lemma lem7119084 (_95068 : real) (h1 : term352) : term592 _95068.
Proof. exact (EQ_MP (@lem7119081 _95068) (@lem7119076 _95068 h1)). Qed.
Lemma lem7119085 {A : Type'} (u : A -> real) (i' : A) (h1 : term352) : term593 A u i'.
Proof. exact (@lem7119084 (u i') h1). Qed.
Lemma lem7119088 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : term372 A u i'.
Proof. exact (@lem7119085 A u i' h2 (@lem7119047 A i s u i' h1)). Qed.
Lemma lem7119089 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : term594 A u i'.
Proof. exact (fun h0 : term595 A u i' => @lem7119088 A i s u i' h1 h2). Qed.
Lemma lem7119091 (p : Prop) : (term584 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7119092 {A : Type'} (u : A -> real) (i' : A) : (term594 A u i') = (term372 A u i').
Proof. exact (@lem7119091 (term372 A u i')). Qed.
Lemma lem7119093 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : term372 A u i'.
Proof. exact (EQ_MP (@lem7119092 A u i') (@lem7119089 A i s u i' h1 h2)). Qed.
Lemma lem7119109 (q : Prop) (p : Prop) (r : Prop) : (term596 p q r) = (term596 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7119110 {A : Type'} (s : A -> Prop) (_95064 : A) (u : A -> real) (_95065 : A) : (term560 A _95064 s u _95065) = (term597 A s _95064 u _95065).
Proof. exact (@lem7119109 (term567 A _95065 s) (term553 A u _95064) (term595 A u _95065)). Qed.
Lemma lem7119124 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7119125 {A : Type'} (_95065 : A) (u : A -> real) (_95064 : A) : (term598 A _95064 u _95065) = (term599 A _95065 u _95064).
Proof. exact (@lem7119124 (term595 A u _95065) (term553 A u _95064)). Qed.
Lemma lem7119131 {A : Type'} (_95065 : A) (s : A -> Prop) : (term385 A _95065 s) = (term385 A _95065 s).
Proof. exact (eq_refl (term385 A _95065 s)). Qed.
Lemma lem7119132 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : (term597 A s _95064 u _95065) = (term600 A s _95065 u _95064).
Proof. exact (MK_COMB (@lem7119131 A _95065 s) (@lem7119125 A _95065 u _95064)). Qed.
Lemma lem7119143 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : (term560 A _95064 s u _95065) = (term600 A s _95065 u _95064).
Proof. exact (TRANS (@lem7119110 A s _95064 u _95065) (@lem7119132 A s _95065 u _95064)). Qed.
Lemma lem7119144 {A : Type'} (_95064 : A) (s : A -> Prop) : (term385 A _95064 s) = (term385 A _95064 s).
Proof. exact (eq_refl (term385 A _95064 s)). Qed.
Lemma lem7119145 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : (term574 A _95064 s u _95065) = (term601 A s _95065 u _95064).
Proof. exact (MK_COMB (@lem7119144 A _95064 s) (@lem7119143 A s _95065 u _95064)). Qed.
Lemma lem7119156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7119157 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : (term602 A _95064 s u _95065) = (term603 A s _95065 u _95064).
Proof. exact (MK_COMB (@lem7119156) (@lem7119145 A s _95065 u _95064)). Qed.
Lemma lem7119161 (q : Prop) (p : Prop) (r : Prop) : (term596 p q r) = (term596 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7119162 {A : Type'} (_95064 : A) (s : A -> Prop) (u : A -> real) (_95065 : A) : (term604 A _95064 s u _95065) = (term574 A _95064 s u _95065).
Proof. exact (@lem7119161 (term567 A _95064 s) (term553 A u _95064) (term371 A s u _95065)). Qed.
Lemma lem7119176 (q : Prop) (p : Prop) (r : Prop) : (term596 p q r) = (term596 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7119177 {A : Type'} (s : A -> Prop) (_95064 : A) (u : A -> real) (_95065 : A) : (term560 A _95064 s u _95065) = (term597 A s _95064 u _95065).
Proof. exact (@lem7119176 (term567 A _95065 s) (term553 A u _95064) (term595 A u _95065)). Qed.
Lemma lem7119191 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7119192 {A : Type'} (_95065 : A) (u : A -> real) (_95064 : A) : (term598 A _95064 u _95065) = (term599 A _95065 u _95064).
Proof. exact (@lem7119191 (term595 A u _95065) (term553 A u _95064)). Qed.
Lemma lem7119198 {A : Type'} (_95065 : A) (s : A -> Prop) : (term385 A _95065 s) = (term385 A _95065 s).
Proof. exact (eq_refl (term385 A _95065 s)). Qed.
Lemma lem7119199 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : (term597 A s _95064 u _95065) = (term600 A s _95065 u _95064).
Proof. exact (MK_COMB (@lem7119198 A _95065 s) (@lem7119192 A _95065 u _95064)). Qed.
Lemma lem7119210 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : (term560 A _95064 s u _95065) = (term600 A s _95065 u _95064).
Proof. exact (TRANS (@lem7119177 A s _95064 u _95065) (@lem7119199 A s _95065 u _95064)). Qed.
Lemma lem7119211 {A : Type'} (_95064 : A) (s : A -> Prop) : (term385 A _95064 s) = (term385 A _95064 s).
Proof. exact (eq_refl (term385 A _95064 s)). Qed.
Lemma lem7119212 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : (term574 A _95064 s u _95065) = (term601 A s _95065 u _95064).
Proof. exact (MK_COMB (@lem7119211 A _95064 s) (@lem7119210 A s _95065 u _95064)). Qed.
Lemma lem7119223 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : (term604 A _95064 s u _95065) = (term601 A s _95065 u _95064).
Proof. exact (TRANS (@lem7119162 A _95064 s u _95065) (@lem7119212 A s _95065 u _95064)). Qed.
Lemma lem7119224 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : ((term574 A _95064 s u _95065) = (term604 A _95064 s u _95065)) = ((term601 A s _95065 u _95064) = (term601 A s _95065 u _95064)).
Proof. exact (MK_COMB (@lem7119157 A s _95065 u _95064) (@lem7119223 A s _95065 u _95064)). Qed.
Lemma lem7119226 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7119227 (x : Prop) : (x = x) = True.
Proof. exact (@lem7119226 Prop x). Qed.
Lemma lem7119228 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : ((term601 A s _95065 u _95064) = (term601 A s _95065 u _95064)) = True.
Proof. exact (@lem7119227 (term601 A s _95065 u _95064)). Qed.
Lemma lem7119229 {A : Type'} (_95064 : A) (s : A -> Prop) (u : A -> real) (_95065 : A) : ((term574 A _95064 s u _95065) = (term604 A _95064 s u _95065)) = True.
Proof. exact (TRANS (@lem7119224 A s _95065 u _95064) (@lem7119228 A s _95065 u _95064)). Qed.
Lemma lem7119230 {A : Type'} (_95064 : A) (s : A -> Prop) (u : A -> real) (_95065 : A) : True = ((term574 A _95064 s u _95065) = (term604 A _95064 s u _95065)).
Proof. exact (SYM (@lem7119229 A _95064 s u _95065)). Qed.
Lemma lem7119231 {A : Type'} (_95064 : A) (s : A -> Prop) (u : A -> real) (_95065 : A) : (term574 A _95064 s u _95065) = (term604 A _95064 s u _95065).
Proof. exact (EQ_MP (@lem7119230 A _95064 s u _95065) (@lem0)). Qed.
Lemma lem7119232 {A : Type'} (_95064 : A) (_95065 : A) (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term604 A _95064 s u _95065.
Proof. exact (EQ_MP (@lem7119231 A _95064 s u _95065) (@lem7118994 A _95064 _95065 i s u i' h1)). Qed.
Lemma lem7119234 (b : Prop) (a : Prop) : (a \/ b) = (term591 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7119235 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : (term604 A _95064 s u _95065) = (term605 A s _95065 u _95064).
Proof. exact (@lem7119234 (term606 A _95064 s u _95065) (term553 A u _95064)). Qed.
Lemma lem7119237 (a : Prop) (b : Prop) : (term607 a b) = (term608 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7119238 {A : Type'} (_95064 : A) (s : A -> Prop) (u : A -> real) (_95065 : A) : (term609 A _95064 s u _95065) = (term610 A _95064 s u _95065).
Proof. exact (@lem7119237 (term567 A _95064 s) (term371 A s u _95065)). Qed.
Lemma lem7119240 (a : Prop) : (term611 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7119241 {A : Type'} (_95064 : A) (s : A -> Prop) : (term612 A _95064 s) = (@IN A _95064 s).
Proof. exact (@lem7119240 (@IN A _95064 s)). Qed.
Lemma lem7119242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7119243 {A : Type'} (_95064 : A) (s : A -> Prop) : (term613 A _95064 s) = (term286 A _95064 s).
Proof. exact (MK_COMB (@lem7119242) (@lem7119241 A _95064 s)). Qed.
Lemma lem7119245 (a : Prop) (b : Prop) : (term607 a b) = (term608 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7119246 {A : Type'} (s : A -> Prop) (u : A -> real) (_95065 : A) : (term614 A s u _95065) = (term615 A s u _95065).
Proof. exact (@lem7119245 (term567 A _95065 s) (term595 A u _95065)). Qed.
Lemma lem7119248 (a : Prop) : (term611 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7119249 {A : Type'} (_95065 : A) (s : A -> Prop) : (term612 A _95065 s) = (@IN A _95065 s).
Proof. exact (@lem7119248 (@IN A _95065 s)). Qed.
Lemma lem7119250 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7119251 {A : Type'} (_95065 : A) (s : A -> Prop) : (term613 A _95065 s) = (term286 A _95065 s).
Proof. exact (MK_COMB (@lem7119250) (@lem7119249 A _95065 s)). Qed.
Lemma lem7119253 (a : Prop) : (term611 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7119254 {A : Type'} (u : A -> real) (_95065 : A) : (term616 A u _95065) = (term372 A u _95065).
Proof. exact (@lem7119253 (term372 A u _95065)). Qed.
Lemma lem7119255 {A : Type'} (s : A -> Prop) (u : A -> real) (_95065 : A) : (term615 A s u _95065) = (term303 A s u _95065).
Proof. exact (MK_COMB (@lem7119251 A _95065 s) (@lem7119254 A u _95065)). Qed.
Lemma lem7119256 {A : Type'} (s : A -> Prop) (u : A -> real) (_95065 : A) : (term614 A s u _95065) = (term303 A s u _95065).
Proof. exact (TRANS (@lem7119246 A s u _95065) (@lem7119255 A s u _95065)). Qed.
Lemma lem7119257 {A : Type'} (_95064 : A) (s : A -> Prop) (u : A -> real) (_95065 : A) : (term610 A _95064 s u _95065) = (term617 A _95064 s u _95065).
Proof. exact (MK_COMB (@lem7119243 A _95064 s) (@lem7119256 A s u _95065)). Qed.
Lemma lem7119258 {A : Type'} (_95064 : A) (s : A -> Prop) (u : A -> real) (_95065 : A) : (term609 A _95064 s u _95065) = (term617 A _95064 s u _95065).
Proof. exact (TRANS (@lem7119238 A _95064 s u _95065) (@lem7119257 A _95064 s u _95065)). Qed.
Lemma lem7119259 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7119260 {A : Type'} (_95064 : A) (s : A -> Prop) (u : A -> real) (_95065 : A) : (term618 A _95064 s u _95065) = (term619 A _95064 s u _95065).
Proof. exact (MK_COMB (@lem7119259) (@lem7119258 A _95064 s u _95065)). Qed.
Lemma lem7119261 {A : Type'} (u : A -> real) (_95064 : A) : (term553 A u _95064) = (term553 A u _95064).
Proof. exact (eq_refl (term553 A u _95064)). Qed.
Lemma lem7119262 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : (term605 A s _95065 u _95064) = (term620 A s _95065 u _95064).
Proof. exact (MK_COMB (@lem7119260 A _95064 s u _95065) (@lem7119261 A u _95064)). Qed.
Lemma lem7119263 {A : Type'} (s : A -> Prop) (_95065 : A) (u : A -> real) (_95064 : A) : (term604 A _95064 s u _95065) = (term620 A s _95065 u _95064).
Proof. exact (TRANS (@lem7119235 A s _95065 u _95064) (@lem7119262 A s _95065 u _95064)). Qed.
Lemma lem7119265 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : term303 A s u i'.
Proof. exact (conj (@lem7119040 A i s u i' h1) (@lem7119093 A i s u i' h1 h2)). Qed.
Lemma lem7119266 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : term617 A i s u i'.
Proof. exact (conj (@lem7119033 A i s u i' h1) (@lem7119265 A i s u i' h1 h2)). Qed.
Lemma lem7119268 {A : Type'} (_95065 : A) (_95064 : A) (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term620 A s _95065 u _95064.
Proof. exact (EQ_MP (@lem7119263 A s _95065 u _95064) (@lem7119232 A _95064 _95065 i s u i' h1)). Qed.
Lemma lem7119269 {A : Type'} (_95065 : A) (_95064 : A) (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term620 A s _95065 u _95064.
Proof. exact (@lem7119268 A _95065 _95064 i s u i' h1). Qed.
Lemma lem7119270 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term620 A s i' u i.
Proof. exact (@lem7119269 A i' i i s u i' h1). Qed.
Lemma lem7119273 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : term553 A u i.
Proof. exact (@lem7119270 A i s u i' h1 (@lem7119266 A i s u i' h1 h2)). Qed.
Lemma lem7119274 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : term621 A u i.
Proof. exact (fun h0 : term300 A u i => @lem7119273 A i s u i' h1 h2). Qed.
Lemma lem7119276 (p : Prop) : (term587 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7119277 {A : Type'} (u : A -> real) (i : A) : (term621 A u i) = (term553 A u i).
Proof. exact (@lem7119276 (term300 A u i)). Qed.
Lemma lem7119278 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : term553 A u i.
Proof. exact (EQ_MP (@lem7119277 A u i) (@lem7119274 A i s u i' h1 h2)). Qed.
Lemma lem7119280 (b : Prop) (a : Prop) : (a \/ b) = (term591 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7119283 (_95066 : real) : (term498 _95066) = (term622 _95066).
Proof. exact (@lem7119280 (term199 _95066) (term209 _95066)). Qed.
Lemma lem7119286 (_95066 : real) (h1 : term352) : term622 _95066.
Proof. exact (EQ_MP (@lem7119283 _95066) (@lem7119008 _95066 h1)). Qed.
Lemma lem7119287 {A : Type'} (u : A -> real) (i : A) (h1 : term352) : term623 A u i.
Proof. exact (@lem7119286 (u i) h1). Qed.
Lemma lem7119290 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : term398 A u i.
Proof. exact (@lem7119287 A u i h2 (@lem7119278 A i s u i' h1 h2)). Qed.
Lemma lem7119291 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : term624 A u i.
Proof. exact (fun h0 : term582 A u i => @lem7119290 A i s u i' h1 h2). Qed.
Lemma lem7119293 (p : Prop) : (term584 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7119294 {A : Type'} (u : A -> real) (i : A) : (term624 A u i) = (term398 A u i).
Proof. exact (@lem7119293 (term398 A u i)). Qed.
Lemma lem7119295 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : term398 A u i.
Proof. exact (EQ_MP (@lem7119294 A u i) (@lem7119291 A i s u i' h1 h2)). Qed.
Lemma lem7119298 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7119300 {A : Type'} (u : A -> real) (i : A) : (term582 A u i) = (term625 A u i).
Proof. exact (@lem7119298 (term398 A u i)). Qed.
Lemma lem7119303 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') : term625 A u i.
Proof. exact (EQ_MP (@lem7119300 A u i) (@lem7119002 A i s u i' h1)). Qed.
Lemma lem7119306 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : False.
Proof. exact (@lem7119303 A i s u i' h1 (@lem7119295 A i s u i' h1 h2)). Qed.
Lemma lem7119307 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : term626.
Proof. exact (fun h0 : ~ False => @lem7119306 A i s u i' h1 h2). Qed.
Lemma lem7119309 (p : Prop) : (term584 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7119310 : term626 = False.
Proof. exact (@lem7119309 False). Qed.
Lemma lem7119311 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : False.
Proof. exact (EQ_MP (@lem7119310) (@lem7119307 A i s u i' h1 h2)). Qed.
Lemma lem7119312 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : (term479 A i s u i') = False.
Proof. exact (prop_ext (fun h3 : term479 A i s u i' => @lem7119311 A i s u i' h1 h2) (fun h3 : False => @lem7118807 A i s u i' h1)). Qed.
Lemma lem7119313 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (i' : A) (h1 : term479 A i s u i') (h2 : term352) : False.
Proof. exact (EQ_MP (@lem7119312 A i s u i' h1 h2) (@lem7118807 A i s u i' h1)). Qed.
Lemma lem7119314 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (h1 : term482 A i s u) (h2 : term352) : False.
Proof. exact (ex_elim (@lem7118582 A i s u h1) (fun i' : A => fun h0 : term481 A i s u i' => @lem7119313 A i s u i' h0 h2)). Qed.
Lemma lem7119315 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term322 A s u) (h2 : term352) : False.
Proof. exact (ex_elim (@lem7118285 A s u h1) (fun i : A => fun h0 : term483 A s u i => @lem7119314 A i s u h0 h2)). Qed.
Lemma lem7119316 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term322 A s u) : term627.
Proof. exact (fun h0 : term352 => @lem7119315 A s u h1 h0). Qed.
Lemma lem7119317 : term627 = term353.
Proof. exact (@lem69 term352). Qed.
Lemma lem7119318 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term322 A s u) : term353.
Proof. exact (EQ_MP (@lem7119317) (@lem7119316 A s u h1)). Qed.
Lemma lem7119319 {A : Type'} (s : A -> Prop) (u : A -> real) : term354 A s u.
Proof. exact (fun h0 : term322 A s u => @lem7119318 A s u h0). Qed.
Lemma lem7119324 {A : Type'} (u : A -> real) : term358 A u.
Proof. exact (fun s : A -> Prop => @lem7119319 A s u). Qed.
Lemma lem7119329 {A : Type'} : term362 A.
Proof. exact (fun u : A -> real => @lem7119324 A u). Qed.
Lemma lem7119330 {A : Type'} : term361 A.
Proof. exact (EQ_MP (@lem7117909 A) (@lem7119329 A)). Qed.
Lemma lem7119331 {A : Type'} (u : A -> real) : term628 A u.
Proof. exact (@lem7119330 A u). Qed.
Lemma lem7119332 {A : Type'} (u : A -> real) : (term628 A u) = (term357 A u).
Proof. exact (eq_refl (term628 A u)). Qed.
Lemma lem7119333 {A : Type'} (u : A -> real) : term357 A u.
Proof. exact (EQ_MP (@lem7119332 A u) (@lem7119331 A u)). Qed.
Lemma lem7119334 {A : Type'} (u : A -> real) (s : A -> Prop) : term629 A u s.
Proof. exact (@lem7119333 A u s). Qed.
Lemma lem7119335 {A : Type'} (s : A -> Prop) (u : A -> real) : (term629 A u s) = (term275 A s u).
Proof. exact (eq_refl (term629 A u s)). Qed.
Lemma lem7119336 {A : Type'} (s : A -> Prop) (u : A -> real) : term275 A s u.
Proof. exact (EQ_MP (@lem7119335 A s u) (@lem7119334 A u s)). Qed.
Lemma lem7119338 {A : Type'} (s : A -> Prop) (u : A -> real) : term275 A s u.
Proof. exact (@lem7117508 A s u (@lem7119336 A s u)). Qed.
Lemma lem7119339 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term274 A s u) : term325.
Proof. exact (@lem7119338 A s u (@lem7117492 A s u h1)). Qed.
Lemma lem7119340 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term274 A s u) : False.
Proof. exact (@lem7119339 A s u h1 (@lem7117487)). Qed.
Lemma lem7119341 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term274 A s u) : (term274 A s u) = False.
Proof. exact (prop_ext (fun h2 : term274 A s u => @lem7119340 A s u h1) (fun h2 : False => @lem7117492 A s u h1)). Qed.
Lemma lem7119342 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term274 A s u) : False.
Proof. exact (EQ_MP (@lem7119341 A s u h1) (@lem7117492 A s u h1)). Qed.
Lemma lem7119343 {A : Type'} (s : A -> Prop) (u : A -> real) : term273 A s u.
Proof. exact (fun h0 : term274 A s u => @lem7119342 A s u h0). Qed.
Lemma lem7119344 {A : Type'} (s : A -> Prop) (u : A -> real) : term272 A s u.
Proof. exact (EQ_MP (@lem7117491 A s u) (@lem7119343 A s u)). Qed.
Lemma lem7119345 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term316 A s u) : term316 A s u.
Proof. exact (h1). Qed.
Lemma lem7119346 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term320 A s u) : term320 A s u.
Proof. exact (h1). Qed.
Lemma lem7119347 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term630 A s u) : term630 A s u.
Proof. exact (h1). Qed.
Lemma lem7119348 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : (@sum A s u) = term15) : (@sum A s u) = term15.
Proof. exact (h1). Qed.
Lemma lem7119349 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7119350 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) : term368 A s u.
Proof. exact (h1). Qed.
Lemma lem7119351 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) : term365 A s u.
Proof. exact (h1). Qed.
Lemma lem7119354 {A : Type'} (s : A -> Prop) (u : A -> real) : (term316 A s u) = ((term316 A s u) = True).
Proof. exact (@lem7 (term316 A s u)). Qed.
Lemma lem7119367 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term316 A s u) : (term316 A s u) = True.
Proof. exact (EQ_MP (@lem7119354 A s u) (@lem7119345 A s u h1)). Qed.
Lemma lem7119368 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term316 A s u) : (term316 A s u) = True.
Proof. exact (@lem7119367 A s u h1). Qed.
Lemma lem7119369 {A : Type'} (s : A -> Prop) (u : A -> real) : (term631 A s u) = (term631 A s u).
Proof. exact (eq_refl (term631 A s u)). Qed.
Lemma lem7119370 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term316 A s u) : (term632 A s u) = (term633 A s u).
Proof. exact (MK_COMB (@lem7119369 A s u) (@lem7119368 A s u h1)). Qed.
Lemma lem7119372 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7119373 {A : Type'} (s : A -> Prop) (u : A -> real) : (term633 A s u) = True.
Proof. exact (@lem7119372 (term6 A s u)). Qed.
Lemma lem7119374 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term316 A s u) : (term632 A s u) = True.
Proof. exact (TRANS (@lem7119370 A s u h1) (@lem7119373 A s u)). Qed.
Lemma lem7119375 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term316 A s u) : True = (term632 A s u).
Proof. exact (SYM (@lem7119374 A s u h1)). Qed.
Lemma lem7119376 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term316 A s u) : term632 A s u.
Proof. exact (EQ_MP (@lem7119375 A s u h1) (@lem0)). Qed.
Lemma lem7119450 (x : real) : (x = term15) = ((real_neg x) = term15).
Proof. exact (@lem7115677 x (@lem7115676 x)). Qed.
Lemma lem7119451 {A : Type'} (u : A -> real) (i : A) : ((u i) = term15) = ((term634 A u i) = term15).
Proof. exact (@lem7119450 (u i)). Qed.
Lemma lem7119452 {A : Type'} (i : A) (s : A -> Prop) : (term635 A i s) = (term635 A i s).
Proof. exact (eq_refl (term635 A i s)). Qed.
Lemma lem7119453 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term636 A s u i) = (term637 A s u i).
Proof. exact (MK_COMB (@lem7119452 A i s) (@lem7119451 A u i)). Qed.
Lemma lem7119454 {A : Type'} (s : A -> Prop) (u : A -> real) : (term638 A s u) = (term639 A s u).
Proof. exact (fun_ext (fun i : A => @lem7119453 A s u i)). Qed.
Lemma lem7119455 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7119456 {A : Type'} (s : A -> Prop) (u : A -> real) : (term6 A s u) = (term640 A s u).
Proof. exact (MK_COMB (@lem7119455 A) (@lem7119454 A s u)). Qed.
Lemma lem7119457 {A : Type'} (s : A -> Prop) (u : A -> real) : (term640 A s u) = (term6 A s u).
Proof. exact (SYM (@lem7119456 A s u)). Qed.
Lemma lem7119459 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : term4 _132718 s f.
Proof. exact (EQ_MP (@lem7114189 _132718 s f) (@lem7114188 _132718 s f)). Qed.
Lemma lem7119460 {A : Type'} (s : A -> Prop) (f : A -> real) : term4 A s f.
Proof. exact (@lem7119459 A s f). Qed.
Lemma lem7119461 {A : Type'} (s : A -> Prop) (u : A -> real) : term4 A s u.
Proof. exact (@lem7119460 A s u). Qed.
Lemma lem7119463 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : term4 _132718 s f.
Proof. exact (EQ_MP (@lem7114189 _132718 s f) (@lem7114188 _132718 s f)). Qed.
Lemma lem7119464 {A : Type'} (s : A -> Prop) (f : A -> real) : term4 A s f.
Proof. exact (@lem7119463 A s f). Qed.
Lemma lem7119465 {A : Type'} (s : A -> Prop) (u : A -> real) : term641 A s u.
Proof. exact (@lem7119464 A s (term642 A u)). Qed.
Lemma lem7119466 {A : Type'} (u : A -> real) (i : A) : (term643 A u i) = (term634 A u i).
Proof. exact (eq_refl (term643 A u i)). Qed.
Lemma lem7119467 : term644 = term644.
Proof. exact (eq_refl term644). Qed.
Lemma lem7119468 {A : Type'} (u : A -> real) (i : A) : (term645 A u i) = (term410 A u i).
Proof. exact (MK_COMB (@lem7119467) (@lem7119466 A u i)). Qed.
Lemma lem7119469 {A : Type'} (i : A) (s : A -> Prop) : (term635 A i s) = (term635 A i s).
Proof. exact (eq_refl (term635 A i s)). Qed.
Lemma lem7119470 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term646 A s u i) = (term363 A s u i).
Proof. exact (MK_COMB (@lem7119469 A i s) (@lem7119468 A u i)). Qed.
Lemma lem7119471 {A : Type'} (s : A -> Prop) (u : A -> real) : (term647 A s u) = (term364 A s u).
Proof. exact (fun_ext (fun i : A => @lem7119470 A s u i)). Qed.
Lemma lem7119472 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7119473 {A : Type'} (s : A -> Prop) (u : A -> real) : (term648 A s u) = (term365 A s u).
Proof. exact (MK_COMB (@lem7119472 A) (@lem7119471 A s u)). Qed.
Lemma lem7119474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7119475 {A : Type'} (s : A -> Prop) (u : A -> real) : (term649 A s u) = (term650 A s u).
Proof. exact (MK_COMB (@lem7119474) (@lem7119473 A s u)). Qed.
Lemma lem7119476 {A : Type'} (s : A -> Prop) (u : A -> real) : ((term651 A s u) = term15) = ((term651 A s u) = term15).
Proof. exact (eq_refl ((term651 A s u) = term15)). Qed.
Lemma lem7119477 {A : Type'} (s : A -> Prop) (u : A -> real) : (term652 A s u) = (term653 A s u).
Proof. exact (MK_COMB (@lem7119475 A s u) (@lem7119476 A s u)). Qed.
Lemma lem7119478 {A : Type'} (s : A -> Prop) : (term654 A s) = (term654 A s).
Proof. exact (eq_refl (term654 A s)). Qed.
Lemma lem7119479 {A : Type'} (s : A -> Prop) (u : A -> real) : (term655 A s u) = (term656 A s u).
Proof. exact (MK_COMB (@lem7119478 A s) (@lem7119477 A s u)). Qed.
Lemma lem7119480 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7119481 {A : Type'} (s : A -> Prop) (u : A -> real) : (term657 A s u) = (term658 A s u).
Proof. exact (MK_COMB (@lem7119480) (@lem7119479 A s u)). Qed.
Lemma lem7119482 {A : Type'} (u : A -> real) (i : A) : (term643 A u i) = (term634 A u i).
Proof. exact (eq_refl (term643 A u i)). Qed.
Lemma lem7119483 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7119484 {A : Type'} (u : A -> real) (i : A) : (term659 A u i) = (term660 A u i).
Proof. exact (MK_COMB (@lem7119483) (@lem7119482 A u i)). Qed.
Lemma lem7119485 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7119486 {A : Type'} (u : A -> real) (i : A) : ((term643 A u i) = term15) = ((term634 A u i) = term15).
Proof. exact (MK_COMB (@lem7119484 A u i) (@lem7119485)). Qed.
Lemma lem7119487 {A : Type'} (i : A) (s : A -> Prop) : (term635 A i s) = (term635 A i s).
Proof. exact (eq_refl (term635 A i s)). Qed.
Lemma lem7119488 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term661 A s u i) = (term637 A s u i).
Proof. exact (MK_COMB (@lem7119487 A i s) (@lem7119486 A u i)). Qed.
Lemma lem7119489 {A : Type'} (s : A -> Prop) (u : A -> real) : (term662 A s u) = (term639 A s u).
Proof. exact (fun_ext (fun i : A => @lem7119488 A s u i)). Qed.
Lemma lem7119490 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7119491 {A : Type'} (s : A -> Prop) (u : A -> real) : (term663 A s u) = (term640 A s u).
Proof. exact (MK_COMB (@lem7119490 A) (@lem7119489 A s u)). Qed.
Lemma lem7119492 {A : Type'} (s : A -> Prop) (u : A -> real) : (term641 A s u) = (term664 A s u).
Proof. exact (MK_COMB (@lem7119481 A s u) (@lem7119491 A s u)). Qed.
Lemma lem7119493 {A : Type'} (s : A -> Prop) (u : A -> real) : term664 A s u.
Proof. exact (EQ_MP (@lem7119492 A s u) (@lem7119465 A s u)). Qed.
Lemma lem7119500 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7119502 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) : term403 A s u i.
Proof. exact (@lem7119350 A s u h1 i). Qed.
Lemma lem7119503 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term403 A s u i) = (term366 A s u i).
Proof. exact (eq_refl (term403 A s u i)). Qed.
Lemma lem7119504 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) : term366 A s u i.
Proof. exact (EQ_MP (@lem7119503 A s u i) (@lem7119502 A i s u h1)). Qed.
Lemma lem7119505 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term366 A s u i) = ((term366 A s u i) = True).
Proof. exact (@lem7 (term366 A s u i)). Qed.
Lemma lem7119510 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7119500 A s) (@lem7119349 A s h1)). Qed.
Lemma lem7119511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7119512 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term654 A s) = (and True).
Proof. exact (MK_COMB (@lem7119511) (@lem7119510 A s h1)). Qed.
Lemma lem7119520 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) : (term366 A s u i) = True.
Proof. exact (EQ_MP (@lem7119505 A s u i) (@lem7119504 A i s u h1)). Qed.
Lemma lem7119521 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) : (term366 A s u i) = True.
Proof. exact (@lem7119520 A i s u h1). Qed.
Lemma lem7119522 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) : (term367 A s u) = (term665 A).
Proof. exact (fun_ext (fun i : A => @lem7119521 A i s u h1)). Qed.
Lemma lem7119523 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7119524 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) : (term368 A s u) = (term666 A).
Proof. exact (MK_COMB (@lem7119523 A) (@lem7119522 A s u h1)). Qed.
Lemma lem7119526 {A : Type'} (t : Prop) : (term667 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7119527 {A : Type'} (t : Prop) : (term667 A t) = t.
Proof. exact (@lem7119526 A t). Qed.
Lemma lem7119528 {A : Type'} : (term666 A) = True.
Proof. exact (@lem7119527 A True). Qed.
Lemma lem7119529 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) : (term368 A s u) = True.
Proof. exact (TRANS (@lem7119524 A s u h1) (@lem7119528 A)). Qed.
Lemma lem7119530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7119531 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) : (term668 A s u) = (and True).
Proof. exact (MK_COMB (@lem7119530) (@lem7119529 A s u h1)). Qed.
Lemma lem7119535 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : (@sum A s u) = term15) : (@sum A s u) = term15.
Proof. exact (h1). Qed.
Lemma lem7119536 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7119537 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : (@sum A s u) = term15) : (term669 A s u) = term670.
Proof. exact (MK_COMB (@lem7119536) (@lem7119535 A s u h1)). Qed.
Lemma lem7119538 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7119539 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : (@sum A s u) = term15) : ((@sum A s u) = term15) = (term15 = term15).
Proof. exact (MK_COMB (@lem7119537 A s u h1) (@lem7119538)). Qed.
Lemma lem7119541 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7119542 (x : real) : (x = x) = True.
Proof. exact (@lem7119541 real x). Qed.
Lemma lem7119543 : (term15 = term15) = True.
Proof. exact (@lem7119542 term15). Qed.
Lemma lem7119544 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : (@sum A s u) = term15) : ((@sum A s u) = term15) = True.
Proof. exact (TRANS (@lem7119539 A s u h1) (@lem7119543)). Qed.
Lemma lem7119545 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) (h2 : (@sum A s u) = term15) : (term671 A s u) = (True /\ True).
Proof. exact (MK_COMB (@lem7119531 A s u h1) (@lem7119544 A s u h2)). Qed.
Lemma lem7119547 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7119548 : (True /\ True) = True.
Proof. exact (@lem7119547 True). Qed.
Lemma lem7119549 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) (h2 : (@sum A s u) = term15) : (term671 A s u) = True.
Proof. exact (TRANS (@lem7119545 A s u h1 h2) (@lem7119548)). Qed.
Lemma lem7119550 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : (term5 A s u) = (True /\ True).
Proof. exact (MK_COMB (@lem7119512 A s h2) (@lem7119549 A s u h1 h3)). Qed.
Lemma lem7119552 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7119553 : (True /\ True) = True.
Proof. exact (@lem7119552 True). Qed.
Lemma lem7119554 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : (term5 A s u) = True.
Proof. exact (TRANS (@lem7119550 A s u h1 h2 h3) (@lem7119553)). Qed.
Lemma lem7119555 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : True = (term5 A s u).
Proof. exact (SYM (@lem7119554 A s u h1 h2 h3)). Qed.
Lemma lem7119556 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : term5 A s u.
Proof. exact (EQ_MP (@lem7119555 A s u h1 h2 h3) (@lem0)). Qed.
Lemma lem7119557 {_132004 : Type'} (f : _132004 -> real) : term672 _132004 f.
Proof. exact (@lem7070827 _132004 f). Qed.
Lemma lem7119558 {_132004 : Type'} (f : _132004 -> real) : (term672 _132004 f) = (term673 _132004 f).
Proof. exact (eq_refl (term672 _132004 f)). Qed.
Lemma lem7119559 {_132004 : Type'} (f : _132004 -> real) : term673 _132004 f.
Proof. exact (EQ_MP (@lem7119558 _132004 f) (@lem7119557 _132004 f)). Qed.
Lemma lem7119560 {_132004 : Type'} (f : _132004 -> real) (s : _132004 -> Prop) : term674 _132004 f s.
Proof. exact (@lem7119559 _132004 f s). Qed.
Lemma lem7119561 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term674 _132004 f s) = ((term651 _132004 s f) = (term675 _132004 s f)).
Proof. exact (eq_refl (term674 _132004 f s)). Qed.
Lemma lem7119563 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7119565 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) : term413 A s u i.
Proof. exact (@lem7119351 A s u h1 i). Qed.
Lemma lem7119566 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term413 A s u i) = (term363 A s u i).
Proof. exact (eq_refl (term413 A s u i)). Qed.
Lemma lem7119567 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) : term363 A s u i.
Proof. exact (EQ_MP (@lem7119566 A s u i) (@lem7119565 A i s u h1)). Qed.
Lemma lem7119568 {A : Type'} (s : A -> Prop) (u : A -> real) (i : A) : (term363 A s u i) = ((term363 A s u i) = True).
Proof. exact (@lem7 (term363 A s u i)). Qed.
Lemma lem7119573 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7119563 A s) (@lem7119349 A s h1)). Qed.
Lemma lem7119574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7119575 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term654 A s) = (and True).
Proof. exact (MK_COMB (@lem7119574) (@lem7119573 A s h1)). Qed.
Lemma lem7119583 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) : (term363 A s u i) = True.
Proof. exact (EQ_MP (@lem7119568 A s u i) (@lem7119567 A i s u h1)). Qed.
Lemma lem7119584 {A : Type'} (i : A) (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) : (term363 A s u i) = True.
Proof. exact (@lem7119583 A i s u h1). Qed.
Lemma lem7119585 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) : (term364 A s u) = (term665 A).
Proof. exact (fun_ext (fun i : A => @lem7119584 A i s u h1)). Qed.
Lemma lem7119586 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7119587 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) : (term365 A s u) = (term666 A).
Proof. exact (MK_COMB (@lem7119586 A) (@lem7119585 A s u h1)). Qed.
Lemma lem7119589 {A : Type'} (t : Prop) : (term667 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7119590 {A : Type'} (t : Prop) : (term667 A t) = t.
Proof. exact (@lem7119589 A t). Qed.
Lemma lem7119591 {A : Type'} : (term666 A) = True.
Proof. exact (@lem7119590 A True). Qed.
Lemma lem7119592 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) : (term365 A s u) = True.
Proof. exact (TRANS (@lem7119587 A s u h1) (@lem7119591 A)). Qed.
Lemma lem7119593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7119594 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) : (term650 A s u) = (and True).
Proof. exact (MK_COMB (@lem7119593) (@lem7119592 A s u h1)). Qed.
Lemma lem7119598 {_132004 : Type'} (s : _132004 -> Prop) (f : _132004 -> real) : (term651 _132004 s f) = (term675 _132004 s f).
Proof. exact (EQ_MP (@lem7119561 _132004 s f) (@lem7119560 _132004 f s)). Qed.
Lemma lem7119599 {A : Type'} (s : A -> Prop) (f : A -> real) : (term651 A s f) = (term675 A s f).
Proof. exact (@lem7119598 A s f). Qed.
Lemma lem7119600 {A : Type'} (s : A -> Prop) (u : A -> real) : (term651 A s u) = (term675 A s u).
Proof. exact (@lem7119599 A s u). Qed.
Lemma lem7119602 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : (@sum A s u) = term15) : (@sum A s u) = term15.
Proof. exact (h1). Qed.
Lemma lem7119603 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7119604 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : (@sum A s u) = term15) : (term675 A s u) = term676.
Proof. exact (MK_COMB (@lem7119603) (@lem7119602 A s u h1)). Qed.
Lemma lem7119606 : term676 = term15.
Proof. exact (EQ_MP (@lem1361604) (@lem1362040)). Qed.
Lemma lem7119607 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : (@sum A s u) = term15) : (term675 A s u) = term15.
Proof. exact (TRANS (@lem7119604 A s u h1) (@lem7119606)). Qed.
Lemma lem7119608 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : (@sum A s u) = term15) : (term651 A s u) = term15.
Proof. exact (TRANS (@lem7119600 A s u) (@lem7119607 A s u h1)). Qed.
Lemma lem7119609 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7119610 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : (@sum A s u) = term15) : (term677 A s u) = term670.
Proof. exact (MK_COMB (@lem7119609) (@lem7119608 A s u h1)). Qed.
Lemma lem7119611 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7119612 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : (@sum A s u) = term15) : ((term651 A s u) = term15) = (term15 = term15).
Proof. exact (MK_COMB (@lem7119610 A s u h1) (@lem7119611)). Qed.
Lemma lem7119614 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7119615 (x : real) : (x = x) = True.
Proof. exact (@lem7119614 real x). Qed.
Lemma lem7119616 : (term15 = term15) = True.
Proof. exact (@lem7119615 term15). Qed.
Lemma lem7119617 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : (@sum A s u) = term15) : ((term651 A s u) = term15) = True.
Proof. exact (TRANS (@lem7119612 A s u h1) (@lem7119616)). Qed.
Lemma lem7119618 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) (h2 : (@sum A s u) = term15) : (term653 A s u) = (True /\ True).
Proof. exact (MK_COMB (@lem7119594 A s u h1) (@lem7119617 A s u h2)). Qed.
Lemma lem7119620 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7119621 : (True /\ True) = True.
Proof. exact (@lem7119620 True). Qed.
Lemma lem7119622 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) (h2 : (@sum A s u) = term15) : (term653 A s u) = True.
Proof. exact (TRANS (@lem7119618 A s u h1 h2) (@lem7119621)). Qed.
Lemma lem7119623 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : (term656 A s u) = (True /\ True).
Proof. exact (MK_COMB (@lem7119575 A s h2) (@lem7119622 A s u h1 h3)). Qed.
Lemma lem7119625 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7119626 : (True /\ True) = True.
Proof. exact (@lem7119625 True). Qed.
Lemma lem7119627 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : (term656 A s u) = True.
Proof. exact (TRANS (@lem7119623 A s u h1 h2 h3) (@lem7119626)). Qed.
Lemma lem7119628 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : True = (term656 A s u).
Proof. exact (SYM (@lem7119627 A s u h1 h2 h3)). Qed.
Lemma lem7119629 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : term656 A s u.
Proof. exact (EQ_MP (@lem7119628 A s u h1 h2 h3) (@lem0)). Qed.
Lemma lem7119630 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : term640 A s u.
Proof. exact (@lem7119493 A s u (@lem7119629 A s u h1 h2 h3)). Qed.
Lemma lem7119631 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : term6 A s u.
Proof. exact (@lem7119461 A s u (@lem7119556 A s u h1 h2 h3)). Qed.
Lemma lem7119632 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : term6 A s u.
Proof. exact (EQ_MP (@lem7119457 A s u) (@lem7119630 A s u h1 h2 h3)). Qed.
Lemma lem7119635 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : term632 A s u.
Proof. exact (or_intro1 (@lem7119632 A s u h1 h2 h3) (term316 A s u)). Qed.
Lemma lem7119636 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : term632 A s u.
Proof. exact (or_intro1 (@lem7119631 A s u h1 h2 h3) (term316 A s u)). Qed.
Lemma lem7119637 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : (term365 A s u) = (term632 A s u).
Proof. exact (prop_ext (fun h4 : term365 A s u => @lem7119635 A s u h1 h2 h3) (fun h4 : term632 A s u => @lem7119351 A s u h1)). Qed.
Lemma lem7119638 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term365 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : term632 A s u.
Proof. exact (EQ_MP (@lem7119637 A s u h1 h2 h3) (@lem7119351 A s u h1)). Qed.
Lemma lem7119639 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : (term368 A s u) = (term632 A s u).
Proof. exact (prop_ext (fun h4 : term368 A s u => @lem7119636 A s u h1 h2 h3) (fun h4 : term632 A s u => @lem7119350 A s u h1)). Qed.
Lemma lem7119640 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term368 A s u) (h2 : @FINITE A s) (h3 : (@sum A s u) = term15) : term632 A s u.
Proof. exact (EQ_MP (@lem7119639 A s u h1 h2 h3) (@lem7119350 A s u h1)). Qed.
Lemma lem7119641 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : @FINITE A s) (h2 : (@sum A s u) = term15) (h3 : term320 A s u) : term632 A s u.
Proof. exact (or_elim (@lem7119346 A s u h3) (fun h0 : term368 A s u => @lem7119640 A s u h0 h1 h2) (fun h0 : term365 A s u => @lem7119638 A s u h0 h1 h2)). Qed.
Lemma lem7119642 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term316 A s u) : (term316 A s u) = (term632 A s u).
Proof. exact (prop_ext (fun h2 : term316 A s u => @lem7119376 A s u h1) (fun h2 : term632 A s u => @lem7119345 A s u h1)). Qed.
Lemma lem7119643 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term316 A s u) : term632 A s u.
Proof. exact (EQ_MP (@lem7119642 A s u h1) (@lem7119345 A s u h1)). Qed.
Lemma lem7119644 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : @FINITE A s) (h2 : (@sum A s u) = term15) : term632 A s u.
Proof. exact (or_elim (@lem7119344 A s u) (fun h0 : term316 A s u => @lem7119643 A s u h0) (fun h0 : term320 A s u => @lem7119641 A s u h1 h2 h0)). Qed.
Lemma lem7119645 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term630 A s u) : (@sum A s u) = term15.
Proof. exact (proj2 (@lem7119347 A s u h1)). Qed.
Lemma lem7119646 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term630 A s u) : @FINITE A s.
Proof. exact (proj1 (@lem7119347 A s u h1)). Qed.
Lemma lem7119647 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : @FINITE A s) (h2 : (@sum A s u) = term15) : ((@sum A s u) = term15) = (term632 A s u).
Proof. exact (prop_ext (fun h3 : (@sum A s u) = term15 => @lem7119644 A s u h1 h2) (fun h3 : term632 A s u => @lem7119348 A s u h2)). Qed.
Lemma lem7119648 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : @FINITE A s) (h2 : (@sum A s u) = term15) : term632 A s u.
Proof. exact (EQ_MP (@lem7119647 A s u h1 h2) (@lem7119348 A s u h2)). Qed.
Lemma lem7119649 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : @FINITE A s) (h2 : (@sum A s u) = term15) : (@FINITE A s) = (term632 A s u).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7119648 A s u h1 h2) (fun h3 : term632 A s u => @lem7119349 A s h1)). Qed.
Lemma lem7119650 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : @FINITE A s) (h2 : (@sum A s u) = term15) : term632 A s u.
Proof. exact (EQ_MP (@lem7119649 A s u h1 h2) (@lem7119349 A s h1)). Qed.
Lemma lem7119651 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : @FINITE A s) (h2 : term630 A s u) : ((@sum A s u) = term15) = (term632 A s u).
Proof. exact (prop_ext (fun h3 : (@sum A s u) = term15 => @lem7119650 A s u h1 h3) (fun h3 : term632 A s u => @lem7119645 A s u h2)). Qed.
Lemma lem7119652 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : @FINITE A s) (h2 : term630 A s u) : term632 A s u.
Proof. exact (EQ_MP (@lem7119651 A s u h1 h2) (@lem7119645 A s u h2)). Qed.
Lemma lem7119653 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term630 A s u) : (@FINITE A s) = (term632 A s u).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7119652 A s u h2 h1) (fun h2 : term632 A s u => @lem7119646 A s u h1)). Qed.
Lemma lem7119654 {A : Type'} (s : A -> Prop) (u : A -> real) (h1 : term630 A s u) : term632 A s u.
Proof. exact (EQ_MP (@lem7119653 A s u h1) (@lem7119646 A s u h1)). Qed.
Lemma lem7119655 {A : Type'} (s : A -> Prop) (u : A -> real) : term678 A s u.
Proof. exact (fun h0 : term630 A s u => @lem7119654 A s u h0). Qed.
Lemma lem7119660 {A : Type'} (u : A -> real) : term679 A u.
Proof. exact (fun s : A -> Prop => @lem7119655 A s u). Qed.
Lemma lem7119665 {A : Type'} : term680 A.
Proof. exact (fun u : A -> real => @lem7119660 A u). Qed.
