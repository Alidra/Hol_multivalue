Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_CASES_term_abbrevs.
Require Import real_sgn_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm21735_spec.
Require Import thm21736_spec.
Lemma lem1740136 (x : real) : term0 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem1740137 (x : real) : (term0 x) = ((real_sgn x) = (term1 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1740148 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1740137 x) (@lem1740136 x)). Qed.
Lemma lem1740149 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740150 (x : real) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem1740149) (@lem1740148 x)). Qed.
Lemma lem1740151 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740152 (x : real) : ((real_sgn x) = term4) = ((term1 x) = term4).
Proof. exact (MK_COMB (@lem1740150 x) (@lem1740151)). Qed.
Lemma lem1740155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1740156 (x : real) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem1740155) (@lem1740152 x)). Qed.
Lemma lem1740162 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1740137 x) (@lem1740136 x)). Qed.
Lemma lem1740163 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740164 (x : real) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem1740163) (@lem1740162 x)). Qed.
Lemma lem1740165 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1740166 (x : real) : ((real_sgn x) = term7) = ((term1 x) = term7).
Proof. exact (MK_COMB (@lem1740164 x) (@lem1740165)). Qed.
Lemma lem1740169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1740170 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1740169) (@lem1740166 x)). Qed.
Lemma lem1740174 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1740137 x) (@lem1740136 x)). Qed.
Lemma lem1740175 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740176 (x : real) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem1740175) (@lem1740174 x)). Qed.
Lemma lem1740177 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1740178 (x : real) : ((real_sgn x) = term10) = ((term1 x) = term10).
Proof. exact (MK_COMB (@lem1740176 x) (@lem1740177)). Qed.
Lemma lem1740181 (x : real) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem1740170 x) (@lem1740178 x)). Qed.
Lemma lem1740184 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem1740156 x) (@lem1740181 x)). Qed.
Lemma lem1740187 : term15 = term16.
Proof. exact (fun_ext (fun x : real => @lem1740184 x)). Qed.
Lemma lem1740188 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1740189 : term17 = term18.
Proof. exact (MK_COMB (@lem1740188) (@lem1740187)). Qed.
Lemma lem1740194 : term18 = term17.
Proof. exact (SYM (@lem1740189)). Qed.
Lemma lem1740196 (p : Prop) : p = (term19 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1740197 : term18 = term20.
Proof. exact (@lem1740196 term18). Qed.
Lemma lem1740198 : term20 = term18.
Proof. exact (SYM (@lem1740197)). Qed.
Lemma lem1740199 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem1740202 (h1 : term20) : term20.
Proof. exact (h1). Qed.
Lemma lem1740203 : term22.
Proof. exact (fun h0 : term20 => @lem1740202 h0). Qed.
Lemma lem1740204 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1740205 (h1 : term20) : term20.
Proof. exact (h1). Qed.
Lemma lem1740206 (h1 : term20) (h2 : term22) : term20.
Proof. exact (@lem1740204 h2 (@lem1740205 h1)). Qed.
Lemma lem1740207 (h1 : term20) : term23.
Proof. exact (fun h0 : term22 => @lem1740206 h1 h0). Qed.
Lemma lem1740208 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1740209 (h1 : term20) (h2 : term22) : term20.
Proof. exact (@lem1740207 h1 (@lem1740208 h2)). Qed.
Lemma lem1740210 (h1 : term22) : term22.
Proof. exact (fun h0 : term20 => @lem1740209 h0 h1). Qed.
Lemma lem1740211 : term24.
Proof. exact (fun h0 : term22 => @lem1740210 h0). Qed.
Lemma lem1740214 : term22.
Proof. exact (@lem1740211 (@lem1740203)). Qed.
Lemma lem1740216 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1740217 : term20 = term25.
Proof. exact (@lem1740216 term21). Qed.
Lemma lem1740219 (t : Prop) : (term26 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1740220 : term25 = term18.
Proof. exact (@lem1740219 term18). Qed.
Lemma lem1740277 : term20 = term18.
Proof. exact (TRANS (@lem1740217) (@lem1740220)). Qed.
Lemma lem1740281 (x : real) (h1 : (term27 x) = False) : (term27 x) = False.
Proof. exact (h1). Qed.
Lemma lem1740282 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1740283 (x : real) (h1 : (term27 x) = False) : (term28 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1740282) (@lem1740281 x h1)). Qed.
Lemma lem1740284 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1740285 (x : real) (h1 : (term27 x) = False) : (term29 x) = term30.
Proof. exact (MK_COMB (@lem1740283 x h1) (@lem1740284)). Qed.
Lemma lem1740286 (x : real) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1740287 (x : real) (h1 : (term27 x) = False) : (term1 x) = (term32 x).
Proof. exact (MK_COMB (@lem1740285 x h1) (@lem1740286 x)). Qed.
Lemma lem1740289 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1740290 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1740289 real t1 t2). Qed.
Lemma lem1740291 (x : real) : (term32 x) = (term31 x).
Proof. exact (@lem1740290 term7 (term31 x)). Qed.
Lemma lem1740292 (x : real) (h1 : (term27 x) = False) : (term1 x) = (term31 x).
Proof. exact (TRANS (@lem1740287 x h1) (@lem1740291 x)). Qed.
Lemma lem1740293 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740294 (x : real) (h1 : (term27 x) = False) : (term3 x) = (term33 x).
Proof. exact (MK_COMB (@lem1740293) (@lem1740292 x h1)). Qed.
Lemma lem1740295 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740296 (x : real) (h1 : (term27 x) = False) : ((term1 x) = term4) = ((term31 x) = term4).
Proof. exact (MK_COMB (@lem1740294 x h1) (@lem1740295)). Qed.
Lemma lem1740299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1740300 (x : real) (h1 : (term27 x) = False) : (term6 x) = (term34 x).
Proof. exact (MK_COMB (@lem1740299) (@lem1740296 x h1)). Qed.
Lemma lem1740302 (x : real) (h1 : (term27 x) = False) : (term27 x) = False.
Proof. exact (h1). Qed.
Lemma lem1740303 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1740304 (x : real) (h1 : (term27 x) = False) : (term28 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1740303) (@lem1740302 x h1)). Qed.
Lemma lem1740305 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1740306 (x : real) (h1 : (term27 x) = False) : (term29 x) = term30.
Proof. exact (MK_COMB (@lem1740304 x h1) (@lem1740305)). Qed.
Lemma lem1740307 (x : real) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1740308 (x : real) (h1 : (term27 x) = False) : (term1 x) = (term32 x).
Proof. exact (MK_COMB (@lem1740306 x h1) (@lem1740307 x)). Qed.
Lemma lem1740310 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1740311 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1740310 real t1 t2). Qed.
Lemma lem1740312 (x : real) : (term32 x) = (term31 x).
Proof. exact (@lem1740311 term7 (term31 x)). Qed.
Lemma lem1740313 (x : real) (h1 : (term27 x) = False) : (term1 x) = (term31 x).
Proof. exact (TRANS (@lem1740308 x h1) (@lem1740312 x)). Qed.
Lemma lem1740314 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740315 (x : real) (h1 : (term27 x) = False) : (term3 x) = (term33 x).
Proof. exact (MK_COMB (@lem1740314) (@lem1740313 x h1)). Qed.
Lemma lem1740316 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1740317 (x : real) (h1 : (term27 x) = False) : ((term1 x) = term7) = ((term31 x) = term7).
Proof. exact (MK_COMB (@lem1740315 x h1) (@lem1740316)). Qed.
Lemma lem1740320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1740321 (x : real) (h1 : (term27 x) = False) : (term9 x) = (term35 x).
Proof. exact (MK_COMB (@lem1740320) (@lem1740317 x h1)). Qed.
Lemma lem1740323 (x : real) (h1 : (term27 x) = False) : (term27 x) = False.
Proof. exact (h1). Qed.
Lemma lem1740324 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1740325 (x : real) (h1 : (term27 x) = False) : (term28 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1740324) (@lem1740323 x h1)). Qed.
Lemma lem1740326 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1740327 (x : real) (h1 : (term27 x) = False) : (term29 x) = term30.
Proof. exact (MK_COMB (@lem1740325 x h1) (@lem1740326)). Qed.
Lemma lem1740328 (x : real) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1740329 (x : real) (h1 : (term27 x) = False) : (term1 x) = (term32 x).
Proof. exact (MK_COMB (@lem1740327 x h1) (@lem1740328 x)). Qed.
Lemma lem1740331 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1740332 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1740331 real t1 t2). Qed.
Lemma lem1740333 (x : real) : (term32 x) = (term31 x).
Proof. exact (@lem1740332 term7 (term31 x)). Qed.
Lemma lem1740334 (x : real) (h1 : (term27 x) = False) : (term1 x) = (term31 x).
Proof. exact (TRANS (@lem1740329 x h1) (@lem1740333 x)). Qed.
Lemma lem1740335 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740336 (x : real) (h1 : (term27 x) = False) : (term3 x) = (term33 x).
Proof. exact (MK_COMB (@lem1740335) (@lem1740334 x h1)). Qed.
Lemma lem1740337 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1740338 (x : real) (h1 : (term27 x) = False) : ((term1 x) = term10) = ((term31 x) = term10).
Proof. exact (MK_COMB (@lem1740336 x h1) (@lem1740337)). Qed.
Lemma lem1740341 (x : real) (h1 : (term27 x) = False) : (term12 x) = (term36 x).
Proof. exact (MK_COMB (@lem1740321 x h1) (@lem1740338 x h1)). Qed.
Lemma lem1740344 (x : real) (h1 : (term27 x) = False) : (term14 x) = (term37 x).
Proof. exact (MK_COMB (@lem1740300 x h1) (@lem1740341 x h1)). Qed.
Lemma lem1740347 (x : real) : term38 x.
Proof. exact (fun h0 : (term27 x) = False => @lem1740344 x h0). Qed.
Lemma lem1740349 (x : real) (h1 : (term27 x) = True) : (term27 x) = True.
Proof. exact (h1). Qed.
Lemma lem1740350 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1740351 (x : real) (h1 : (term27 x) = True) : (term28 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1740350) (@lem1740349 x h1)). Qed.
Lemma lem1740352 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1740353 (x : real) (h1 : (term27 x) = True) : (term29 x) = term39.
Proof. exact (MK_COMB (@lem1740351 x h1) (@lem1740352)). Qed.
Lemma lem1740354 (x : real) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1740355 (x : real) (h1 : (term27 x) = True) : (term1 x) = (term40 x).
Proof. exact (MK_COMB (@lem1740353 x h1) (@lem1740354 x)). Qed.
Lemma lem1740357 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1740358 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1740357 real t2 t1). Qed.
Lemma lem1740359 (x : real) : (term40 x) = term7.
Proof. exact (@lem1740358 (term31 x) term7). Qed.
Lemma lem1740360 (x : real) (h1 : (term27 x) = True) : (term1 x) = term7.
Proof. exact (TRANS (@lem1740355 x h1) (@lem1740359 x)). Qed.
Lemma lem1740361 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740362 (x : real) (h1 : (term27 x) = True) : (term3 x) = term41.
Proof. exact (MK_COMB (@lem1740361) (@lem1740360 x h1)). Qed.
Lemma lem1740363 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740364 (x : real) (h1 : (term27 x) = True) : ((term1 x) = term4) = (term7 = term4).
Proof. exact (MK_COMB (@lem1740362 x h1) (@lem1740363)). Qed.
Lemma lem1740367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1740368 (x : real) (h1 : (term27 x) = True) : (term6 x) = term42.
Proof. exact (MK_COMB (@lem1740367) (@lem1740364 x h1)). Qed.
Lemma lem1740370 (x : real) (h1 : (term27 x) = True) : (term27 x) = True.
Proof. exact (h1). Qed.
Lemma lem1740371 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1740372 (x : real) (h1 : (term27 x) = True) : (term28 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1740371) (@lem1740370 x h1)). Qed.
Lemma lem1740373 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1740374 (x : real) (h1 : (term27 x) = True) : (term29 x) = term39.
Proof. exact (MK_COMB (@lem1740372 x h1) (@lem1740373)). Qed.
Lemma lem1740375 (x : real) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1740376 (x : real) (h1 : (term27 x) = True) : (term1 x) = (term40 x).
Proof. exact (MK_COMB (@lem1740374 x h1) (@lem1740375 x)). Qed.
Lemma lem1740378 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1740379 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1740378 real t2 t1). Qed.
Lemma lem1740380 (x : real) : (term40 x) = term7.
Proof. exact (@lem1740379 (term31 x) term7). Qed.
Lemma lem1740381 (x : real) (h1 : (term27 x) = True) : (term1 x) = term7.
Proof. exact (TRANS (@lem1740376 x h1) (@lem1740380 x)). Qed.
Lemma lem1740382 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740383 (x : real) (h1 : (term27 x) = True) : (term3 x) = term41.
Proof. exact (MK_COMB (@lem1740382) (@lem1740381 x h1)). Qed.
Lemma lem1740384 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1740385 (x : real) (h1 : (term27 x) = True) : ((term1 x) = term7) = (term7 = term7).
Proof. exact (MK_COMB (@lem1740383 x h1) (@lem1740384)). Qed.
Lemma lem1740387 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1740388 (x : real) : (x = x) = True.
Proof. exact (@lem1740387 real x). Qed.
Lemma lem1740389 : (term7 = term7) = True.
Proof. exact (@lem1740388 term7). Qed.
Lemma lem1740390 (x : real) (h1 : (term27 x) = True) : ((term1 x) = term7) = True.
Proof. exact (TRANS (@lem1740385 x h1) (@lem1740389)). Qed.
Lemma lem1740391 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1740392 (x : real) (h1 : (term27 x) = True) : (term9 x) = (or True).
Proof. exact (MK_COMB (@lem1740391) (@lem1740390 x h1)). Qed.
Lemma lem1740394 (x : real) (h1 : (term27 x) = True) : (term27 x) = True.
Proof. exact (h1). Qed.
Lemma lem1740395 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1740396 (x : real) (h1 : (term27 x) = True) : (term28 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1740395) (@lem1740394 x h1)). Qed.
Lemma lem1740397 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1740398 (x : real) (h1 : (term27 x) = True) : (term29 x) = term39.
Proof. exact (MK_COMB (@lem1740396 x h1) (@lem1740397)). Qed.
Lemma lem1740399 (x : real) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1740400 (x : real) (h1 : (term27 x) = True) : (term1 x) = (term40 x).
Proof. exact (MK_COMB (@lem1740398 x h1) (@lem1740399 x)). Qed.
Lemma lem1740402 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1740403 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1740402 real t2 t1). Qed.
Lemma lem1740404 (x : real) : (term40 x) = term7.
Proof. exact (@lem1740403 (term31 x) term7). Qed.
Lemma lem1740405 (x : real) (h1 : (term27 x) = True) : (term1 x) = term7.
Proof. exact (TRANS (@lem1740400 x h1) (@lem1740404 x)). Qed.
Lemma lem1740406 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740407 (x : real) (h1 : (term27 x) = True) : (term3 x) = term41.
Proof. exact (MK_COMB (@lem1740406) (@lem1740405 x h1)). Qed.
Lemma lem1740408 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1740409 (x : real) (h1 : (term27 x) = True) : ((term1 x) = term10) = (term7 = term10).
Proof. exact (MK_COMB (@lem1740407 x h1) (@lem1740408)). Qed.
Lemma lem1740412 (x : real) (h1 : (term27 x) = True) : (term12 x) = term43.
Proof. exact (MK_COMB (@lem1740392 x h1) (@lem1740409 x h1)). Qed.
Lemma lem1740414 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1740415 : term43 = True.
Proof. exact (@lem1740414 (term7 = term10)). Qed.
Lemma lem1740416 (x : real) (h1 : (term27 x) = True) : (term12 x) = True.
Proof. exact (TRANS (@lem1740412 x h1) (@lem1740415)). Qed.
Lemma lem1740417 (x : real) (h1 : (term27 x) = True) : (term14 x) = term44.
Proof. exact (MK_COMB (@lem1740368 x h1) (@lem1740416 x h1)). Qed.
Lemma lem1740419 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1740420 : term44 = True.
Proof. exact (@lem1740419 (term7 = term4)). Qed.
Lemma lem1740421 (x : real) (h1 : (term27 x) = True) : (term14 x) = True.
Proof. exact (TRANS (@lem1740417 x h1) (@lem1740420)). Qed.
Lemma lem1740422 (x : real) : term45 x.
Proof. exact (fun h0 : (term27 x) = True => @lem1740421 x h0). Qed.
Lemma lem1740423 (x : real) : term46 x.
Proof. exact (conj (@lem1740347 x) (@lem1740422 x)). Qed.
Lemma lem1740425 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term47 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem1740426 (x : real) : term48 x.
Proof. exact (@lem1740425 (term14 x) True (term27 x) (term37 x)). Qed.
Lemma lem1740427 (x : real) : (term14 x) = (term49 x).
Proof. exact (@lem1740426 x (@lem1740423 x)). Qed.
Lemma lem1740430 (x : real) : (term50 x) = (term50 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1740432 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1740433 (x : real) : (term51 x) = True.
Proof. exact (@lem1740432 (term52 x)). Qed.
Lemma lem1740434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1740435 (x : real) : (term53 x) = (and True).
Proof. exact (MK_COMB (@lem1740434) (@lem1740433 x)). Qed.
Lemma lem1740436 (x : real) : (term49 x) = (term54 x).
Proof. exact (MK_COMB (@lem1740435 x) (@lem1740430 x)). Qed.
Lemma lem1740438 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1740439 (x : real) : (term54 x) = (term50 x).
Proof. exact (@lem1740438 (term50 x)). Qed.
Lemma lem1740440 (x : real) : (term49 x) = (term50 x).
Proof. exact (TRANS (@lem1740436 x) (@lem1740439 x)). Qed.
Lemma lem1740441 (x : real) : (term14 x) = (term50 x).
Proof. exact (TRANS (@lem1740427 x) (@lem1740440 x)). Qed.
Lemma lem1740445 (x : real) (h1 : (term55 x) = False) : (term55 x) = False.
Proof. exact (h1). Qed.
Lemma lem1740446 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1740447 (x : real) (h1 : (term55 x) = False) : (term56 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1740446) (@lem1740445 x h1)). Qed.
Lemma lem1740448 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1740449 (x : real) (h1 : (term55 x) = False) : (term57 x) = term58.
Proof. exact (MK_COMB (@lem1740447 x h1) (@lem1740448)). Qed.
Lemma lem1740450 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740451 (x : real) (h1 : (term55 x) = False) : (term31 x) = term59.
Proof. exact (MK_COMB (@lem1740449 x h1) (@lem1740450)). Qed.
Lemma lem1740453 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1740454 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1740453 real t1 t2). Qed.
Lemma lem1740455 : term59 = term4.
Proof. exact (@lem1740454 term10 term4). Qed.
Lemma lem1740456 (x : real) (h1 : (term55 x) = False) : (term31 x) = term4.
Proof. exact (TRANS (@lem1740451 x h1) (@lem1740455)). Qed.
Lemma lem1740457 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740458 (x : real) (h1 : (term55 x) = False) : (term33 x) = term60.
Proof. exact (MK_COMB (@lem1740457) (@lem1740456 x h1)). Qed.
Lemma lem1740459 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740460 (x : real) (h1 : (term55 x) = False) : ((term31 x) = term4) = (term4 = term4).
Proof. exact (MK_COMB (@lem1740458 x h1) (@lem1740459)). Qed.
Lemma lem1740462 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1740463 (x : real) : (x = x) = True.
Proof. exact (@lem1740462 real x). Qed.
Lemma lem1740464 : (term4 = term4) = True.
Proof. exact (@lem1740463 term4). Qed.
Lemma lem1740465 (x : real) (h1 : (term55 x) = False) : ((term31 x) = term4) = True.
Proof. exact (TRANS (@lem1740460 x h1) (@lem1740464)). Qed.
Lemma lem1740466 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1740467 (x : real) (h1 : (term55 x) = False) : (term34 x) = (or True).
Proof. exact (MK_COMB (@lem1740466) (@lem1740465 x h1)). Qed.
Lemma lem1740469 (x : real) (h1 : (term55 x) = False) : (term55 x) = False.
Proof. exact (h1). Qed.
Lemma lem1740470 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1740471 (x : real) (h1 : (term55 x) = False) : (term56 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1740470) (@lem1740469 x h1)). Qed.
Lemma lem1740472 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1740473 (x : real) (h1 : (term55 x) = False) : (term57 x) = term58.
Proof. exact (MK_COMB (@lem1740471 x h1) (@lem1740472)). Qed.
Lemma lem1740474 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740475 (x : real) (h1 : (term55 x) = False) : (term31 x) = term59.
Proof. exact (MK_COMB (@lem1740473 x h1) (@lem1740474)). Qed.
Lemma lem1740477 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1740478 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1740477 real t1 t2). Qed.
Lemma lem1740479 : term59 = term4.
Proof. exact (@lem1740478 term10 term4). Qed.
Lemma lem1740480 (x : real) (h1 : (term55 x) = False) : (term31 x) = term4.
Proof. exact (TRANS (@lem1740475 x h1) (@lem1740479)). Qed.
Lemma lem1740481 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740482 (x : real) (h1 : (term55 x) = False) : (term33 x) = term60.
Proof. exact (MK_COMB (@lem1740481) (@lem1740480 x h1)). Qed.
Lemma lem1740483 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1740484 (x : real) (h1 : (term55 x) = False) : ((term31 x) = term7) = (term4 = term7).
Proof. exact (MK_COMB (@lem1740482 x h1) (@lem1740483)). Qed.
Lemma lem1740487 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1740488 (x : real) (h1 : (term55 x) = False) : (term35 x) = term61.
Proof. exact (MK_COMB (@lem1740487) (@lem1740484 x h1)). Qed.
Lemma lem1740490 (x : real) (h1 : (term55 x) = False) : (term55 x) = False.
Proof. exact (h1). Qed.
Lemma lem1740491 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1740492 (x : real) (h1 : (term55 x) = False) : (term56 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1740491) (@lem1740490 x h1)). Qed.
Lemma lem1740493 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1740494 (x : real) (h1 : (term55 x) = False) : (term57 x) = term58.
Proof. exact (MK_COMB (@lem1740492 x h1) (@lem1740493)). Qed.
Lemma lem1740495 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740496 (x : real) (h1 : (term55 x) = False) : (term31 x) = term59.
Proof. exact (MK_COMB (@lem1740494 x h1) (@lem1740495)). Qed.
Lemma lem1740498 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1740499 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1740498 real t1 t2). Qed.
Lemma lem1740500 : term59 = term4.
Proof. exact (@lem1740499 term10 term4). Qed.
Lemma lem1740501 (x : real) (h1 : (term55 x) = False) : (term31 x) = term4.
Proof. exact (TRANS (@lem1740496 x h1) (@lem1740500)). Qed.
Lemma lem1740502 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740503 (x : real) (h1 : (term55 x) = False) : (term33 x) = term60.
Proof. exact (MK_COMB (@lem1740502) (@lem1740501 x h1)). Qed.
Lemma lem1740504 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1740505 (x : real) (h1 : (term55 x) = False) : ((term31 x) = term10) = (term4 = term10).
Proof. exact (MK_COMB (@lem1740503 x h1) (@lem1740504)). Qed.
Lemma lem1740508 (x : real) (h1 : (term55 x) = False) : (term36 x) = term62.
Proof. exact (MK_COMB (@lem1740488 x h1) (@lem1740505 x h1)). Qed.
Lemma lem1740511 (x : real) (h1 : (term55 x) = False) : (term37 x) = term63.
Proof. exact (MK_COMB (@lem1740467 x h1) (@lem1740508 x h1)). Qed.
Lemma lem1740513 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1740514 : term63 = True.
Proof. exact (@lem1740513 term62). Qed.
Lemma lem1740515 (x : real) (h1 : (term55 x) = False) : (term37 x) = True.
Proof. exact (TRANS (@lem1740511 x h1) (@lem1740514)). Qed.
Lemma lem1740516 (x : real) : (term64 x) = (term64 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1740517 (x : real) (h1 : (term55 x) = False) : (term50 x) = (term65 x).
Proof. exact (MK_COMB (@lem1740516 x) (@lem1740515 x h1)). Qed.
Lemma lem1740519 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1740520 (x : real) : (term65 x) = True.
Proof. exact (@lem1740519 (term27 x)). Qed.
Lemma lem1740521 (x : real) (h1 : (term55 x) = False) : (term50 x) = True.
Proof. exact (TRANS (@lem1740517 x h1) (@lem1740520 x)). Qed.
Lemma lem1740522 (x : real) : term66 x.
Proof. exact (fun h0 : (term55 x) = False => @lem1740521 x h0). Qed.
Lemma lem1740524 (x : real) (h1 : (term55 x) = True) : (term55 x) = True.
Proof. exact (h1). Qed.
Lemma lem1740525 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1740526 (x : real) (h1 : (term55 x) = True) : (term56 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1740525) (@lem1740524 x h1)). Qed.
Lemma lem1740527 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1740528 (x : real) (h1 : (term55 x) = True) : (term57 x) = term67.
Proof. exact (MK_COMB (@lem1740526 x h1) (@lem1740527)). Qed.
Lemma lem1740529 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740530 (x : real) (h1 : (term55 x) = True) : (term31 x) = term68.
Proof. exact (MK_COMB (@lem1740528 x h1) (@lem1740529)). Qed.
Lemma lem1740532 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1740533 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1740532 real t2 t1). Qed.
Lemma lem1740534 : term68 = term10.
Proof. exact (@lem1740533 term4 term10). Qed.
Lemma lem1740535 (x : real) (h1 : (term55 x) = True) : (term31 x) = term10.
Proof. exact (TRANS (@lem1740530 x h1) (@lem1740534)). Qed.
Lemma lem1740536 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740537 (x : real) (h1 : (term55 x) = True) : (term33 x) = term69.
Proof. exact (MK_COMB (@lem1740536) (@lem1740535 x h1)). Qed.
Lemma lem1740538 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740539 (x : real) (h1 : (term55 x) = True) : ((term31 x) = term4) = (term10 = term4).
Proof. exact (MK_COMB (@lem1740537 x h1) (@lem1740538)). Qed.
Lemma lem1740542 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1740543 (x : real) (h1 : (term55 x) = True) : (term34 x) = term70.
Proof. exact (MK_COMB (@lem1740542) (@lem1740539 x h1)). Qed.
Lemma lem1740545 (x : real) (h1 : (term55 x) = True) : (term55 x) = True.
Proof. exact (h1). Qed.
Lemma lem1740546 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1740547 (x : real) (h1 : (term55 x) = True) : (term56 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1740546) (@lem1740545 x h1)). Qed.
Lemma lem1740548 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1740549 (x : real) (h1 : (term55 x) = True) : (term57 x) = term67.
Proof. exact (MK_COMB (@lem1740547 x h1) (@lem1740548)). Qed.
Lemma lem1740550 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740551 (x : real) (h1 : (term55 x) = True) : (term31 x) = term68.
Proof. exact (MK_COMB (@lem1740549 x h1) (@lem1740550)). Qed.
Lemma lem1740553 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1740554 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1740553 real t2 t1). Qed.
Lemma lem1740555 : term68 = term10.
Proof. exact (@lem1740554 term4 term10). Qed.
Lemma lem1740556 (x : real) (h1 : (term55 x) = True) : (term31 x) = term10.
Proof. exact (TRANS (@lem1740551 x h1) (@lem1740555)). Qed.
Lemma lem1740557 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740558 (x : real) (h1 : (term55 x) = True) : (term33 x) = term69.
Proof. exact (MK_COMB (@lem1740557) (@lem1740556 x h1)). Qed.
Lemma lem1740559 : term7 = term7.
Proof. exact (eq_refl term7). Qed.
Lemma lem1740560 (x : real) (h1 : (term55 x) = True) : ((term31 x) = term7) = (term10 = term7).
Proof. exact (MK_COMB (@lem1740558 x h1) (@lem1740559)). Qed.
Lemma lem1740563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1740564 (x : real) (h1 : (term55 x) = True) : (term35 x) = term71.
Proof. exact (MK_COMB (@lem1740563) (@lem1740560 x h1)). Qed.
Lemma lem1740566 (x : real) (h1 : (term55 x) = True) : (term55 x) = True.
Proof. exact (h1). Qed.
Lemma lem1740567 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1740568 (x : real) (h1 : (term55 x) = True) : (term56 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1740567) (@lem1740566 x h1)). Qed.
Lemma lem1740569 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1740570 (x : real) (h1 : (term55 x) = True) : (term57 x) = term67.
Proof. exact (MK_COMB (@lem1740568 x h1) (@lem1740569)). Qed.
Lemma lem1740571 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740572 (x : real) (h1 : (term55 x) = True) : (term31 x) = term68.
Proof. exact (MK_COMB (@lem1740570 x h1) (@lem1740571)). Qed.
Lemma lem1740574 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1740575 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1740574 real t2 t1). Qed.
Lemma lem1740576 : term68 = term10.
Proof. exact (@lem1740575 term4 term10). Qed.
Lemma lem1740577 (x : real) (h1 : (term55 x) = True) : (term31 x) = term10.
Proof. exact (TRANS (@lem1740572 x h1) (@lem1740576)). Qed.
Lemma lem1740578 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1740579 (x : real) (h1 : (term55 x) = True) : (term33 x) = term69.
Proof. exact (MK_COMB (@lem1740578) (@lem1740577 x h1)). Qed.
Lemma lem1740580 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1740581 (x : real) (h1 : (term55 x) = True) : ((term31 x) = term10) = (term10 = term10).
Proof. exact (MK_COMB (@lem1740579 x h1) (@lem1740580)). Qed.
Lemma lem1740583 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1740584 (x : real) : (x = x) = True.
Proof. exact (@lem1740583 real x). Qed.
Lemma lem1740585 : (term10 = term10) = True.
Proof. exact (@lem1740584 term10). Qed.
Lemma lem1740586 (x : real) (h1 : (term55 x) = True) : ((term31 x) = term10) = True.
Proof. exact (TRANS (@lem1740581 x h1) (@lem1740585)). Qed.
Lemma lem1740587 (x : real) (h1 : (term55 x) = True) : (term36 x) = term72.
Proof. exact (MK_COMB (@lem1740564 x h1) (@lem1740586 x h1)). Qed.
Lemma lem1740589 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1740590 : term72 = True.
Proof. exact (@lem1740589 (term10 = term7)). Qed.
Lemma lem1740591 (x : real) (h1 : (term55 x) = True) : (term36 x) = True.
Proof. exact (TRANS (@lem1740587 x h1) (@lem1740590)). Qed.
Lemma lem1740592 (x : real) (h1 : (term55 x) = True) : (term37 x) = term73.
Proof. exact (MK_COMB (@lem1740543 x h1) (@lem1740591 x h1)). Qed.
Lemma lem1740594 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1740595 : term73 = True.
Proof. exact (@lem1740594 (term10 = term4)). Qed.
Lemma lem1740596 (x : real) (h1 : (term55 x) = True) : (term37 x) = True.
Proof. exact (TRANS (@lem1740592 x h1) (@lem1740595)). Qed.
Lemma lem1740597 (x : real) : (term64 x) = (term64 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1740598 (x : real) (h1 : (term55 x) = True) : (term50 x) = (term65 x).
Proof. exact (MK_COMB (@lem1740597 x) (@lem1740596 x h1)). Qed.
Lemma lem1740600 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1740601 (x : real) : (term65 x) = True.
Proof. exact (@lem1740600 (term27 x)). Qed.
Lemma lem1740602 (x : real) (h1 : (term55 x) = True) : (term50 x) = True.
Proof. exact (TRANS (@lem1740598 x h1) (@lem1740601 x)). Qed.
Lemma lem1740603 (x : real) : term74 x.
Proof. exact (fun h0 : (term55 x) = True => @lem1740602 x h0). Qed.
Lemma lem1740604 (x : real) : term75 x.
Proof. exact (conj (@lem1740522 x) (@lem1740603 x)). Qed.
Lemma lem1740606 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term47 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem1740607 (x : real) : term76 x.
Proof. exact (@lem1740606 (term50 x) True (term55 x) True). Qed.
Lemma lem1740608 (x : real) : (term50 x) = (term77 x).
Proof. exact (@lem1740607 x (@lem1740604 x)). Qed.
Lemma lem1740610 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1740611 (x : real) : (term78 x) = True.
Proof. exact (@lem1740610 (term55 x)). Qed.
Lemma lem1740613 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1740614 (x : real) : (term79 x) = True.
Proof. exact (@lem1740613 (term80 x)). Qed.
Lemma lem1740615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1740616 (x : real) : (term81 x) = (and True).
Proof. exact (MK_COMB (@lem1740615) (@lem1740614 x)). Qed.
Lemma lem1740617 (x : real) : (term77 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1740616 x) (@lem1740611 x)). Qed.
Lemma lem1740619 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1740620 : (True /\ True) = True.
Proof. exact (@lem1740619 True). Qed.
Lemma lem1740621 (x : real) : (term77 x) = True.
Proof. exact (TRANS (@lem1740617 x) (@lem1740620)). Qed.
Lemma lem1740626 (x : real) : (term50 x) = True.
Proof. exact (TRANS (@lem1740608 x) (@lem1740621 x)). Qed.
Lemma lem1740627 (x : real) : (term82 x) = (term82 x).
Proof. exact (eq_refl (term82 x)). Qed.
Lemma lem1740628 (x : real) : ((term14 x) = (term50 x)) = ((term14 x) = True).
Proof. exact (MK_COMB (@lem1740627 x) (@lem1740626 x)). Qed.
Lemma lem1740629 (x : real) : (term14 x) = True.
Proof. exact (EQ_MP (@lem1740628 x) (@lem1740441 x)). Qed.
Lemma lem1740630 : term16 = term83.
Proof. exact (fun_ext (fun x : real => @lem1740629 x)). Qed.
Lemma lem1740631 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1740632 : term18 = term84.
Proof. exact (MK_COMB (@lem1740631) (@lem1740630)). Qed.
Lemma lem1740633 : term20 = term84.
Proof. exact (TRANS (@lem1740277) (@lem1740632)). Qed.
Lemma lem1740635 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem1740636 (t : Prop) : (term86 t) = t.
Proof. exact (@lem1740635 real t). Qed.
Lemma lem1740637 : term84 = True.
Proof. exact (@lem1740636 True). Qed.
Lemma lem1740638 : term20 = True.
Proof. exact (TRANS (@lem1740633) (@lem1740637)). Qed.
Lemma lem1740639 : True = term20.
Proof. exact (SYM (@lem1740638)). Qed.
Lemma lem1740640 : term20.
Proof. exact (EQ_MP (@lem1740639) (@lem0)). Qed.
Lemma lem1740642 : term20.
Proof. exact (@lem1740214 (@lem1740640)). Qed.
Lemma lem1740643 (h1 : term21) : False.
Proof. exact (@lem1740642 (@lem1740199 h1)). Qed.
Lemma lem1740644 (h1 : term21) : term21 = False.
Proof. exact (prop_ext (fun h2 : term21 => @lem1740643 h1) (fun h2 : False => @lem1740199 h1)). Qed.
Lemma lem1740645 (h1 : term21) : False.
Proof. exact (EQ_MP (@lem1740644 h1) (@lem1740199 h1)). Qed.
Lemma lem1740646 : term20.
Proof. exact (fun h0 : term21 => @lem1740645 h0). Qed.
Lemma lem1740647 : term18.
Proof. exact (EQ_MP (@lem1740198) (@lem1740646)). Qed.
Lemma lem1740648 : term17.
Proof. exact (EQ_MP (@lem1740194) (@lem1740647)). Qed.
