Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1710422_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm12653_spec.
Require Import thm1366270_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367254_spec.
Require Import thm1386578_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483554_spec.
Require Import thm1834_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm20234_spec.
Require Import thm20420_spec.
Require Import thm20421_spec.
Require Import thm940073_spec.
Lemma lem1710188 (h1 : term0 = False) : term0 = False.
Proof. exact (h1). Qed.
Lemma lem1710189 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710190 (h1 : term0 = False) : term1 = (@COND real False).
Proof. exact (MK_COMB (@lem1710189) (@lem1710188 h1)). Qed.
Lemma lem1710191 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1710192 (h1 : term0 = False) : term3 = term4.
Proof. exact (MK_COMB (@lem1710190 h1) (@lem1710191)). Qed.
Lemma lem1710194 (h1 : term0 = False) : term0 = False.
Proof. exact (h1). Qed.
Lemma lem1710195 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710196 (h1 : term0 = False) : term1 = (@COND real False).
Proof. exact (MK_COMB (@lem1710195) (@lem1710194 h1)). Qed.
Lemma lem1710197 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1710198 (h1 : term0 = False) : term6 = term7.
Proof. exact (MK_COMB (@lem1710196 h1) (@lem1710197)). Qed.
Lemma lem1710199 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1710200 (h1 : term0 = False) : term9 = term10.
Proof. exact (MK_COMB (@lem1710198 h1) (@lem1710199)). Qed.
Lemma lem1710202 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1710203 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1710202 real t1 t2). Qed.
Lemma lem1710204 : term10 = term8.
Proof. exact (@lem1710203 term5 term8). Qed.
Lemma lem1710205 (h1 : term0 = False) : term9 = term8.
Proof. exact (TRANS (@lem1710200 h1) (@lem1710204)). Qed.
Lemma lem1710206 (h1 : term0 = False) : term11 = term12.
Proof. exact (MK_COMB (@lem1710192 h1) (@lem1710205 h1)). Qed.
Lemma lem1710208 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1710209 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1710208 real t1 t2). Qed.
Lemma lem1710210 : term12 = term8.
Proof. exact (@lem1710209 term2 term8). Qed.
Lemma lem1710211 (h1 : term0 = False) : term11 = term8.
Proof. exact (TRANS (@lem1710206 h1) (@lem1710210)). Qed.
Lemma lem1710212 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1710213 (h1 : term0 = False) : term13 = term14.
Proof. exact (MK_COMB (@lem1710212) (@lem1710211 h1)). Qed.
Lemma lem1710214 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1710215 (h1 : term0 = False) : (term11 = term8) = (term8 = term8).
Proof. exact (MK_COMB (@lem1710213 h1) (@lem1710214)). Qed.
Lemma lem1710217 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1710218 (x : real) : (x = x) = True.
Proof. exact (@lem1710217 real x). Qed.
Lemma lem1710219 : (term8 = term8) = True.
Proof. exact (@lem1710218 term8). Qed.
Lemma lem1710220 (h1 : term0 = False) : (term11 = term8) = True.
Proof. exact (TRANS (@lem1710215 h1) (@lem1710219)). Qed.
Lemma lem1710221 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710222 (h1 : term0 = False) : term15 = (~ True).
Proof. exact (MK_COMB (@lem1710221) (@lem1710220 h1)). Qed.
Lemma lem1710224 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1710225 (h1 : term0 = False) : term15 = False.
Proof. exact (TRANS (@lem1710222 h1) (@lem1710224)). Qed.
Lemma lem1710226 : term16.
Proof. exact (fun h0 : term0 = False => @lem1710225 h0). Qed.
Lemma lem1710228 (h1 : term0 = True) : term0 = True.
Proof. exact (h1). Qed.
Lemma lem1710229 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710230 (h1 : term0 = True) : term1 = (@COND real True).
Proof. exact (MK_COMB (@lem1710229) (@lem1710228 h1)). Qed.
Lemma lem1710231 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1710232 (h1 : term0 = True) : term3 = term17.
Proof. exact (MK_COMB (@lem1710230 h1) (@lem1710231)). Qed.
Lemma lem1710234 (h1 : term0 = True) : term0 = True.
Proof. exact (h1). Qed.
Lemma lem1710235 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710236 (h1 : term0 = True) : term1 = (@COND real True).
Proof. exact (MK_COMB (@lem1710235) (@lem1710234 h1)). Qed.
Lemma lem1710237 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1710238 (h1 : term0 = True) : term6 = term18.
Proof. exact (MK_COMB (@lem1710236 h1) (@lem1710237)). Qed.
Lemma lem1710239 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1710240 (h1 : term0 = True) : term9 = term19.
Proof. exact (MK_COMB (@lem1710238 h1) (@lem1710239)). Qed.
Lemma lem1710242 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1710243 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1710242 real t2 t1). Qed.
Lemma lem1710244 : term19 = term5.
Proof. exact (@lem1710243 term8 term5). Qed.
Lemma lem1710245 (h1 : term0 = True) : term9 = term5.
Proof. exact (TRANS (@lem1710240 h1) (@lem1710244)). Qed.
Lemma lem1710246 (h1 : term0 = True) : term11 = term20.
Proof. exact (MK_COMB (@lem1710232 h1) (@lem1710245 h1)). Qed.
Lemma lem1710248 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1710249 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1710248 real t2 t1). Qed.
Lemma lem1710250 : term20 = term2.
Proof. exact (@lem1710249 term5 term2). Qed.
Lemma lem1710251 (h1 : term0 = True) : term11 = term2.
Proof. exact (TRANS (@lem1710246 h1) (@lem1710250)). Qed.
Lemma lem1710252 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1710253 (h1 : term0 = True) : term13 = term21.
Proof. exact (MK_COMB (@lem1710252) (@lem1710251 h1)). Qed.
Lemma lem1710254 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1710255 (h1 : term0 = True) : (term11 = term8) = (term2 = term8).
Proof. exact (MK_COMB (@lem1710253 h1) (@lem1710254)). Qed.
Lemma lem1710258 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710259 (h1 : term0 = True) : term15 = term22.
Proof. exact (MK_COMB (@lem1710258) (@lem1710255 h1)). Qed.
Lemma lem1710260 : term23.
Proof. exact (fun h0 : term0 = True => @lem1710259 h0). Qed.
Lemma lem1710261 : term24.
Proof. exact (conj (@lem1710226) (@lem1710260)). Qed.
Lemma lem1710263 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term25 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1710264 : term26.
Proof. exact (@lem1710263 term15 term22 term0 False). Qed.
Lemma lem1710265 : term15 = term27.
Proof. exact (@lem1710264 (@lem1710261)). Qed.
Lemma lem1710267 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1710268 : term28 = False.
Proof. exact (@lem1710267 term29). Qed.
Lemma lem1710273 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1710274 : term27 = term31.
Proof. exact (MK_COMB (@lem1710273) (@lem1710268)). Qed.
Lemma lem1710276 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1710277 : term31 = term32.
Proof. exact (@lem1710276 term32). Qed.
Lemma lem1710278 : term27 = term32.
Proof. exact (TRANS (@lem1710274) (@lem1710277)). Qed.
Lemma lem1710290 : term15 = term32.
Proof. exact (TRANS (@lem1710265) (@lem1710278)). Qed.
Lemma lem1710291 : term0 = term33.
Proof. exact (@lem1483521 term8 term8). Qed.
Lemma lem1710297 : term34 = term35.
Proof. exact (@lem1483519 term8 term8). Qed.
Lemma lem1710299 (x : nat) : (term36 x) = term8.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1710300 : term37 = term8.
Proof. exact (@lem1710299 term38). Qed.
Lemma lem1710301 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1710302 : term35 = term40.
Proof. exact (MK_COMB (@lem1710301) (@lem1710300)). Qed.
Lemma lem1710303 : term40 = term8.
Proof. exact (@lem1483448 term8). Qed.
Lemma lem1710304 : term35 = term8.
Proof. exact (TRANS (@lem1710302) (@lem1710303)). Qed.
Lemma lem1710306 : term34 = term8.
Proof. exact (TRANS (@lem1710297) (@lem1710304)). Qed.
Lemma lem1710307 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1710308 : term41 = term42.
Proof. exact (MK_COMB (@lem1710307) (@lem1710306)). Qed.
Lemma lem1710309 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1710310 : term33 = term43.
Proof. exact (MK_COMB (@lem1710308) (@lem1710309)). Qed.
Lemma lem1710311 : term0 = term43.
Proof. exact (TRANS (@lem1710291) (@lem1710310)). Qed.
Lemma lem1710312 : term22 = term44.
Proof. exact (@lem1483554 term2 term8). Qed.
Lemma lem1710318 : term45 = term46.
Proof. exact (@lem1483519 term2 term8). Qed.
Lemma lem1710320 (x : nat) : (term36 x) = term8.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1710321 : term37 = term8.
Proof. exact (@lem1710320 term38). Qed.
Lemma lem1710322 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1710323 : term46 = term48.
Proof. exact (MK_COMB (@lem1710322) (@lem1710321)). Qed.
Lemma lem1710324 : term48 = term2.
Proof. exact (@lem1483450 term2). Qed.
Lemma lem1710325 : term46 = term2.
Proof. exact (TRANS (@lem1710323) (@lem1710324)). Qed.
Lemma lem1710327 : term45 = term2.
Proof. exact (TRANS (@lem1710318) (@lem1710325)). Qed.
Lemma lem1710328 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1710329 : term49 = term5.
Proof. exact (MK_COMB (@lem1710328) (@lem1710327)). Qed.
Lemma lem1710330 : term5 = term50.
Proof. exact (@lem1483512 term2). Qed.
Lemma lem1710332 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1710333 : term50 = term53.
Proof. exact (@lem1710332 term38 term38). Qed.
Lemma lem1710334 : (term54 = (BIT1 0)) = (term55 = term38).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1710335 : term55 = term38.
Proof. exact (EQ_MP (@lem1710334) (@lem940073)). Qed.
Lemma lem1710336 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1710337 : term56 = term2.
Proof. exact (MK_COMB (@lem1710336) (@lem1710335)). Qed.
Lemma lem1710338 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1710339 : term53 = term5.
Proof. exact (MK_COMB (@lem1710338) (@lem1710337)). Qed.
Lemma lem1710340 : term50 = term5.
Proof. exact (TRANS (@lem1710333) (@lem1710339)). Qed.
Lemma lem1710341 : term5 = term5.
Proof. exact (TRANS (@lem1710330) (@lem1710340)). Qed.
Lemma lem1710342 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem1710343 : (term49 = term5) = (term49 = term5).
Proof. exact (MK_COMB (@lem1710342) (@lem1710341)). Qed.
Lemma lem1710344 : term49 = term5.
Proof. exact (EQ_MP (@lem1710343) (@lem1710329)). Qed.
Lemma lem1710345 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1710346 : term58 = term59.
Proof. exact (MK_COMB (@lem1710345) (@lem1710344)). Qed.
Lemma lem1710347 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1710348 : term60 = term61.
Proof. exact (MK_COMB (@lem1710346) (@lem1710347)). Qed.
Lemma lem1710349 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1710350 : term62 = term63.
Proof. exact (MK_COMB (@lem1710349) (@lem1710327)). Qed.
Lemma lem1710351 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1710352 : term64 = term65.
Proof. exact (MK_COMB (@lem1710350) (@lem1710351)). Qed.
Lemma lem1710353 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1710354 : term66 = term67.
Proof. exact (MK_COMB (@lem1710353) (@lem1710352)). Qed.
Lemma lem1710355 : term44 = term68.
Proof. exact (MK_COMB (@lem1710354) (@lem1710348)). Qed.
Lemma lem1710356 : term22 = term68.
Proof. exact (TRANS (@lem1710312) (@lem1710355)). Qed.
Lemma lem1710357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1710358 : term69 = term70.
Proof. exact (MK_COMB (@lem1710357) (@lem1710311)). Qed.
Lemma lem1710359 : term32 = term71.
Proof. exact (MK_COMB (@lem1710358) (@lem1710356)). Qed.
Lemma lem1710366 : term15 = term71.
Proof. exact (TRANS (@lem1710290) (@lem1710359)). Qed.
Lemma lem1710383 : term71 = term72.
Proof. exact (@lem19158 term65 term43 term61). Qed.
Lemma lem1710384 : term15 = term72.
Proof. exact (TRANS (@lem1710366) (@lem1710383)). Qed.
Lemma lem1710394 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem1710395 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1710397 (h1 : term73) : term43.
Proof. exact (proj1 (@lem1710395 h1)). Qed.
Lemma lem1710399 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1710400 : term43 = term75.
Proof. exact (@lem1710399 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1710401 : term75 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1710402 : term43 = False.
Proof. exact (TRANS (@lem1710400) (@lem1710401)). Qed.
Lemma lem1710403 (h1 : term73) : False.
Proof. exact (EQ_MP (@lem1710402) (@lem1710397 h1)). Qed.
Lemma lem1710404 (h1 : term76) : term76.
Proof. exact (h1). Qed.
Lemma lem1710405 (h1 : term76) : term61.
Proof. exact (proj2 (@lem1710404 h1)). Qed.
Lemma lem1710408 (m : nat) (n : nat) : (term77 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1710409 : term61 = False.
Proof. exact (@lem1710408 term38 (NUMERAL 0)). Qed.
Lemma lem1710410 (h1 : term76) : False.
Proof. exact (EQ_MP (@lem1710409) (@lem1710405 h1)). Qed.
Lemma lem1710411 (h1 : term72) : False.
Proof. exact (or_elim (@lem1710394 h1) (fun h0 : term73 => @lem1710403 h0) (fun h0 : term76 => @lem1710410 h0)). Qed.
Lemma lem1710413 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem1710414 (h1 : term72) : term72 = False.
Proof. exact (prop_ext (fun h2 : term72 => @lem1710411 h1) (fun h2 : False => @lem1710413 h1)). Qed.
Lemma lem1710415 (h1 : term72) : False.
Proof. exact (EQ_MP (@lem1710414 h1) (@lem1710413 h1)). Qed.
Lemma lem1710416 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem1710417 (h1 : term15) : term72.
Proof. exact (EQ_MP (@lem1710384) (@lem1710416 h1)). Qed.
Lemma lem1710418 (h1 : term15) : term72 = False.
Proof. exact (prop_ext (fun h2 : term72 => @lem1710415 h2) (fun h2 : False => @lem1710417 h1)). Qed.
Lemma lem1710419 (h1 : term15) : False.
Proof. exact (EQ_MP (@lem1710418 h1) (@lem1710417 h1)). Qed.
Lemma lem1710420 : term78.
Proof. exact (fun h0 : term15 => @lem1710419 h0). Qed.
Lemma lem1710421 : term79.
Proof. exact (@lem1386578 (term11 = term8)). Qed.
Lemma lem1710422 : term11 = term8.
Proof. exact (@lem1710421 (@lem1710420)). Qed.
