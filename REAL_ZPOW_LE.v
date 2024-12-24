Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_LE_term_abbrevs.
Require Import FORALL_INT_CASES_spec.
Require Import REAL_LE_INV_EQ_spec.
Require Import REAL_POW_LE_spec.
Require Import REAL_ZPOW_POW_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem3179168 (x : real) : term0 x.
Proof. exact (@lem1582434 x). Qed.
Lemma lem3179169 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3179170 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem3179169 x) (@lem3179168 x)). Qed.
Lemma lem3179171 (x : real) (n : nat) : term2 x n.
Proof. exact (@lem3179170 x n). Qed.
Lemma lem3179172 (x : real) (n : nat) : (term2 x n) = (term3 x n).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem3179173 (x : real) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem3179172 x n) (@lem3179171 x n)). Qed.
Lemma lem3179174 (x : real) (h1 : term4 x) : term4 x.
Proof. exact (h1). Qed.
Lemma lem3179175 (n : nat) (x : real) (h1 : term4 x) : term5 x n.
Proof. exact (@lem3179173 x n (@lem3179174 x h1)). Qed.
Lemma lem3179176 (x : real) (n : nat) : (term5 x n) = ((term5 x n) = True).
Proof. exact (@lem7 (term5 x n)). Qed.
Lemma lem3179177 (n : nat) (x : real) (h1 : term4 x) : (term5 x n) = True.
Proof. exact (EQ_MP (@lem3179176 x n) (@lem3179175 n x h1)). Qed.
Lemma lem3179183 (x : real) : term6 x.
Proof. exact (@lem1591907 x). Qed.
Lemma lem3179184 (x : real) : (term6 x) = ((term7 x) = (term4 x)).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem3179186 : term8.
Proof. exact (proj2 (@lem3174260)). Qed.
Lemma lem3179187 (x : real) : term9 x.
Proof. exact (@lem3179186 x). Qed.
Lemma lem3179188 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem3179189 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem3179188 x) (@lem3179187 x)). Qed.
Lemma lem3179190 (x : real) (n : nat) : term11 x n.
Proof. exact (@lem3179189 x n). Qed.
Lemma lem3179191 (x : real) (n : nat) : (term11 x n) = ((term12 x n) = (term13 x n)).
Proof. exact (eq_refl (term11 x n)). Qed.
Lemma lem3179193 : term14.
Proof. exact (proj1 (@lem3174260)). Qed.
Lemma lem3179194 (x : real) : term15 x.
Proof. exact (@lem3179193 x). Qed.
Lemma lem3179195 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem3179196 (x : real) : term16 x.
Proof. exact (EQ_MP (@lem3179195 x) (@lem3179194 x)). Qed.
Lemma lem3179197 (x : real) (n : nat) : term17 x n.
Proof. exact (@lem3179196 x n). Qed.
Lemma lem3179198 (x : real) (n : nat) : (term17 x n) = ((term18 x n) = (real_pow x n)).
Proof. exact (eq_refl (term17 x n)). Qed.
Lemma lem3179200 (P : int -> Prop) : term19 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem3179201 (P : int -> Prop) : (term19 P) = ((term20 P) = (term21 P)).
Proof. exact (eq_refl (term19 P)). Qed.
Lemma lem3179214 (P : int -> Prop) : (term20 P) = (term21 P).
Proof. exact (EQ_MP (@lem3179201 P) (@lem3179200 P)). Qed.
Lemma lem3179215 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem3179214 (term24 x)). Qed.
Lemma lem3179216 (x : real) (n : int) : (term25 x n) = (term26 x n).
Proof. exact (eq_refl (term25 x n)). Qed.
Lemma lem3179217 (x : real) : (term27 x) = (term24 x).
Proof. exact (fun_ext (fun n : int => @lem3179216 x n)). Qed.
Lemma lem3179218 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3179219 (x : real) : (term22 x) = (term28 x).
Proof. exact (MK_COMB (@lem3179218) (@lem3179217 x)). Qed.
Lemma lem3179220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3179221 (x : real) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem3179220) (@lem3179219 x)). Qed.
Lemma lem3179222 (x : real) (n : nat) : (term31 x n) = (term32 x n).
Proof. exact (eq_refl (term31 x n)). Qed.
Lemma lem3179223 (x : real) : (term33 x) = (term34 x).
Proof. exact (fun_ext (fun n : nat => @lem3179222 x n)). Qed.
Lemma lem3179224 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179225 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem3179224) (@lem3179223 x)). Qed.
Lemma lem3179226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3179227 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem3179226) (@lem3179225 x)). Qed.
Lemma lem3179228 (x : real) (n : nat) : (term39 x n) = (term40 x n).
Proof. exact (eq_refl (term39 x n)). Qed.
Lemma lem3179229 (x : real) : (term41 x) = (term42 x).
Proof. exact (fun_ext (fun n : nat => @lem3179228 x n)). Qed.
Lemma lem3179230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179231 (x : real) : (term43 x) = (term44 x).
Proof. exact (MK_COMB (@lem3179230) (@lem3179229 x)). Qed.
Lemma lem3179232 (x : real) : (term23 x) = (term45 x).
Proof. exact (MK_COMB (@lem3179227 x) (@lem3179231 x)). Qed.
Lemma lem3179233 (x : real) : ((term22 x) = (term23 x)) = ((term28 x) = (term45 x)).
Proof. exact (MK_COMB (@lem3179221 x) (@lem3179232 x)). Qed.
Lemma lem3179234 (x : real) : (term28 x) = (term45 x).
Proof. exact (EQ_MP (@lem3179233 x) (@lem3179215 x)). Qed.
Lemma lem3179246 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term46 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3179247 (p : Prop) (q : Prop) (p' : Prop) : term47 p q p'.
Proof. exact (fun q' : Prop => @lem3179246 p q p' q'). Qed.
Lemma lem3179248 (p : Prop) (q : Prop) : term48 p q.
Proof. exact (fun p' : Prop => @lem3179247 p q p'). Qed.
Lemma lem3179249 (x : real) (n : nat) : term49 x n.
Proof. exact (@lem3179248 (term4 x) (term50 x n)). Qed.
Lemma lem3179250 (x : real) (n : nat) (p' : Prop) : term51 x n p'.
Proof. exact (@lem3179249 x n p'). Qed.
Lemma lem3179251 (x : real) (n : nat) (p' : Prop) : (term51 x n p') = (term52 x n p').
Proof. exact (eq_refl (term51 x n p')). Qed.
Lemma lem3179252 (x : real) (n : nat) (p' : Prop) : term52 x n p'.
Proof. exact (EQ_MP (@lem3179251 x n p') (@lem3179250 x n p')). Qed.
Lemma lem3179253 (x : real) (n : nat) (p' : Prop) (q' : Prop) : term53 x n p' q'.
Proof. exact (@lem3179252 x n p' q'). Qed.
Lemma lem3179254 (x : real) (n : nat) (p' : Prop) (q' : Prop) : (term53 x n p' q') = (term54 x n p' q').
Proof. exact (eq_refl (term53 x n p' q')). Qed.
Lemma lem3179255 (x : real) (n : nat) (p' : Prop) (q' : Prop) : term54 x n p' q'.
Proof. exact (EQ_MP (@lem3179254 x n p' q') (@lem3179253 x n p' q')). Qed.
Lemma lem3179256 (x : real) : (term4 x) = (term4 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem3179257 (n : nat) (x : real) (q' : Prop) : term55 n x q'.
Proof. exact (@lem3179255 x n (term4 x) q'). Qed.
Lemma lem3179258 (n : nat) (x : real) (q' : Prop) : term56 n x q'.
Proof. exact (@lem3179257 n x q' (@lem3179256 x)). Qed.
Lemma lem3179259 (x : real) (h1 : term4 x) : term4 x.
Proof. exact (h1). Qed.
Lemma lem3179260 (x : real) : (term4 x) = ((term4 x) = True).
Proof. exact (@lem7 (term4 x)). Qed.
Lemma lem3179263 (x : real) (n : nat) : (term18 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3179198 x n) (@lem3179197 x n)). Qed.
Lemma lem3179264 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem3179265 (x : real) (n : nat) : (term50 x n) = (term5 x n).
Proof. exact (MK_COMB (@lem3179264) (@lem3179263 x n)). Qed.
Lemma lem3179267 (x : real) (n : nat) : term58 x n.
Proof. exact (fun h0 : term4 x => @lem3179177 n x h0). Qed.
Lemma lem3179269 (x : real) (h1 : term4 x) : (term4 x) = True.
Proof. exact (EQ_MP (@lem3179260 x) (@lem3179259 x h1)). Qed.
Lemma lem3179270 (x : real) (h1 : term4 x) : True = (term4 x).
Proof. exact (SYM (@lem3179269 x h1)). Qed.
Lemma lem3179271 (x : real) (h1 : term4 x) : term4 x.
Proof. exact (EQ_MP (@lem3179270 x h1) (@lem0)). Qed.
Lemma lem3179272 (n : nat) (x : real) (h1 : term4 x) : (term5 x n) = True.
Proof. exact (@lem3179267 x n (@lem3179271 x h1)). Qed.
Lemma lem3179273 (n : nat) (x : real) (h1 : term4 x) : (term50 x n) = True.
Proof. exact (TRANS (@lem3179265 x n) (@lem3179272 n x h1)). Qed.
Lemma lem3179274 (x : real) (n : nat) : term59 x n.
Proof. exact (fun h0 : term4 x => @lem3179273 n x h0). Qed.
Lemma lem3179275 (n : nat) (x : real) : term60 n x.
Proof. exact (@lem3179258 n x True). Qed.
Lemma lem3179276 (n : nat) (x : real) : (term32 x n) = (term61 x).
Proof. exact (@lem3179275 n x (@lem3179274 x n)). Qed.
Lemma lem3179278 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3179279 (x : real) : (term61 x) = True.
Proof. exact (@lem3179278 (term4 x)). Qed.
Lemma lem3179280 (x : real) (n : nat) : (term32 x n) = True.
Proof. exact (TRANS (@lem3179276 n x) (@lem3179279 x)). Qed.
Lemma lem3179281 (x : real) : (term34 x) = term62.
Proof. exact (fun_ext (fun n : nat => @lem3179280 x n)). Qed.
Lemma lem3179282 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179283 (x : real) : (term36 x) = term63.
Proof. exact (MK_COMB (@lem3179282) (@lem3179281 x)). Qed.
Lemma lem3179285 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179286 (t : Prop) : (term65 t) = t.
Proof. exact (@lem3179285 nat t). Qed.
Lemma lem3179287 : term63 = True.
Proof. exact (@lem3179286 True). Qed.
Lemma lem3179288 (x : real) : (term36 x) = True.
Proof. exact (TRANS (@lem3179283 x) (@lem3179287)). Qed.
Lemma lem3179289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3179290 (x : real) : (term38 x) = (and True).
Proof. exact (MK_COMB (@lem3179289) (@lem3179288 x)). Qed.
Lemma lem3179300 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term46 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3179301 (p : Prop) (q : Prop) (p' : Prop) : term47 p q p'.
Proof. exact (fun q' : Prop => @lem3179300 p q p' q'). Qed.
Lemma lem3179302 (p : Prop) (q : Prop) : term48 p q.
Proof. exact (fun p' : Prop => @lem3179301 p q p'). Qed.
Lemma lem3179303 (x : real) (n : nat) : term66 x n.
Proof. exact (@lem3179302 (term4 x) (term67 x n)). Qed.
Lemma lem3179304 (x : real) (n : nat) (p' : Prop) : term68 x n p'.
Proof. exact (@lem3179303 x n p'). Qed.
Lemma lem3179305 (x : real) (n : nat) (p' : Prop) : (term68 x n p') = (term69 x n p').
Proof. exact (eq_refl (term68 x n p')). Qed.
Lemma lem3179306 (x : real) (n : nat) (p' : Prop) : term69 x n p'.
Proof. exact (EQ_MP (@lem3179305 x n p') (@lem3179304 x n p')). Qed.
Lemma lem3179307 (x : real) (n : nat) (p' : Prop) (q' : Prop) : term70 x n p' q'.
Proof. exact (@lem3179306 x n p' q'). Qed.
Lemma lem3179308 (x : real) (n : nat) (p' : Prop) (q' : Prop) : (term70 x n p' q') = (term71 x n p' q').
Proof. exact (eq_refl (term70 x n p' q')). Qed.
Lemma lem3179309 (x : real) (n : nat) (p' : Prop) (q' : Prop) : term71 x n p' q'.
Proof. exact (EQ_MP (@lem3179308 x n p' q') (@lem3179307 x n p' q')). Qed.
Lemma lem3179310 (x : real) : (term4 x) = (term4 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem3179311 (n : nat) (x : real) (q' : Prop) : term72 n x q'.
Proof. exact (@lem3179309 x n (term4 x) q'). Qed.
Lemma lem3179312 (n : nat) (x : real) (q' : Prop) : term73 n x q'.
Proof. exact (@lem3179311 n x q' (@lem3179310 x)). Qed.
Lemma lem3179313 (x : real) (h1 : term4 x) : term4 x.
Proof. exact (h1). Qed.
Lemma lem3179314 (x : real) : (term4 x) = ((term4 x) = True).
Proof. exact (@lem7 (term4 x)). Qed.
Lemma lem3179317 (x : real) (n : nat) : (term12 x n) = (term13 x n).
Proof. exact (EQ_MP (@lem3179191 x n) (@lem3179190 x n)). Qed.
Lemma lem3179318 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem3179319 (x : real) (n : nat) : (term67 x n) = (term74 x n).
Proof. exact (MK_COMB (@lem3179318) (@lem3179317 x n)). Qed.
Lemma lem3179321 (x : real) : (term7 x) = (term4 x).
Proof. exact (EQ_MP (@lem3179184 x) (@lem3179183 x)). Qed.
Lemma lem3179322 (x : real) (n : nat) : (term74 x n) = (term5 x n).
Proof. exact (@lem3179321 (real_pow x n)). Qed.
Lemma lem3179324 (x : real) (n : nat) : term58 x n.
Proof. exact (fun h0 : term4 x => @lem3179177 n x h0). Qed.
Lemma lem3179326 (x : real) (h1 : term4 x) : (term4 x) = True.
Proof. exact (EQ_MP (@lem3179314 x) (@lem3179313 x h1)). Qed.
Lemma lem3179327 (x : real) (h1 : term4 x) : True = (term4 x).
Proof. exact (SYM (@lem3179326 x h1)). Qed.
Lemma lem3179328 (x : real) (h1 : term4 x) : term4 x.
Proof. exact (EQ_MP (@lem3179327 x h1) (@lem0)). Qed.
Lemma lem3179329 (n : nat) (x : real) (h1 : term4 x) : (term5 x n) = True.
Proof. exact (@lem3179324 x n (@lem3179328 x h1)). Qed.
Lemma lem3179330 (n : nat) (x : real) (h1 : term4 x) : (term74 x n) = True.
Proof. exact (TRANS (@lem3179322 x n) (@lem3179329 n x h1)). Qed.
Lemma lem3179331 (n : nat) (x : real) (h1 : term4 x) : (term67 x n) = True.
Proof. exact (TRANS (@lem3179319 x n) (@lem3179330 n x h1)). Qed.
Lemma lem3179332 (x : real) (n : nat) : term75 x n.
Proof. exact (fun h0 : term4 x => @lem3179331 n x h0). Qed.
Lemma lem3179333 (n : nat) (x : real) : term76 n x.
Proof. exact (@lem3179312 n x True). Qed.
Lemma lem3179334 (n : nat) (x : real) : (term40 x n) = (term61 x).
Proof. exact (@lem3179333 n x (@lem3179332 x n)). Qed.
Lemma lem3179336 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3179337 (x : real) : (term61 x) = True.
Proof. exact (@lem3179336 (term4 x)). Qed.
Lemma lem3179338 (x : real) (n : nat) : (term40 x n) = True.
Proof. exact (TRANS (@lem3179334 n x) (@lem3179337 x)). Qed.
Lemma lem3179339 (x : real) : (term42 x) = term62.
Proof. exact (fun_ext (fun n : nat => @lem3179338 x n)). Qed.
Lemma lem3179340 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179341 (x : real) : (term44 x) = term63.
Proof. exact (MK_COMB (@lem3179340) (@lem3179339 x)). Qed.
Lemma lem3179343 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179344 (t : Prop) : (term65 t) = t.
Proof. exact (@lem3179343 nat t). Qed.
Lemma lem3179345 : term63 = True.
Proof. exact (@lem3179344 True). Qed.
Lemma lem3179346 (x : real) : (term44 x) = True.
Proof. exact (TRANS (@lem3179341 x) (@lem3179345)). Qed.
Lemma lem3179347 (x : real) : (term45 x) = (True /\ True).
Proof. exact (MK_COMB (@lem3179290 x) (@lem3179346 x)). Qed.
Lemma lem3179349 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3179350 : (True /\ True) = True.
Proof. exact (@lem3179349 True). Qed.
Lemma lem3179351 (x : real) : (term45 x) = True.
Proof. exact (TRANS (@lem3179347 x) (@lem3179350)). Qed.
Lemma lem3179352 (x : real) : (term28 x) = True.
Proof. exact (TRANS (@lem3179234 x) (@lem3179351 x)). Qed.
Lemma lem3179353 : term77 = term78.
Proof. exact (fun_ext (fun x : real => @lem3179352 x)). Qed.
Lemma lem3179354 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3179355 : term79 = term80.
Proof. exact (MK_COMB (@lem3179354) (@lem3179353)). Qed.
Lemma lem3179357 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179358 (t : Prop) : (term81 t) = t.
Proof. exact (@lem3179357 real t). Qed.
Lemma lem3179359 : term80 = True.
Proof. exact (@lem3179358 True). Qed.
Lemma lem3179360 : term79 = True.
Proof. exact (TRANS (@lem3179355) (@lem3179359)). Qed.
Lemma lem3179361 : True = term79.
Proof. exact (SYM (@lem3179360)). Qed.
Lemma lem3179362 : term79.
Proof. exact (EQ_MP (@lem3179361) (@lem0)). Qed.
