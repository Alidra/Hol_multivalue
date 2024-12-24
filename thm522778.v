Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522778_term_abbrevs.
Require Import SUB_0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Require Import thm75543_spec.
Lemma lem522202 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem522203 : (NUMERAL 0) = 0.
Proof. exact (@lem522202 0). Qed.
Lemma lem522204 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem522205 : term0 = (Nat.sub 0).
Proof. exact (MK_COMB (@lem522204) (@lem522203)). Qed.
Lemma lem522206 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem522207 (m : nat) : (term1 m) = (Nat.sub 0 m).
Proof. exact (MK_COMB (@lem522205) (@lem522206 m)). Qed.
Lemma lem522208 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522209 (m : nat) : (term2 m) = (term3 m).
Proof. exact (MK_COMB (@lem522208) (@lem522207 m)). Qed.
Lemma lem522211 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem522212 : (NUMERAL 0) = 0.
Proof. exact (@lem522211 0). Qed.
Lemma lem522213 (m : nat) : ((term1 m) = (NUMERAL 0)) = ((Nat.sub 0 m) = 0).
Proof. exact (MK_COMB (@lem522209 m) (@lem522212)). Qed.
Lemma lem522214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522215 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem522214) (@lem522213 m)). Qed.
Lemma lem522217 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem522218 : (NUMERAL 0) = 0.
Proof. exact (@lem522217 0). Qed.
Lemma lem522219 (m : nat) : (Nat.sub m) = (Nat.sub m).
Proof. exact (eq_refl (Nat.sub m)). Qed.
Lemma lem522220 (m : nat) : (term6 m) = (Nat.sub m 0).
Proof. exact (MK_COMB (@lem522219 m) (@lem522218)). Qed.
Lemma lem522221 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522222 (m : nat) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem522221) (@lem522220 m)). Qed.
Lemma lem522223 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem522224 (m : nat) : ((term6 m) = m) = ((Nat.sub m 0) = m).
Proof. exact (MK_COMB (@lem522222 m) (@lem522223 m)). Qed.
Lemma lem522225 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem522215 m) (@lem522224 m)). Qed.
Lemma lem522226 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem522225 m)). Qed.
Lemma lem522227 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522228 : term13 = term14.
Proof. exact (MK_COMB (@lem522227) (@lem522226)). Qed.
Lemma lem522229 : term14.
Proof. exact (EQ_MP (@lem522228) (@lem135231)). Qed.
Lemma lem522230 (m : nat) : term15 m.
Proof. exact (@lem522229 m). Qed.
Lemma lem522231 (m : nat) : (term15 m) = (term10 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem522232 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem522231 m) (@lem522230 m)). Qed.
Lemma lem522235 (n : nat) : term16 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem522236 (n : nat) : (term16 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem522251 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem522236 n) (@lem522235 n)). Qed.
Lemma lem522252 (m : nat) : (NUMERAL m) = m.
Proof. exact (@lem522251 m). Qed.
Lemma lem522253 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem522254 (m : nat) : (term17 m) = (Nat.sub m).
Proof. exact (MK_COMB (@lem522253) (@lem522252 m)). Qed.
Lemma lem522256 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem522236 n) (@lem522235 n)). Qed.
Lemma lem522257 (m : nat) (n : nat) : (term18 m n) = (Nat.sub m n).
Proof. exact (MK_COMB (@lem522254 m) (@lem522256 n)). Qed.
Lemma lem522258 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522259 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem522258) (@lem522257 m n)). Qed.
Lemma lem522261 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem522236 n) (@lem522235 n)). Qed.
Lemma lem522262 (m : nat) (n : nat) : (term21 m n) = (Nat.sub m n).
Proof. exact (@lem522261 (Nat.sub m n)). Qed.
Lemma lem522263 (m : nat) (n : nat) : ((term18 m n) = (term21 m n)) = ((Nat.sub m n) = (Nat.sub m n)).
Proof. exact (MK_COMB (@lem522259 m n) (@lem522262 m n)). Qed.
Lemma lem522265 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem522266 (x : nat) : (x = x) = True.
Proof. exact (@lem522265 nat x). Qed.
Lemma lem522267 (m : nat) (n : nat) : ((Nat.sub m n) = (Nat.sub m n)) = True.
Proof. exact (@lem522266 (Nat.sub m n)). Qed.
Lemma lem522268 (m : nat) (n : nat) : ((term18 m n) = (term21 m n)) = True.
Proof. exact (TRANS (@lem522263 m n) (@lem522267 m n)). Qed.
Lemma lem522269 (m : nat) : (term22 m) = term23.
Proof. exact (fun_ext (fun n : nat => @lem522268 m n)). Qed.
Lemma lem522270 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522271 (m : nat) : (term24 m) = term25.
Proof. exact (MK_COMB (@lem522270) (@lem522269 m)). Qed.
Lemma lem522273 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem522274 (t : Prop) : (term27 t) = t.
Proof. exact (@lem522273 nat t). Qed.
Lemma lem522275 : term25 = True.
Proof. exact (@lem522274 True). Qed.
Lemma lem522276 (m : nat) : (term24 m) = True.
Proof. exact (TRANS (@lem522271 m) (@lem522275)). Qed.
Lemma lem522277 : term28 = term23.
Proof. exact (fun_ext (fun m : nat => @lem522276 m)). Qed.
Lemma lem522278 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522279 : term29 = term25.
Proof. exact (MK_COMB (@lem522278) (@lem522277)). Qed.
Lemma lem522281 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem522282 (t : Prop) : (term27 t) = t.
Proof. exact (@lem522281 nat t). Qed.
Lemma lem522283 : term25 = True.
Proof. exact (@lem522282 True). Qed.
Lemma lem522284 : term29 = True.
Proof. exact (TRANS (@lem522279) (@lem522283)). Qed.
Lemma lem522285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522286 : term30 = (and True).
Proof. exact (MK_COMB (@lem522285) (@lem522284)). Qed.
Lemma lem522292 (m : nat) : (Nat.sub 0 m) = 0.
Proof. exact (proj1 (@lem522232 m)). Qed.
Lemma lem522293 : (Nat.sub 0 0) = 0.
Proof. exact (@lem522292 0). Qed.
Lemma lem522294 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522295 : term31 = (@eq nat 0).
Proof. exact (MK_COMB (@lem522294) (@lem522293)). Qed.
Lemma lem522296 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem522297 : ((Nat.sub 0 0) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem522295) (@lem522296)). Qed.
Lemma lem522299 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem522300 (x : nat) : (x = x) = True.
Proof. exact (@lem522299 nat x). Qed.
Lemma lem522301 : (0 = 0) = True.
Proof. exact (@lem522300 0). Qed.
Lemma lem522302 : ((Nat.sub 0 0) = 0) = True.
Proof. exact (TRANS (@lem522297) (@lem522301)). Qed.
Lemma lem522303 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522304 : term32 = (and True).
Proof. exact (MK_COMB (@lem522303) (@lem522302)). Qed.
Lemma lem522314 (m : nat) : (Nat.sub 0 m) = 0.
Proof. exact (proj1 (@lem522232 m)). Qed.
Lemma lem522315 (n : nat) : (term33 n) = 0.
Proof. exact (@lem522314 (BIT0 n)). Qed.
Lemma lem522316 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522317 (n : nat) : (term34 n) = (@eq nat 0).
Proof. exact (MK_COMB (@lem522316) (@lem522315 n)). Qed.
Lemma lem522318 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem522319 (n : nat) : ((term33 n) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem522317 n) (@lem522318)). Qed.
Lemma lem522321 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem522322 (x : nat) : (x = x) = True.
Proof. exact (@lem522321 nat x). Qed.
Lemma lem522323 : (0 = 0) = True.
Proof. exact (@lem522322 0). Qed.
Lemma lem522324 (n : nat) : ((term33 n) = 0) = True.
Proof. exact (TRANS (@lem522319 n) (@lem522323)). Qed.
Lemma lem522325 : term35 = term23.
Proof. exact (fun_ext (fun n : nat => @lem522324 n)). Qed.
Lemma lem522326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522327 : term36 = term25.
Proof. exact (MK_COMB (@lem522326) (@lem522325)). Qed.
Lemma lem522329 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem522330 (t : Prop) : (term27 t) = t.
Proof. exact (@lem522329 nat t). Qed.
Lemma lem522331 : term25 = True.
Proof. exact (@lem522330 True). Qed.
Lemma lem522332 : term36 = True.
Proof. exact (TRANS (@lem522327) (@lem522331)). Qed.
Lemma lem522333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522334 : term37 = (and True).
Proof. exact (MK_COMB (@lem522333) (@lem522332)). Qed.
Lemma lem522344 (m : nat) : (Nat.sub 0 m) = 0.
Proof. exact (proj1 (@lem522232 m)). Qed.
Lemma lem522345 (n : nat) : (term38 n) = 0.
Proof. exact (@lem522344 (BIT1 n)). Qed.
Lemma lem522346 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522347 (n : nat) : (term39 n) = (@eq nat 0).
Proof. exact (MK_COMB (@lem522346) (@lem522345 n)). Qed.
Lemma lem522348 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem522349 (n : nat) : ((term38 n) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem522347 n) (@lem522348)). Qed.
Lemma lem522351 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem522352 (x : nat) : (x = x) = True.
Proof. exact (@lem522351 nat x). Qed.
Lemma lem522353 : (0 = 0) = True.
Proof. exact (@lem522352 0). Qed.
Lemma lem522354 (n : nat) : ((term38 n) = 0) = True.
Proof. exact (TRANS (@lem522349 n) (@lem522353)). Qed.
Lemma lem522355 : term40 = term23.
Proof. exact (fun_ext (fun n : nat => @lem522354 n)). Qed.
Lemma lem522356 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522357 : term41 = term25.
Proof. exact (MK_COMB (@lem522356) (@lem522355)). Qed.
Lemma lem522359 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem522360 (t : Prop) : (term27 t) = t.
Proof. exact (@lem522359 nat t). Qed.
Lemma lem522361 : term25 = True.
Proof. exact (@lem522360 True). Qed.
Lemma lem522362 : term41 = True.
Proof. exact (TRANS (@lem522357) (@lem522361)). Qed.
Lemma lem522363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522364 : term42 = (and True).
Proof. exact (MK_COMB (@lem522363) (@lem522362)). Qed.
Lemma lem522374 (m : nat) : (Nat.sub m 0) = m.
Proof. exact (proj2 (@lem522232 m)). Qed.
Lemma lem522375 (n : nat) : (term43 n) = (BIT0 n).
Proof. exact (@lem522374 (BIT0 n)). Qed.
Lemma lem522376 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522377 (n : nat) : (term44 n) = (term45 n).
Proof. exact (MK_COMB (@lem522376) (@lem522375 n)). Qed.
Lemma lem522378 (n : nat) : (BIT0 n) = (BIT0 n).
Proof. exact (eq_refl (BIT0 n)). Qed.
Lemma lem522379 (n : nat) : ((term43 n) = (BIT0 n)) = ((BIT0 n) = (BIT0 n)).
Proof. exact (MK_COMB (@lem522377 n) (@lem522378 n)). Qed.
Lemma lem522381 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem522382 (x : nat) : (x = x) = True.
Proof. exact (@lem522381 nat x). Qed.
Lemma lem522383 (n : nat) : ((BIT0 n) = (BIT0 n)) = True.
Proof. exact (@lem522382 (BIT0 n)). Qed.
Lemma lem522384 (n : nat) : ((term43 n) = (BIT0 n)) = True.
Proof. exact (TRANS (@lem522379 n) (@lem522383 n)). Qed.
Lemma lem522385 : term46 = term23.
Proof. exact (fun_ext (fun n : nat => @lem522384 n)). Qed.
Lemma lem522386 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522387 : term47 = term25.
Proof. exact (MK_COMB (@lem522386) (@lem522385)). Qed.
Lemma lem522389 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem522390 (t : Prop) : (term27 t) = t.
Proof. exact (@lem522389 nat t). Qed.
Lemma lem522391 : term25 = True.
Proof. exact (@lem522390 True). Qed.
Lemma lem522392 : term47 = True.
Proof. exact (TRANS (@lem522387) (@lem522391)). Qed.
Lemma lem522393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522394 : term48 = (and True).
Proof. exact (MK_COMB (@lem522393) (@lem522392)). Qed.
Lemma lem522404 (m : nat) : (Nat.sub m 0) = m.
Proof. exact (proj2 (@lem522232 m)). Qed.
Lemma lem522405 (n : nat) : (term49 n) = (BIT1 n).
Proof. exact (@lem522404 (BIT1 n)). Qed.
Lemma lem522406 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem522407 (n : nat) : (term50 n) = (term51 n).
Proof. exact (MK_COMB (@lem522406) (@lem522405 n)). Qed.
Lemma lem522408 (n : nat) : (BIT1 n) = (BIT1 n).
Proof. exact (eq_refl (BIT1 n)). Qed.
Lemma lem522409 (n : nat) : ((term49 n) = (BIT1 n)) = ((BIT1 n) = (BIT1 n)).
Proof. exact (MK_COMB (@lem522407 n) (@lem522408 n)). Qed.
Lemma lem522411 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem522412 (x : nat) : (x = x) = True.
Proof. exact (@lem522411 nat x). Qed.
Lemma lem522413 (n : nat) : ((BIT1 n) = (BIT1 n)) = True.
Proof. exact (@lem522412 (BIT1 n)). Qed.
Lemma lem522414 (n : nat) : ((term49 n) = (BIT1 n)) = True.
Proof. exact (TRANS (@lem522409 n) (@lem522413 n)). Qed.
Lemma lem522415 : term52 = term23.
Proof. exact (fun_ext (fun n : nat => @lem522414 n)). Qed.
Lemma lem522416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522417 : term53 = term25.
Proof. exact (MK_COMB (@lem522416) (@lem522415)). Qed.
Lemma lem522419 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem522420 (t : Prop) : (term27 t) = t.
Proof. exact (@lem522419 nat t). Qed.
Lemma lem522421 : term25 = True.
Proof. exact (@lem522420 True). Qed.
Lemma lem522422 : term53 = True.
Proof. exact (TRANS (@lem522417) (@lem522421)). Qed.
Lemma lem522423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem522424 : term54 = (and True).
Proof. exact (MK_COMB (@lem522423) (@lem522422)). Qed.
Lemma lem522471 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem522472 : term56 = term57.
Proof. exact (MK_COMB (@lem522424) (@lem522471)). Qed.
Lemma lem522474 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem522475 : term57 = term55.
Proof. exact (@lem522474 term55). Qed.
Lemma lem522522 : term56 = term55.
Proof. exact (TRANS (@lem522472) (@lem522475)). Qed.
Lemma lem522523 : term58 = term57.
Proof. exact (MK_COMB (@lem522394) (@lem522522)). Qed.
Lemma lem522525 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem522526 : term57 = term55.
Proof. exact (@lem522525 term55). Qed.
Lemma lem522573 : term58 = term55.
Proof. exact (TRANS (@lem522523) (@lem522526)). Qed.
Lemma lem522574 : term59 = term57.
Proof. exact (MK_COMB (@lem522364) (@lem522573)). Qed.
Lemma lem522576 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem522577 : term57 = term55.
Proof. exact (@lem522576 term55). Qed.
Lemma lem522624 : term59 = term55.
Proof. exact (TRANS (@lem522574) (@lem522577)). Qed.
Lemma lem522625 : term60 = term57.
Proof. exact (MK_COMB (@lem522334) (@lem522624)). Qed.
Lemma lem522627 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem522628 : term57 = term55.
Proof. exact (@lem522627 term55). Qed.
Lemma lem522675 : term60 = term55.
Proof. exact (TRANS (@lem522625) (@lem522628)). Qed.
Lemma lem522676 : term61 = term57.
Proof. exact (MK_COMB (@lem522304) (@lem522675)). Qed.
Lemma lem522678 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem522679 : term57 = term55.
Proof. exact (@lem522678 term55). Qed.
Lemma lem522726 : term61 = term55.
Proof. exact (TRANS (@lem522676) (@lem522679)). Qed.
Lemma lem522727 : term62 = term57.
Proof. exact (MK_COMB (@lem522286) (@lem522726)). Qed.
Lemma lem522729 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem522730 : term57 = term55.
Proof. exact (@lem522729 term55). Qed.
Lemma lem522777 : term62 = term55.
Proof. exact (TRANS (@lem522727) (@lem522730)). Qed.
Lemma lem522778 : term55 = term62.
Proof. exact (SYM (@lem522777)). Qed.
