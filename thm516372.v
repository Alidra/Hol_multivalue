Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516372_term_abbrevs.
Require Import BIT0_spec.
Require Import BIT1_spec.
Require Import EVEN_spec.
Require Import EVEN_ADD_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Require Import thm75543_spec.
Lemma lem516207 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem516208 : (NUMERAL 0) = 0.
Proof. exact (@lem516207 0). Qed.
Lemma lem516209 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem516210 : term0 = (Coq.Arith.PeanoNat.Nat.Even 0).
Proof. exact (MK_COMB (@lem516209) (@lem516208)). Qed.
Lemma lem516211 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem516212 : term1 = term2.
Proof. exact (MK_COMB (@lem516211) (@lem516210)). Qed.
Lemma lem516213 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem516214 : (term0 = True) = ((Coq.Arith.PeanoNat.Nat.Even 0) = True).
Proof. exact (MK_COMB (@lem516212) (@lem516213)). Qed.
Lemma lem516215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem516216 : term3 = term4.
Proof. exact (MK_COMB (@lem516215) (@lem516214)). Qed.
Lemma lem516217 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem516218 : term6 = term7.
Proof. exact (MK_COMB (@lem516216) (@lem516217)). Qed.
Lemma lem516219 : term7.
Proof. exact (EQ_MP (@lem516218) (@lem124236)). Qed.
Lemma lem516220 (m : nat) : term8 m.
Proof. exact (@lem125496 m). Qed.
Lemma lem516221 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem516222 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem516221 m) (@lem516220 m)). Qed.
Lemma lem516223 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem516222 m n). Qed.
Lemma lem516224 (m : nat) (n : nat) : (term10 m n) = ((term11 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem516226 : term5.
Proof. exact (proj2 (@lem516219)). Qed.
Lemma lem516227 (n : nat) : term12 n.
Proof. exact (@lem516226 n). Qed.
Lemma lem516228 (n : nat) : (term12 n) = ((term13 n) = (term14 n)).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem516231 (n : nat) : term15 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem516232 (n : nat) : (term15 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem516234 (n : nat) : term16 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem516235 (n : nat) : (term16 n) = ((BIT1 n) = (term17 n)).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem516237 (n : nat) : term18 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem516238 (n : nat) : (term18 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem516249 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem516238 n) (@lem516237 n)). Qed.
Lemma lem516250 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem516251 (n : nat) : (term19 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (MK_COMB (@lem516250) (@lem516249 n)). Qed.
Lemma lem516252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem516253 (n : nat) : (term20 n) = (term21 n).
Proof. exact (MK_COMB (@lem516252) (@lem516251 n)). Qed.
Lemma lem516254 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem516255 (n : nat) : ((term19 n) = (Coq.Arith.PeanoNat.Nat.Even n)) = ((Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (MK_COMB (@lem516253 n) (@lem516254 n)). Qed.
Lemma lem516257 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516258 (x : Prop) : (x = x) = True.
Proof. exact (@lem516257 Prop x). Qed.
Lemma lem516259 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n)) = True.
Proof. exact (@lem516258 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem516260 (n : nat) : ((term19 n) = (Coq.Arith.PeanoNat.Nat.Even n)) = True.
Proof. exact (TRANS (@lem516255 n) (@lem516259 n)). Qed.
Lemma lem516261 : term22 = term23.
Proof. exact (fun_ext (fun n : nat => @lem516260 n)). Qed.
Lemma lem516262 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516263 : term24 = term25.
Proof. exact (MK_COMB (@lem516262) (@lem516261)). Qed.
Lemma lem516265 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem516266 (t : Prop) : (term27 t) = t.
Proof. exact (@lem516265 nat t). Qed.
Lemma lem516267 : term25 = True.
Proof. exact (@lem516266 True). Qed.
Lemma lem516268 : term24 = True.
Proof. exact (TRANS (@lem516263) (@lem516267)). Qed.
Lemma lem516269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem516270 : term28 = (and True).
Proof. exact (MK_COMB (@lem516269) (@lem516268)). Qed.
Lemma lem516274 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem516275 : ((Coq.Arith.PeanoNat.Nat.Even 0) = True) = (Coq.Arith.PeanoNat.Nat.Even 0).
Proof. exact (@lem516274 (Coq.Arith.PeanoNat.Nat.Even 0)). Qed.
Lemma lem516277 : (Coq.Arith.PeanoNat.Nat.Even 0) = True.
Proof. exact (proj1 (@lem516219)). Qed.
Lemma lem516278 : ((Coq.Arith.PeanoNat.Nat.Even 0) = True) = True.
Proof. exact (TRANS (@lem516275) (@lem516277)). Qed.
Lemma lem516279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem516280 : term4 = (and True).
Proof. exact (MK_COMB (@lem516279) (@lem516278)). Qed.
Lemma lem516288 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem516289 (n : nat) : ((term29 n) = True) = (term29 n).
Proof. exact (@lem516288 (term29 n)). Qed.
Lemma lem516291 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem516232 n) (@lem516231 n)). Qed.
Lemma lem516292 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem516293 (n : nat) : (term29 n) = (term30 n).
Proof. exact (MK_COMB (@lem516292) (@lem516291 n)). Qed.
Lemma lem516295 (m : nat) (n : nat) : (term11 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem516224 m n) (@lem516223 m n)). Qed.
Lemma lem516296 (n : nat) : (term30 n) = ((Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (@lem516295 n n). Qed.
Lemma lem516298 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516299 (x : Prop) : (x = x) = True.
Proof. exact (@lem516298 Prop x). Qed.
Lemma lem516300 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n)) = True.
Proof. exact (@lem516299 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem516301 (n : nat) : (term30 n) = True.
Proof. exact (TRANS (@lem516296 n) (@lem516300 n)). Qed.
Lemma lem516302 (n : nat) : (term29 n) = True.
Proof. exact (TRANS (@lem516293 n) (@lem516301 n)). Qed.
Lemma lem516303 (n : nat) : ((term29 n) = True) = True.
Proof. exact (TRANS (@lem516289 n) (@lem516302 n)). Qed.
Lemma lem516304 : term31 = term23.
Proof. exact (fun_ext (fun n : nat => @lem516303 n)). Qed.
Lemma lem516305 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516306 : term32 = term25.
Proof. exact (MK_COMB (@lem516305) (@lem516304)). Qed.
Lemma lem516308 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem516309 (t : Prop) : (term27 t) = t.
Proof. exact (@lem516308 nat t). Qed.
Lemma lem516310 : term25 = True.
Proof. exact (@lem516309 True). Qed.
Lemma lem516311 : term32 = True.
Proof. exact (TRANS (@lem516306) (@lem516310)). Qed.
Lemma lem516312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem516313 : term33 = (and True).
Proof. exact (MK_COMB (@lem516312) (@lem516311)). Qed.
Lemma lem516319 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem516320 (n : nat) : ((term34 n) = False) = (term35 n).
Proof. exact (@lem516319 (term34 n)). Qed.
Lemma lem516322 (n : nat) : (BIT1 n) = (term17 n).
Proof. exact (EQ_MP (@lem516235 n) (@lem516234 n)). Qed.
Lemma lem516323 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem516324 (n : nat) : (term34 n) = (term36 n).
Proof. exact (MK_COMB (@lem516323) (@lem516322 n)). Qed.
Lemma lem516326 (n : nat) : (term13 n) = (term14 n).
Proof. exact (EQ_MP (@lem516228 n) (@lem516227 n)). Qed.
Lemma lem516327 (n : nat) : (term36 n) = (term37 n).
Proof. exact (@lem516326 (Nat.add n n)). Qed.
Lemma lem516329 (m : nat) (n : nat) : (term11 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem516224 m n) (@lem516223 m n)). Qed.
Lemma lem516330 (n : nat) : (term30 n) = ((Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (@lem516329 n n). Qed.
Lemma lem516332 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem516333 (x : Prop) : (x = x) = True.
Proof. exact (@lem516332 Prop x). Qed.
Lemma lem516334 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n)) = True.
Proof. exact (@lem516333 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem516335 (n : nat) : (term30 n) = True.
Proof. exact (TRANS (@lem516330 n) (@lem516334 n)). Qed.
Lemma lem516336 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem516337 (n : nat) : (term37 n) = (~ True).
Proof. exact (MK_COMB (@lem516336) (@lem516335 n)). Qed.
Lemma lem516339 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem516340 (n : nat) : (term37 n) = False.
Proof. exact (TRANS (@lem516337 n) (@lem516339)). Qed.
Lemma lem516341 (n : nat) : (term36 n) = False.
Proof. exact (TRANS (@lem516327 n) (@lem516340 n)). Qed.
Lemma lem516342 (n : nat) : (term34 n) = False.
Proof. exact (TRANS (@lem516324 n) (@lem516341 n)). Qed.
Lemma lem516343 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem516344 (n : nat) : (term35 n) = (~ False).
Proof. exact (MK_COMB (@lem516343) (@lem516342 n)). Qed.
Lemma lem516346 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem516347 (n : nat) : (term35 n) = True.
Proof. exact (TRANS (@lem516344 n) (@lem516346)). Qed.
Lemma lem516348 (n : nat) : ((term34 n) = False) = True.
Proof. exact (TRANS (@lem516320 n) (@lem516347 n)). Qed.
Lemma lem516349 : term38 = term23.
Proof. exact (fun_ext (fun n : nat => @lem516348 n)). Qed.
Lemma lem516350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516351 : term39 = term25.
Proof. exact (MK_COMB (@lem516350) (@lem516349)). Qed.
Lemma lem516353 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem516354 (t : Prop) : (term27 t) = t.
Proof. exact (@lem516353 nat t). Qed.
Lemma lem516355 : term25 = True.
Proof. exact (@lem516354 True). Qed.
Lemma lem516356 : term39 = True.
Proof. exact (TRANS (@lem516351) (@lem516355)). Qed.
Lemma lem516357 : term40 = (True /\ True).
Proof. exact (MK_COMB (@lem516313) (@lem516356)). Qed.
Lemma lem516359 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem516360 : (True /\ True) = True.
Proof. exact (@lem516359 True). Qed.
Lemma lem516361 : term40 = True.
Proof. exact (TRANS (@lem516357) (@lem516360)). Qed.
Lemma lem516362 : term41 = (True /\ True).
Proof. exact (MK_COMB (@lem516280) (@lem516361)). Qed.
Lemma lem516364 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem516365 : (True /\ True) = True.
Proof. exact (@lem516364 True). Qed.
Lemma lem516366 : term41 = True.
Proof. exact (TRANS (@lem516362) (@lem516365)). Qed.
Lemma lem516367 : term42 = (True /\ True).
Proof. exact (MK_COMB (@lem516270) (@lem516366)). Qed.
Lemma lem516369 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem516370 : (True /\ True) = True.
Proof. exact (@lem516369 True). Qed.
Lemma lem516371 : term42 = True.
Proof. exact (TRANS (@lem516367) (@lem516370)). Qed.
Lemma lem516372 : True = term42.
Proof. exact (SYM (@lem516371)). Qed.
