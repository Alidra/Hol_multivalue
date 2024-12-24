Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513386_term_abbrevs.
Require Import BIT0_spec.
Require Import BIT1_spec.
Require Import PRE_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Require Import thm75543_spec.
Lemma lem513193 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem513194 : (NUMERAL 0) = 0.
Proof. exact (@lem513193 0). Qed.
Lemma lem513195 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem513196 : term0 = (Nat.pred 0).
Proof. exact (MK_COMB (@lem513195) (@lem513194)). Qed.
Lemma lem513197 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513198 : term1 = term2.
Proof. exact (MK_COMB (@lem513197) (@lem513196)). Qed.
Lemma lem513200 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem513201 : (NUMERAL 0) = 0.
Proof. exact (@lem513200 0). Qed.
Lemma lem513202 : (term0 = (NUMERAL 0)) = ((Nat.pred 0) = 0).
Proof. exact (MK_COMB (@lem513198) (@lem513201)). Qed.
Lemma lem513203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513204 : term3 = term4.
Proof. exact (MK_COMB (@lem513203) (@lem513202)). Qed.
Lemma lem513205 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem513206 : term6 = term7.
Proof. exact (MK_COMB (@lem513204) (@lem513205)). Qed.
Lemma lem513207 : term7.
Proof. exact (EQ_MP (@lem513206) (@lem76888)). Qed.
Lemma lem513208 : term5.
Proof. exact (proj2 (@lem513207)). Qed.
Lemma lem513209 (n : nat) : term8 n.
Proof. exact (@lem513208 n). Qed.
Lemma lem513210 (n : nat) : (term8 n) = ((term9 n) = n).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem513213 (n : nat) : term10 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem513214 (n : nat) : (term10 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem513216 (n : nat) : term11 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem513217 (n : nat) : (term11 n) = ((BIT1 n) = (term12 n)).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem513219 (n : nat) : term13 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem513220 (n : nat) : (term13 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem513231 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem513220 n) (@lem513219 n)). Qed.
Lemma lem513232 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem513233 (n : nat) : (term14 n) = (Nat.pred n).
Proof. exact (MK_COMB (@lem513232) (@lem513231 n)). Qed.
Lemma lem513234 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513235 (n : nat) : (term15 n) = (term16 n).
Proof. exact (MK_COMB (@lem513234) (@lem513233 n)). Qed.
Lemma lem513237 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem513220 n) (@lem513219 n)). Qed.
Lemma lem513238 (n : nat) : (term17 n) = (Nat.pred n).
Proof. exact (@lem513237 (Nat.pred n)). Qed.
Lemma lem513239 (n : nat) : ((term14 n) = (term17 n)) = ((Nat.pred n) = (Nat.pred n)).
Proof. exact (MK_COMB (@lem513235 n) (@lem513238 n)). Qed.
Lemma lem513241 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513242 (x : nat) : (x = x) = True.
Proof. exact (@lem513241 nat x). Qed.
Lemma lem513243 (n : nat) : ((Nat.pred n) = (Nat.pred n)) = True.
Proof. exact (@lem513242 (Nat.pred n)). Qed.
Lemma lem513244 (n : nat) : ((term14 n) = (term17 n)) = True.
Proof. exact (TRANS (@lem513239 n) (@lem513243 n)). Qed.
Lemma lem513245 : term18 = term19.
Proof. exact (fun_ext (fun n : nat => @lem513244 n)). Qed.
Lemma lem513246 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513247 : term20 = term21.
Proof. exact (MK_COMB (@lem513246) (@lem513245)). Qed.
Lemma lem513249 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem513250 (t : Prop) : (term23 t) = t.
Proof. exact (@lem513249 nat t). Qed.
Lemma lem513251 : term21 = True.
Proof. exact (@lem513250 True). Qed.
Lemma lem513252 : term20 = True.
Proof. exact (TRANS (@lem513247) (@lem513251)). Qed.
Lemma lem513253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513254 : term24 = (and True).
Proof. exact (MK_COMB (@lem513253) (@lem513252)). Qed.
Lemma lem513260 : (Nat.pred 0) = 0.
Proof. exact (proj1 (@lem513207)). Qed.
Lemma lem513261 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513262 : term2 = (@eq nat 0).
Proof. exact (MK_COMB (@lem513261) (@lem513260)). Qed.
Lemma lem513263 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem513264 : ((Nat.pred 0) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem513262) (@lem513263)). Qed.
Lemma lem513266 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513267 (x : nat) : (x = x) = True.
Proof. exact (@lem513266 nat x). Qed.
Lemma lem513268 : (0 = 0) = True.
Proof. exact (@lem513267 0). Qed.
Lemma lem513269 : ((Nat.pred 0) = 0) = True.
Proof. exact (TRANS (@lem513264) (@lem513268)). Qed.
Lemma lem513270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513271 : term4 = (and True).
Proof. exact (MK_COMB (@lem513270) (@lem513269)). Qed.
Lemma lem513281 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem513214 n) (@lem513213 n)). Qed.
Lemma lem513282 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem513283 (n : nat) : (term25 n) = (term26 n).
Proof. exact (MK_COMB (@lem513282) (@lem513281 n)). Qed.
Lemma lem513284 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513285 (n : nat) : (term27 n) = (term28 n).
Proof. exact (MK_COMB (@lem513284) (@lem513283 n)). Qed.
Lemma lem513291 (n : nat) : (BIT1 n) = (term12 n).
Proof. exact (EQ_MP (@lem513217 n) (@lem513216 n)). Qed.
Lemma lem513292 (n : nat) : (term29 n) = (term30 n).
Proof. exact (@lem513291 (Nat.pred n)). Qed.
Lemma lem513293 (n : nat) : (term31 n) = (term31 n).
Proof. exact (eq_refl (term31 n)). Qed.
Lemma lem513294 (n : nat) : (term32 n) = (term33 n).
Proof. exact (MK_COMB (@lem513293 n) (@lem513292 n)). Qed.
Lemma lem513297 (n : nat) : ((term25 n) = (term32 n)) = ((term26 n) = (term33 n)).
Proof. exact (MK_COMB (@lem513285 n) (@lem513294 n)). Qed.
Lemma lem513300 : term34 = term35.
Proof. exact (fun_ext (fun n : nat => @lem513297 n)). Qed.
Lemma lem513301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513302 : term36 = term37.
Proof. exact (MK_COMB (@lem513301) (@lem513300)). Qed.
Lemma lem513307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513308 : term38 = term39.
Proof. exact (MK_COMB (@lem513307) (@lem513302)). Qed.
Lemma lem513316 (n : nat) : (BIT1 n) = (term12 n).
Proof. exact (EQ_MP (@lem513217 n) (@lem513216 n)). Qed.
Lemma lem513317 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem513318 (n : nat) : (term40 n) = (term41 n).
Proof. exact (MK_COMB (@lem513317) (@lem513316 n)). Qed.
Lemma lem513320 (n : nat) : (term9 n) = n.
Proof. exact (EQ_MP (@lem513210 n) (@lem513209 n)). Qed.
Lemma lem513321 (n : nat) : (term41 n) = (Nat.add n n).
Proof. exact (@lem513320 (Nat.add n n)). Qed.
Lemma lem513322 (n : nat) : (term40 n) = (Nat.add n n).
Proof. exact (TRANS (@lem513318 n) (@lem513321 n)). Qed.
Lemma lem513323 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513324 (n : nat) : (term42 n) = (term43 n).
Proof. exact (MK_COMB (@lem513323) (@lem513322 n)). Qed.
Lemma lem513326 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem513214 n) (@lem513213 n)). Qed.
Lemma lem513327 (n : nat) : ((term40 n) = (BIT0 n)) = ((Nat.add n n) = (Nat.add n n)).
Proof. exact (MK_COMB (@lem513324 n) (@lem513326 n)). Qed.
Lemma lem513329 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513330 (x : nat) : (x = x) = True.
Proof. exact (@lem513329 nat x). Qed.
Lemma lem513331 (n : nat) : ((Nat.add n n) = (Nat.add n n)) = True.
Proof. exact (@lem513330 (Nat.add n n)). Qed.
Lemma lem513332 (n : nat) : ((term40 n) = (BIT0 n)) = True.
Proof. exact (TRANS (@lem513327 n) (@lem513331 n)). Qed.
Lemma lem513333 : term44 = term19.
Proof. exact (fun_ext (fun n : nat => @lem513332 n)). Qed.
Lemma lem513334 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513335 : term45 = term21.
Proof. exact (MK_COMB (@lem513334) (@lem513333)). Qed.
Lemma lem513337 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem513338 (t : Prop) : (term23 t) = t.
Proof. exact (@lem513337 nat t). Qed.
Lemma lem513339 : term21 = True.
Proof. exact (@lem513338 True). Qed.
Lemma lem513340 : term45 = True.
Proof. exact (TRANS (@lem513335) (@lem513339)). Qed.
Lemma lem513341 : term46 = term47.
Proof. exact (MK_COMB (@lem513308) (@lem513340)). Qed.
Lemma lem513343 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem513344 : term47 = term37.
Proof. exact (@lem513343 term37). Qed.
Lemma lem513355 : term46 = term37.
Proof. exact (TRANS (@lem513341) (@lem513344)). Qed.
Lemma lem513356 : term48 = term49.
Proof. exact (MK_COMB (@lem513271) (@lem513355)). Qed.
Lemma lem513358 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem513359 : term49 = term37.
Proof. exact (@lem513358 term37). Qed.
Lemma lem513370 : term48 = term37.
Proof. exact (TRANS (@lem513356) (@lem513359)). Qed.
Lemma lem513371 : term50 = term49.
Proof. exact (MK_COMB (@lem513254) (@lem513370)). Qed.
Lemma lem513373 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem513374 : term49 = term37.
Proof. exact (@lem513373 term37). Qed.
Lemma lem513385 : term50 = term37.
Proof. exact (TRANS (@lem513371) (@lem513374)). Qed.
Lemma lem513386 : term37 = term50.
Proof. exact (SYM (@lem513385)). Qed.
