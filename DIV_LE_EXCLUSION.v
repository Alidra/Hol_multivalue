Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_LE_EXCLUSION_term_abbrevs.
Require Import ADD1_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LET_TRANS_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_RDIV_EQ_spec.
Require Import LE_REFL_spec.
Require Import LT_MULT_RCANCEL_spec.
Require Import LT_SUC_LE_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16457_spec.
Require Import thm16458_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm7250_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem213260 (m : nat) (h1 : (S m) = (term0 m)) : (S m) = (term0 m).
Proof. exact (h1). Qed.
Lemma lem213261 (m : nat) (h1 : (S m) = (term0 m)) : (term0 m) = (S m).
Proof. exact (SYM (@lem213260 m h1)). Qed.
Lemma lem213262 (m : nat) (h1 : (term0 m) = (S m)) : (term0 m) = (S m).
Proof. exact (h1). Qed.
Lemma lem213263 (m : nat) (h1 : (term0 m) = (S m)) : (S m) = (term0 m).
Proof. exact (SYM (@lem213262 m h1)). Qed.
Lemma lem213264 (m : nat) : ((S m) = (term0 m)) = ((term0 m) = (S m)).
Proof. exact (prop_ext (fun h1 : (S m) = (term0 m) => @lem213261 m h1) (fun h1 : (term0 m) = (S m) => @lem213263 m h1)). Qed.
Lemma lem213265 : term1 = term2.
Proof. exact (fun_ext (fun m : nat => @lem213264 m)). Qed.
Lemma lem213266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213267 : term3 = term4.
Proof. exact (MK_COMB (@lem213266) (@lem213265)). Qed.
Lemma lem213268 : term4.
Proof. exact (EQ_MP (@lem213267) (@lem80621)). Qed.
Lemma lem213269 (m : nat) : term5 m.
Proof. exact (@lem91305 m). Qed.
Lemma lem213270 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem213271 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem213270 m) (@lem213269 m)). Qed.
Lemma lem213272 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem213271 m n). Qed.
Lemma lem213273 (m : nat) (n : nat) : (term7 m n) = ((term8 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem213275 (m : nat) : term9 m.
Proof. exact (@lem213268 m). Qed.
Lemma lem213276 (m : nat) : (term9 m) = ((term0 m) = (S m)).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem213278 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (h1 : term10 A C B D) : term10 A C B D.
Proof. exact (h1). Qed.
Lemma lem213279 (B : Prop) (A : Prop) (C : Prop) (D : Prop) (h1 : term11 B A C D) : term11 B A C D.
Proof. exact (h1). Qed.
Lemma lem213280 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (h1 : term11 B A C D) (h2 : term10 A C B D) : term12 A C B D.
Proof. exact (@lem213278 A C B D h2 (@lem213279 B A C D h1)). Qed.
Lemma lem213281 (B : Prop) (A : Prop) (C : Prop) (D : Prop) (h1 : term11 B A C D) : term13 A C B D.
Proof. exact (fun h0 : term10 A C B D => @lem213280 A C B D h1 h0). Qed.
Lemma lem213282 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (h1 : term10 A C B D) : term10 A C B D.
Proof. exact (h1). Qed.
Lemma lem213283 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (h1 : term11 B A C D) (h2 : term10 A C B D) : term12 A C B D.
Proof. exact (@lem213281 B A C D h1 (@lem213282 A C B D h2)). Qed.
Lemma lem213284 (A : Prop) (C : Prop) (B : Prop) (D : Prop) (h1 : term10 A C B D) : term10 A C B D.
Proof. exact (fun h0 : term11 B A C D => @lem213283 A C B D h0 h1). Qed.
Lemma lem213285 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term14 A C B D.
Proof. exact (fun h0 : term10 A C B D => @lem213284 A C B D h0). Qed.
Lemma lem213287 (t1 : Prop) : term15 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem213288 (t1 : Prop) : (term15 t1) = (term16 t1).
Proof. exact (eq_refl (term15 t1)). Qed.
Lemma lem213289 (t1 : Prop) : term16 t1.
Proof. exact (EQ_MP (@lem213288 t1) (@lem213287 t1)). Qed.
Lemma lem213290 (t1 : Prop) (t2 : Prop) : term17 t1 t2.
Proof. exact (@lem213289 t1 t2). Qed.
Lemma lem213291 (t1 : Prop) (t2 : Prop) : (term17 t1 t2) = (term18 t1 t2).
Proof. exact (eq_refl (term17 t1 t2)). Qed.
Lemma lem213292 (t1 : Prop) (t2 : Prop) : term18 t1 t2.
Proof. exact (EQ_MP (@lem213291 t1 t2) (@lem213290 t1 t2)). Qed.
Lemma lem213293 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term19 t1 t2 t3.
Proof. exact (@lem213292 t1 t2 t3). Qed.
Lemma lem213294 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term19 t1 t2 t3) = ((term20 t1 t2 t3) = (term21 t1 t2 t3)).
Proof. exact (eq_refl (term19 t1 t2 t3)). Qed.
Lemma lem213295 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term20 t1 t2 t3) = (term21 t1 t2 t3).
Proof. exact (EQ_MP (@lem213294 t1 t2 t3) (@lem213293 t1 t2 t3)). Qed.
Lemma lem213296 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term21 t1 t2 t3) = (term20 t1 t2 t3).
Proof. exact (SYM (@lem213295 t1 t2 t3)). Qed.
Lemma lem213297 (n : nat) (m : nat) : term22 n m.
Proof. exact (fun p : nat => @lem83517 n m p). Qed.
Lemma lem213298 (n : nat) : term23 n.
Proof. exact (fun m : nat => @lem213297 n m). Qed.
Lemma lem213299 : term24.
Proof. exact (fun n : nat => @lem213298 n). Qed.
Lemma lem213311 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem213312 (a : nat) (b : nat) : (term26 a b) = (term27 a b).
Proof. exact (@lem213311 (term26 a b)). Qed.
Lemma lem213313 (a : nat) (b : nat) : (term27 a b) = (term26 a b).
Proof. exact (SYM (@lem213312 a b)). Qed.
Lemma lem213314 (a : nat) (b : nat) (h1 : term28 a b) : term28 a b.
Proof. exact (h1). Qed.
Lemma lem213317 (a : nat) (b : nat) (h1 : term29 a b) : term29 a b.
Proof. exact (h1). Qed.
Lemma lem213318 (a : nat) (b : nat) : term30 a b.
Proof. exact (fun h0 : term29 a b => @lem213317 a b h0). Qed.
Lemma lem213319 (a : nat) (b : nat) (h1 : term30 a b) : term30 a b.
Proof. exact (h1). Qed.
Lemma lem213320 (a : nat) (b : nat) (h1 : term29 a b) : term29 a b.
Proof. exact (h1). Qed.
Lemma lem213321 (a : nat) (b : nat) (h1 : term29 a b) (h2 : term30 a b) : term29 a b.
Proof. exact (@lem213319 a b h2 (@lem213320 a b h1)). Qed.
Lemma lem213322 (a : nat) (b : nat) (h1 : term29 a b) : term31 a b.
Proof. exact (fun h0 : term30 a b => @lem213321 a b h1 h0). Qed.
Lemma lem213323 (a : nat) (b : nat) (h1 : term30 a b) : term30 a b.
Proof. exact (h1). Qed.
Lemma lem213324 (a : nat) (b : nat) (h1 : term29 a b) (h2 : term30 a b) : term29 a b.
Proof. exact (@lem213322 a b h1 (@lem213323 a b h2)). Qed.
Lemma lem213325 (a : nat) (b : nat) (h1 : term30 a b) : term30 a b.
Proof. exact (fun h0 : term29 a b => @lem213324 a b h0 h1). Qed.
Lemma lem213326 (a : nat) (b : nat) : term32 a b.
Proof. exact (fun h0 : term30 a b => @lem213325 a b h0). Qed.
Lemma lem213329 (a : nat) (b : nat) : term30 a b.
Proof. exact (@lem213326 a b (@lem213318 a b)). Qed.
Lemma lem213349 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem213350 : term33 = term34.
Proof. exact (@lem213349 term35). Qed.
Lemma lem213355 (a : nat) (b : nat) : (term36 a b) = (term36 a b).
Proof. exact (eq_refl (term36 a b)). Qed.
Lemma lem213356 (a : nat) (b : nat) : (term29 a b) = (term37 a b).
Proof. exact (MK_COMB (@lem213355 a b) (@lem213350)). Qed.
Lemma lem213359 (b : nat) : (term38 b) = (term39 b).
Proof. exact (fun_ext (fun a : nat => @lem213356 a b)). Qed.
Lemma lem213360 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213361 (b : nat) : (term40 b) = (term41 b).
Proof. exact (MK_COMB (@lem213360) (@lem213359 b)). Qed.
Lemma lem213366 : term42 = term43.
Proof. exact (fun_ext (fun b : nat => @lem213361 b)). Qed.
Lemma lem213367 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213376 : term44 = term45.
Proof. exact (MK_COMB (@lem213367) (@lem213366)). Qed.
Lemma lem213377 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem213378 : term46 = term46.
Proof. exact (fun_ext (fun n : nat => @lem213377 n)). Qed.
Lemma lem213379 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213380 : term35 = term35.
Proof. exact (MK_COMB (@lem213379) (@lem213378)). Qed.
Lemma lem213381 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem213382 : term34 = term34.
Proof. exact (MK_COMB (@lem213381) (@lem213380)). Qed.
Lemma lem213383 (a : nat) (b : nat) : (Peano.le a b) = (Peano.le a b).
Proof. exact (eq_refl (Peano.le a b)). Qed.
Lemma lem213388 (a : nat) (k : nat) (b : nat) : (term47 a k b) = (term47 a k b).
Proof. exact (eq_refl (term47 a k b)). Qed.
Lemma lem213389 (a : nat) (b : nat) : (term48 a b) = (term48 a b).
Proof. exact (fun_ext (fun k : nat => @lem213388 a k b)). Qed.
Lemma lem213390 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213391 (a : nat) (b : nat) : (term49 a b) = (term49 a b).
Proof. exact (MK_COMB (@lem213390) (@lem213389 a b)). Qed.
Lemma lem213392 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem213393 (a : nat) (b : nat) : (term50 a b) = (term50 a b).
Proof. exact (MK_COMB (@lem213392) (@lem213391 a b)). Qed.
Lemma lem213394 (a : nat) (b : nat) : (term26 a b) = (term26 a b).
Proof. exact (MK_COMB (@lem213393 a b) (@lem213383 a b)). Qed.
Lemma lem213395 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem213396 (a : nat) (b : nat) : (term28 a b) = (term28 a b).
Proof. exact (MK_COMB (@lem213395) (@lem213394 a b)). Qed.
Lemma lem213397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem213398 (a : nat) (b : nat) : (term36 a b) = (term36 a b).
Proof. exact (MK_COMB (@lem213397) (@lem213396 a b)). Qed.
Lemma lem213399 (a : nat) (b : nat) : (term37 a b) = (term37 a b).
Proof. exact (MK_COMB (@lem213398 a b) (@lem213382)). Qed.
Lemma lem213400 (b : nat) : (term39 b) = (term39 b).
Proof. exact (fun_ext (fun a : nat => @lem213399 a b)). Qed.
Lemma lem213401 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213402 (b : nat) : (term41 b) = (term41 b).
Proof. exact (MK_COMB (@lem213401) (@lem213400 b)). Qed.
Lemma lem213403 : term43 = term43.
Proof. exact (fun_ext (fun b : nat => @lem213402 b)). Qed.
Lemma lem213404 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213405 : term45 = term45.
Proof. exact (MK_COMB (@lem213404) (@lem213403)). Qed.
Lemma lem213438 : term44 = term45.
Proof. exact (TRANS (@lem213376) (@lem213405)). Qed.
Lemma lem213439 : term45 = term44.
Proof. exact (SYM (@lem213438)). Qed.
Lemma lem213440 (a : nat) (b : nat) (h1 : term28 a b) : term28 a b.
Proof. exact (h1). Qed.
Lemma lem213441 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem213448 (a : nat) (k : nat) (b : nat) : (term47 a k b) = (term51 a k b).
Proof. exact (@lem17265 (Peano.le k a) (Peano.le k b)). Qed.
Lemma lem213449 (a : nat) (b : nat) : (term48 a b) = (term52 a b).
Proof. exact (fun_ext (fun k : nat => @lem213448 a k b)). Qed.
Lemma lem213450 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213451 (a : nat) (b : nat) : (term49 a b) = (term53 a b).
Proof. exact (MK_COMB (@lem213450) (@lem213449 a b)). Qed.
Lemma lem213452 (a : nat) (b : nat) : (term54 a b) = (term54 a b).
Proof. exact (eq_refl (term54 a b)). Qed.
Lemma lem213453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem213454 (a : nat) (b : nat) : (term55 a b) = (term56 a b).
Proof. exact (MK_COMB (@lem213453) (@lem213451 a b)). Qed.
Lemma lem213455 (a : nat) (b : nat) : (term57 a b) = (term58 a b).
Proof. exact (MK_COMB (@lem213454 a b) (@lem213452 a b)). Qed.
Lemma lem213456 (a : nat) (b : nat) : (term28 a b) = (term57 a b).
Proof. exact (@lem17362 (term49 a b) (Peano.le a b)). Qed.
Lemma lem213509 (a : nat) (b : nat) : (term28 a b) = (term58 a b).
Proof. exact (TRANS (@lem213456 a b) (@lem213455 a b)). Qed.
Lemma lem213510 (a : nat) (b : nat) (h1 : term28 a b) : term58 a b.
Proof. exact (EQ_MP (@lem213509 a b) (@lem213440 a b h1)). Qed.
Lemma lem213511 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem213512 : term46 = term46.
Proof. exact (fun_ext (fun n : nat => @lem213511 n)). Qed.
Lemma lem213513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213522 : term35 = term35.
Proof. exact (MK_COMB (@lem213513) (@lem213512)). Qed.
Lemma lem213523 (h1 : term35) : term35.
Proof. exact (EQ_MP (@lem213522) (@lem213441 h1)). Qed.
Lemma lem213530 (a : nat) (b : nat) : (term54 a b) = (term54 a b).
Proof. exact (eq_refl (term54 a b)). Qed.
Lemma lem213545 (a : nat) (k : nat) (b : nat) : (term51 a k b) = (term51 a k b).
Proof. exact (eq_refl (term51 a k b)). Qed.
Lemma lem213546 (a : nat) (b : nat) : (term52 a b) = (term52 a b).
Proof. exact (fun_ext (fun k : nat => @lem213545 a k b)). Qed.
Lemma lem213547 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213548 (a : nat) (b : nat) : (term53 a b) = (term53 a b).
Proof. exact (MK_COMB (@lem213547) (@lem213546 a b)). Qed.
Lemma lem213549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem213550 (a : nat) (b : nat) : (term56 a b) = (term56 a b).
Proof. exact (MK_COMB (@lem213549) (@lem213548 a b)). Qed.
Lemma lem213551 (a : nat) (b : nat) : (term58 a b) = (term58 a b).
Proof. exact (MK_COMB (@lem213550 a b) (@lem213530 a b)). Qed.
Lemma lem213552 (a : nat) (b : nat) (h1 : term28 a b) : term58 a b.
Proof. exact (EQ_MP (@lem213551 a b) (@lem213510 a b h1)). Qed.
Lemma lem213557 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem213558 : term46 = term46.
Proof. exact (fun_ext (fun n : nat => @lem213557 n)). Qed.
Lemma lem213559 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213560 : term35 = term35.
Proof. exact (MK_COMB (@lem213559) (@lem213558)). Qed.
Lemma lem213561 (h1 : term35) : term35.
Proof. exact (EQ_MP (@lem213560) (@lem213523 h1)). Qed.
Lemma lem213563 (a : nat) (b : nat) (h1 : term28 a b) : term53 a b.
Proof. exact (proj1 (@lem213552 a b h1)). Qed.
Lemma lem213565 (n : nat) : (Peano.le n n) = (Peano.le n n).
Proof. exact (eq_refl (Peano.le n n)). Qed.
Lemma lem213566 : term46 = term46.
Proof. exact (fun_ext (fun n : nat => @lem213565 n)). Qed.
Lemma lem213567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213569 : term35 = term35.
Proof. exact (MK_COMB (@lem213567) (@lem213566)). Qed.
Lemma lem213570 (h1 : term35) : term35.
Proof. exact (EQ_MP (@lem213569) (@lem213561 h1)). Qed.
Lemma lem213578 (a : nat) (k : nat) (b : nat) : (term51 a k b) = (term51 a k b).
Proof. exact (eq_refl (term51 a k b)). Qed.
Lemma lem213579 (a : nat) (b : nat) : (term52 a b) = (term52 a b).
Proof. exact (fun_ext (fun k : nat => @lem213578 a k b)). Qed.
Lemma lem213580 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213582 (a : nat) (b : nat) : (term53 a b) = (term53 a b).
Proof. exact (MK_COMB (@lem213580) (@lem213579 a b)). Qed.
Lemma lem213583 (a : nat) (b : nat) (h1 : term28 a b) : term53 a b.
Proof. exact (EQ_MP (@lem213582 a b) (@lem213563 a b h1)). Qed.
Lemma lem213588 (_4323 : nat) (h1 : term35) : term59 _4323.
Proof. exact (@lem213570 h1 _4323). Qed.
Lemma lem213589 (_4323 : nat) : (term59 _4323) = (Peano.le _4323 _4323).
Proof. exact (eq_refl (term59 _4323)). Qed.
Lemma lem213591 (_4324 : nat) (a : nat) (b : nat) (h1 : term28 a b) : term60 a b _4324.
Proof. exact (@lem213583 a b h1 _4324). Qed.
Lemma lem213592 (a : nat) (_4324 : nat) (b : nat) : (term60 a b _4324) = (term51 a _4324 b).
Proof. exact (eq_refl (term60 a b _4324)). Qed.
Lemma lem213601 (_4324 : nat) (a : nat) (b : nat) (h1 : term28 a b) : term51 a _4324 b.
Proof. exact (EQ_MP (@lem213592 a _4324 b) (@lem213591 _4324 a b h1)). Qed.
Lemma lem213603 (a : nat) (b : nat) (h1 : term28 a b) : term54 a b.
Proof. exact (proj2 (@lem213552 a b h1)). Qed.
Lemma lem213605 (_4323 : nat) (h1 : term35) : Peano.le _4323 _4323.
Proof. exact (EQ_MP (@lem213589 _4323) (@lem213588 _4323 h1)). Qed.
Lemma lem213606 (a : nat) (h1 : term35) : Peano.le a a.
Proof. exact (@lem213605 a h1). Qed.
Lemma lem213607 (a : nat) (h1 : term35) : term61 a.
Proof. exact (fun h0 : term62 a => @lem213606 a h1). Qed.
Lemma lem213609 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem213610 (a : nat) : (term61 a) = (Peano.le a a).
Proof. exact (@lem213609 (Peano.le a a)). Qed.
Lemma lem213611 (a : nat) (h1 : term35) : Peano.le a a.
Proof. exact (EQ_MP (@lem213610 a) (@lem213607 a h1)). Qed.
Lemma lem213617 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem213618 (b : nat) (_4324 : nat) (a : nat) : (term51 a _4324 b) = (term64 b _4324 a).
Proof. exact (@lem213617 (Peano.le _4324 b) (term54 _4324 a)). Qed.
Lemma lem213624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem213625 (b : nat) (_4324 : nat) (a : nat) : (term65 a _4324 b) = (term66 b _4324 a).
Proof. exact (MK_COMB (@lem213624) (@lem213618 b _4324 a)). Qed.
Lemma lem213631 (b : nat) (_4324 : nat) (a : nat) : (term64 b _4324 a) = (term64 b _4324 a).
Proof. exact (eq_refl (term64 b _4324 a)). Qed.
Lemma lem213632 (b : nat) (_4324 : nat) (a : nat) : ((term51 a _4324 b) = (term64 b _4324 a)) = ((term64 b _4324 a) = (term64 b _4324 a)).
Proof. exact (MK_COMB (@lem213625 b _4324 a) (@lem213631 b _4324 a)). Qed.
Lemma lem213634 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem213635 (x : Prop) : (x = x) = True.
Proof. exact (@lem213634 Prop x). Qed.
Lemma lem213636 (b : nat) (_4324 : nat) (a : nat) : ((term64 b _4324 a) = (term64 b _4324 a)) = True.
Proof. exact (@lem213635 (term64 b _4324 a)). Qed.
Lemma lem213637 (b : nat) (_4324 : nat) (a : nat) : ((term51 a _4324 b) = (term64 b _4324 a)) = True.
Proof. exact (TRANS (@lem213632 b _4324 a) (@lem213636 b _4324 a)). Qed.
Lemma lem213638 (b : nat) (_4324 : nat) (a : nat) : True = ((term51 a _4324 b) = (term64 b _4324 a)).
Proof. exact (SYM (@lem213637 b _4324 a)). Qed.
Lemma lem213639 (b : nat) (_4324 : nat) (a : nat) : (term51 a _4324 b) = (term64 b _4324 a).
Proof. exact (EQ_MP (@lem213638 b _4324 a) (@lem0)). Qed.
Lemma lem213640 (_4324 : nat) (a : nat) (b : nat) (h1 : term28 a b) : term64 b _4324 a.
Proof. exact (EQ_MP (@lem213639 b _4324 a) (@lem213601 _4324 a b h1)). Qed.
Lemma lem213642 (b : Prop) (a : Prop) : (a \/ b) = (term67 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem213643 (a : nat) (_4324 : nat) (b : nat) : (term64 b _4324 a) = (term68 a _4324 b).
Proof. exact (@lem213642 (term54 _4324 a) (Peano.le _4324 b)). Qed.
Lemma lem213645 (a : Prop) : (term69 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem213646 (_4324 : nat) (a : nat) : (term70 _4324 a) = (Peano.le _4324 a).
Proof. exact (@lem213645 (Peano.le _4324 a)). Qed.
Lemma lem213647 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem213648 (_4324 : nat) (a : nat) : (term71 _4324 a) = (term72 _4324 a).
Proof. exact (MK_COMB (@lem213647) (@lem213646 _4324 a)). Qed.
Lemma lem213649 (_4324 : nat) (b : nat) : (Peano.le _4324 b) = (Peano.le _4324 b).
Proof. exact (eq_refl (Peano.le _4324 b)). Qed.
Lemma lem213650 (a : nat) (_4324 : nat) (b : nat) : (term68 a _4324 b) = (term47 a _4324 b).
Proof. exact (MK_COMB (@lem213648 _4324 a) (@lem213649 _4324 b)). Qed.
Lemma lem213651 (a : nat) (_4324 : nat) (b : nat) : (term64 b _4324 a) = (term47 a _4324 b).
Proof. exact (TRANS (@lem213643 a _4324 b) (@lem213650 a _4324 b)). Qed.
Lemma lem213654 (_4324 : nat) (a : nat) (b : nat) (h1 : term28 a b) : term47 a _4324 b.
Proof. exact (EQ_MP (@lem213651 a _4324 b) (@lem213640 _4324 a b h1)). Qed.
Lemma lem213655 (a : nat) (b : nat) (h1 : term28 a b) : term73 a b.
Proof. exact (@lem213654 a a b h1). Qed.
Lemma lem213658 (a : nat) (b : nat) (h1 : term35) (h2 : term28 a b) : Peano.le a b.
Proof. exact (@lem213655 a b h2 (@lem213611 a h1)). Qed.
Lemma lem213659 (a : nat) (b : nat) (h1 : term35) (h2 : term28 a b) : term74 a b.
Proof. exact (fun h0 : term54 a b => @lem213658 a b h1 h2). Qed.
Lemma lem213661 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem213662 (a : nat) (b : nat) : (term74 a b) = (Peano.le a b).
Proof. exact (@lem213661 (Peano.le a b)). Qed.
Lemma lem213663 (a : nat) (b : nat) (h1 : term35) (h2 : term28 a b) : Peano.le a b.
Proof. exact (EQ_MP (@lem213662 a b) (@lem213659 a b h1 h2)). Qed.
Lemma lem213666 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem213668 (a : nat) (b : nat) : (term54 a b) = (term75 a b).
Proof. exact (@lem213666 (Peano.le a b)). Qed.
Lemma lem213671 (a : nat) (b : nat) (h1 : term28 a b) : term75 a b.
Proof. exact (EQ_MP (@lem213668 a b) (@lem213603 a b h1)). Qed.
Lemma lem213674 (a : nat) (b : nat) (h1 : term35) (h2 : term28 a b) : False.
Proof. exact (@lem213671 a b h2 (@lem213663 a b h1 h2)). Qed.
Lemma lem213675 (a : nat) (b : nat) (h1 : term35) (h2 : term28 a b) : term76.
Proof. exact (fun h0 : ~ False => @lem213674 a b h1 h2). Qed.
Lemma lem213677 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem213678 : term76 = False.
Proof. exact (@lem213677 False). Qed.
Lemma lem213679 (a : nat) (b : nat) (h1 : term35) (h2 : term28 a b) : False.
Proof. exact (EQ_MP (@lem213678) (@lem213675 a b h1 h2)). Qed.
Lemma lem213680 (a : nat) (b : nat) (h1 : term35) (h2 : term28 a b) : term35 = False.
Proof. exact (prop_ext (fun h3 : term35 => @lem213679 a b h1 h2) (fun h3 : False => @lem213570 h1)). Qed.
Lemma lem213681 (a : nat) (b : nat) (h1 : term35) (h2 : term28 a b) : False.
Proof. exact (EQ_MP (@lem213680 a b h1 h2) (@lem213570 h1)). Qed.
Lemma lem213682 (a : nat) (b : nat) (h1 : term35) (h2 : term28 a b) : term35 = False.
Proof. exact (prop_ext (fun h3 : term35 => @lem213681 a b h1 h2) (fun h3 : False => @lem213561 h1)). Qed.
Lemma lem213683 (a : nat) (b : nat) (h1 : term35) (h2 : term28 a b) : False.
Proof. exact (EQ_MP (@lem213682 a b h1 h2) (@lem213561 h1)). Qed.
Lemma lem213684 (a : nat) (b : nat) (h1 : term35) (h2 : term28 a b) : term35 = False.
Proof. exact (prop_ext (fun h3 : term35 => @lem213683 a b h1 h2) (fun h3 : False => @lem213523 h1)). Qed.
Lemma lem213685 (a : nat) (b : nat) (h1 : term35) (h2 : term28 a b) : False.
Proof. exact (EQ_MP (@lem213684 a b h1 h2) (@lem213523 h1)). Qed.
Lemma lem213686 (a : nat) (b : nat) (h1 : term28 a b) : term33.
Proof. exact (fun h0 : term35 => @lem213685 a b h0 h1). Qed.
Lemma lem213687 : term33 = term34.
Proof. exact (@lem69 term35). Qed.
Lemma lem213688 (a : nat) (b : nat) (h1 : term28 a b) : term34.
Proof. exact (EQ_MP (@lem213687) (@lem213686 a b h1)). Qed.
Lemma lem213689 (a : nat) (b : nat) : term37 a b.
Proof. exact (fun h0 : term28 a b => @lem213688 a b h0). Qed.
Lemma lem213694 (b : nat) : term41 b.
Proof. exact (fun a : nat => @lem213689 a b). Qed.
Lemma lem213699 : term45.
Proof. exact (fun b : nat => @lem213694 b). Qed.
Lemma lem213700 : term44.
Proof. exact (EQ_MP (@lem213439) (@lem213699)). Qed.
Lemma lem213701 (b : nat) : term77 b.
Proof. exact (@lem213700 b). Qed.
Lemma lem213702 (b : nat) : (term77 b) = (term40 b).
Proof. exact (eq_refl (term77 b)). Qed.
Lemma lem213703 (b : nat) : term40 b.
Proof. exact (EQ_MP (@lem213702 b) (@lem213701 b)). Qed.
Lemma lem213704 (b : nat) (a : nat) : term78 b a.
Proof. exact (@lem213703 b a). Qed.
Lemma lem213705 (a : nat) (b : nat) : (term78 b a) = (term29 a b).
Proof. exact (eq_refl (term78 b a)). Qed.
Lemma lem213706 (a : nat) (b : nat) : term29 a b.
Proof. exact (EQ_MP (@lem213705 a b) (@lem213704 b a)). Qed.
Lemma lem213708 (a : nat) (b : nat) : term29 a b.
Proof. exact (@lem213329 a b (@lem213706 a b)). Qed.
Lemma lem213709 (a : nat) (b : nat) (h1 : term28 a b) : term33.
Proof. exact (@lem213708 a b (@lem213314 a b h1)). Qed.
Lemma lem213710 (a : nat) (b : nat) (h1 : term28 a b) : False.
Proof. exact (@lem213709 a b h1 (@lem91603)). Qed.
Lemma lem213711 (a : nat) (b : nat) (h1 : term28 a b) : (term28 a b) = False.
Proof. exact (prop_ext (fun h2 : term28 a b => @lem213710 a b h1) (fun h2 : False => @lem213314 a b h1)). Qed.
Lemma lem213712 (a : nat) (b : nat) (h1 : term28 a b) : False.
Proof. exact (EQ_MP (@lem213711 a b h1) (@lem213314 a b h1)). Qed.
Lemma lem213713 (a : nat) (b : nat) : term27 a b.
Proof. exact (fun h0 : term28 a b => @lem213712 a b h0). Qed.
Lemma lem213714 (a : nat) (b : nat) : term26 a b.
Proof. exact (EQ_MP (@lem213313 a b) (@lem213713 a b)). Qed.
Lemma lem213715 (a : nat) (b : nat) (h1 : term26 a b) : term26 a b.
Proof. exact (h1). Qed.
Lemma lem213716 (a : nat) (b : nat) (h1 : term49 a b) : term49 a b.
Proof. exact (h1). Qed.
Lemma lem213717 (a : nat) (b : nat) (h1 : term49 a b) (h2 : term26 a b) : Peano.le a b.
Proof. exact (@lem213715 a b h2 (@lem213716 a b h1)). Qed.
Lemma lem213718 (a : nat) (b : nat) (h1 : term49 a b) : term79 a b.
Proof. exact (fun h0 : term26 a b => @lem213717 a b h1 h0). Qed.
Lemma lem213719 (a : nat) (b : nat) (h1 : term26 a b) : term26 a b.
Proof. exact (h1). Qed.
Lemma lem213720 (a : nat) (b : nat) (h1 : term49 a b) (h2 : term26 a b) : Peano.le a b.
Proof. exact (@lem213718 a b h1 (@lem213719 a b h2)). Qed.
Lemma lem213721 (a : nat) (b : nat) (h1 : term26 a b) : term26 a b.
Proof. exact (fun h0 : term49 a b => @lem213720 a b h0 h1). Qed.
Lemma lem213722 (a : nat) (b : nat) : term80 a b.
Proof. exact (fun h0 : term26 a b => @lem213721 a b h0). Qed.
Lemma lem213724 (d : nat) : term81 d.
Proof. exact (@lem9784 (d = (NUMERAL 0))). Qed.
Lemma lem213725 (d : nat) : (term81 d) = (term82 d).
Proof. exact (eq_refl (term81 d)). Qed.
Lemma lem213726 (d : nat) : term82 d.
Proof. exact (EQ_MP (@lem213725 d) (@lem213724 d)). Qed.
Lemma lem213728 (d : nat) (h1 : term83 d) : term83 d.
Proof. exact (h1). Qed.
Lemma lem213736 : term84.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem213737 (m : nat) : term85 m.
Proof. exact (@lem213736 m). Qed.
Lemma lem213738 (m : nat) : (term85 m) = ((term86 m) = False).
Proof. exact (eq_refl (term85 m)). Qed.
Lemma lem213740 : term87.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem213766 : term88.
Proof. exact (proj1 (@lem213740)). Qed.
Lemma lem213767 (m : nat) : term89 m.
Proof. exact (@lem213766 m). Qed.
Lemma lem213768 (m : nat) : (term89 m) = ((term90 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term89 m)). Qed.
Lemma lem213781 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem213782 (a : nat) : (term91 a) = (term91 a).
Proof. exact (eq_refl (term91 a)). Qed.
Lemma lem213783 (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term92 a d) = (term93 a).
Proof. exact (MK_COMB (@lem213782 a) (@lem213781 d h1)). Qed.
Lemma lem213785 (m : nat) : (term90 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem213768 m) (@lem213767 m)). Qed.
Lemma lem213786 (a : nat) : (term93 a) = (NUMERAL 0).
Proof. exact (@lem213785 (term0 a)). Qed.
Lemma lem213787 (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term92 a d) = (NUMERAL 0).
Proof. exact (TRANS (@lem213783 a d h1) (@lem213786 a)). Qed.
Lemma lem213788 (b : nat) (c : nat) : (term94 b c) = (term94 b c).
Proof. exact (eq_refl (term94 b c)). Qed.
Lemma lem213789 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term95 b c a d) = (term96 b c).
Proof. exact (MK_COMB (@lem213788 b c) (@lem213787 a d h1)). Qed.
Lemma lem213791 (m : nat) : (term86 m) = False.
Proof. exact (EQ_MP (@lem213738 m) (@lem213737 m)). Qed.
Lemma lem213792 (b : nat) (c : nat) : (term96 b c) = False.
Proof. exact (@lem213791 (Nat.mul b c)). Qed.
Lemma lem213793 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term95 b c a d) = False.
Proof. exact (TRANS (@lem213789 a b c d h1) (@lem213792 b c)). Qed.
Lemma lem213794 (b : nat) : (term97 b) = (term97 b).
Proof. exact (eq_refl (term97 b)). Qed.
Lemma lem213795 (c : nat) (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term98 b c a d) = (term99 b).
Proof. exact (MK_COMB (@lem213794 b) (@lem213793 b c a d h1)). Qed.
Lemma lem213797 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem213798 (b : nat) : (term99 b) = False.
Proof. exact (@lem213797 (term83 b)). Qed.
Lemma lem213799 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term98 b c a d) = False.
Proof. exact (TRANS (@lem213795 c a b d h1) (@lem213798 b)). Qed.
Lemma lem213800 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem213801 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term100 b c a d) = (imp False).
Proof. exact (MK_COMB (@lem213800) (@lem213799 b c a d h1)). Qed.
Lemma lem213803 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem213804 (c : nat) : (Nat.div c) = (Nat.div c).
Proof. exact (eq_refl (Nat.div c)). Qed.
Lemma lem213805 (c : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (Nat.div c d) = (term101 c).
Proof. exact (MK_COMB (@lem213804 c) (@lem213803 d h1)). Qed.
Lemma lem213806 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem213807 (c : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term102 c d) = (term103 c).
Proof. exact (MK_COMB (@lem213806) (@lem213805 c d h1)). Qed.
Lemma lem213808 (a : nat) (b : nat) : (Nat.div a b) = (Nat.div a b).
Proof. exact (eq_refl (Nat.div a b)). Qed.
Lemma lem213809 (c : nat) (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term104 c d a b) = (term105 c a b).
Proof. exact (MK_COMB (@lem213807 c d h1) (@lem213808 a b)). Qed.
Lemma lem213810 (c : nat) (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term106 c d a b) = (term107 c a b).
Proof. exact (MK_COMB (@lem213801 b c a d h1) (@lem213809 c a b d h1)). Qed.
Lemma lem213812 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem213813 (c : nat) (a : nat) (b : nat) : (term107 c a b) = True.
Proof. exact (@lem213812 (term105 c a b)). Qed.
Lemma lem213814 (c : nat) (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term106 c d a b) = True.
Proof. exact (TRANS (@lem213810 c a b d h1) (@lem213813 c a b)). Qed.
Lemma lem213815 (c : nat) (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : True = (term106 c d a b).
Proof. exact (SYM (@lem213814 c a b d h1)). Qed.
Lemma lem213816 (c : nat) (a : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : term106 c d a b.
Proof. exact (EQ_MP (@lem213815 c a b d h1) (@lem0)). Qed.
Lemma lem213883 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term98 b c a d) : term98 b c a d.
Proof. exact (h1). Qed.
Lemma lem213884 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term95 b c a d) : term95 b c a d.
Proof. exact (h1). Qed.
Lemma lem213885 (b : nat) (h1 : term83 b) : term83 b.
Proof. exact (h1). Qed.
Lemma lem213887 (a : nat) (b : nat) : term26 a b.
Proof. exact (@lem213722 a b (@lem213714 a b)). Qed.
Lemma lem213888 (c : nat) (d : nat) (a : nat) (b : nat) : term108 c d a b.
Proof. exact (@lem213887 (Nat.div c d) (Nat.div a b)). Qed.
Lemma lem213889 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term109 c b k a d) : term109 c b k a d.
Proof. exact (h1). Qed.
Lemma lem213891 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem213892 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term109 c b k a d) = (term110 c b k a d).
Proof. exact (@lem213891 (term109 c b k a d)). Qed.
Lemma lem213893 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term110 c b k a d) = (term109 c b k a d).
Proof. exact (SYM (@lem213892 c b k a d)). Qed.
Lemma lem213894 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) : term111 c b k a d.
Proof. exact (h1). Qed.
Lemma lem213897 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term112 c b k a d) : term112 c b k a d.
Proof. exact (h1). Qed.
Lemma lem213898 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : term113 c b k a d.
Proof. exact (fun h0 : term112 c b k a d => @lem213897 c b k a d h0). Qed.
Lemma lem213899 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term113 c b k a d) : term113 c b k a d.
Proof. exact (h1). Qed.
Lemma lem213900 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term112 c b k a d) : term112 c b k a d.
Proof. exact (h1). Qed.
Lemma lem213901 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term112 c b k a d) (h2 : term113 c b k a d) : term112 c b k a d.
Proof. exact (@lem213899 c b k a d h2 (@lem213900 c b k a d h1)). Qed.
Lemma lem213902 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term112 c b k a d) : term114 c b k a d.
Proof. exact (fun h0 : term113 c b k a d => @lem213901 c b k a d h1 h0). Qed.
Lemma lem213903 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term113 c b k a d) : term113 c b k a d.
Proof. exact (h1). Qed.
Lemma lem213904 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term112 c b k a d) (h2 : term113 c b k a d) : term112 c b k a d.
Proof. exact (@lem213902 c b k a d h1 (@lem213903 c b k a d h2)). Qed.
Lemma lem213905 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term113 c b k a d) : term113 c b k a d.
Proof. exact (fun h0 : term112 c b k a d => @lem213904 c b k a d h0 h1). Qed.
Lemma lem213906 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : term115 c b k a d.
Proof. exact (fun h0 : term113 c b k a d => @lem213905 c b k a d h0). Qed.
Lemma lem213909 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : term113 c b k a d.
Proof. exact (@lem213906 c b k a d (@lem213898 c b k a d)). Qed.
Lemma lem213951 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem213952 (P : nat -> Prop) (Q : nat -> Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem213951 nat P Q). Qed.
Lemma lem213953 (n : nat) (m : nat) : (term120 n m) = (term121 n m).
Proof. exact (@lem213952 (term122 n m) (term123 n m)). Qed.
Lemma lem213954 (p : nat) (n : nat) (m : nat) : (term124 n m p) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term124 n m p)). Qed.
Lemma lem213955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem213956 (p : nat) (n : nat) (m : nat) : (term125 n m p) = (term126 n m).
Proof. exact (MK_COMB (@lem213955) (@lem213954 p n m)). Qed.
Lemma lem213957 (n : nat) (m : nat) (p : nat) : (term127 n m p) = (term128 n m p).
Proof. exact (eq_refl (term127 n m p)). Qed.
Lemma lem213958 (n : nat) (m : nat) (p : nat) : (term129 n m p) = (term130 n m p).
Proof. exact (MK_COMB (@lem213956 p n m) (@lem213957 n m p)). Qed.
Lemma lem213959 (n : nat) (m : nat) : (term131 n m) = (term132 n m).
Proof. exact (fun_ext (fun p : nat => @lem213958 n m p)). Qed.
Lemma lem213960 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213961 (n : nat) (m : nat) : (term120 n m) = (term22 n m).
Proof. exact (MK_COMB (@lem213960) (@lem213959 n m)). Qed.
Lemma lem213962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem213963 (n : nat) (m : nat) : (term133 n m) = (term134 n m).
Proof. exact (MK_COMB (@lem213962) (@lem213961 n m)). Qed.
Lemma lem213964 (p : nat) (n : nat) (m : nat) : (term124 n m p) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term124 n m p)). Qed.
Lemma lem213965 (n : nat) (m : nat) : (term135 n m) = (term122 n m).
Proof. exact (fun_ext (fun p : nat => @lem213964 p n m)). Qed.
Lemma lem213966 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213967 (n : nat) (m : nat) : (term136 n m) = (term137 n m).
Proof. exact (MK_COMB (@lem213966) (@lem213965 n m)). Qed.
Lemma lem213968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem213969 (n : nat) (m : nat) : (term138 n m) = (term139 n m).
Proof. exact (MK_COMB (@lem213968) (@lem213967 n m)). Qed.
Lemma lem213970 (n : nat) (m : nat) (p : nat) : (term127 n m p) = (term128 n m p).
Proof. exact (eq_refl (term127 n m p)). Qed.
Lemma lem213971 (n : nat) (m : nat) : (term140 n m) = (term123 n m).
Proof. exact (fun_ext (fun p : nat => @lem213970 n m p)). Qed.
Lemma lem213972 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213973 (n : nat) (m : nat) : (term141 n m) = (term142 n m).
Proof. exact (MK_COMB (@lem213972) (@lem213971 n m)). Qed.
Lemma lem213974 (n : nat) (m : nat) : (term121 n m) = (term143 n m).
Proof. exact (MK_COMB (@lem213969 n m) (@lem213973 n m)). Qed.
Lemma lem213975 (n : nat) (m : nat) : ((term120 n m) = (term121 n m)) = ((term22 n m) = (term143 n m)).
Proof. exact (MK_COMB (@lem213963 n m) (@lem213974 n m)). Qed.
Lemma lem213976 (n : nat) (m : nat) : (term22 n m) = (term143 n m).
Proof. exact (EQ_MP (@lem213975 n m) (@lem213953 n m)). Qed.
Lemma lem213980 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem213981 (t : Prop) : (term145 t) = t.
Proof. exact (@lem213980 nat t). Qed.
Lemma lem213982 (n : nat) (m : nat) : (term137 n m) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (@lem213981 ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem213983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem213984 (n : nat) (m : nat) : (term139 n m) = (term126 n m).
Proof. exact (MK_COMB (@lem213983) (@lem213982 n m)). Qed.
Lemma lem213986 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem213987 (P : nat -> Prop) (Q : nat -> Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem213986 nat P Q). Qed.
Lemma lem213988 (n : nat) (m : nat) : (term146 n m) = (term147 n m).
Proof. exact (@lem213987 (term148 m n) (term149 n m)). Qed.
Lemma lem213989 (m : nat) (n : nat) (p : nat) : (term150 m n p) = ((term151 m n p) = (term152 m n p)).
Proof. exact (eq_refl (term150 m n p)). Qed.
Lemma lem213990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem213991 (m : nat) (n : nat) (p : nat) : (term153 m n p) = (term154 m n p).
Proof. exact (MK_COMB (@lem213990) (@lem213989 m n p)). Qed.
Lemma lem213992 (n : nat) (m : nat) (p : nat) : (term155 n m p) = ((term152 m n p) = (term152 n m p)).
Proof. exact (eq_refl (term155 n m p)). Qed.
Lemma lem213993 (n : nat) (m : nat) (p : nat) : (term156 n m p) = (term128 n m p).
Proof. exact (MK_COMB (@lem213991 m n p) (@lem213992 n m p)). Qed.
Lemma lem213994 (n : nat) (m : nat) : (term157 n m) = (term123 n m).
Proof. exact (fun_ext (fun p : nat => @lem213993 n m p)). Qed.
Lemma lem213995 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem213996 (n : nat) (m : nat) : (term146 n m) = (term142 n m).
Proof. exact (MK_COMB (@lem213995) (@lem213994 n m)). Qed.
Lemma lem213997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem213998 (n : nat) (m : nat) : (term158 n m) = (term159 n m).
Proof. exact (MK_COMB (@lem213997) (@lem213996 n m)). Qed.
Lemma lem213999 (m : nat) (n : nat) (p : nat) : (term150 m n p) = ((term151 m n p) = (term152 m n p)).
Proof. exact (eq_refl (term150 m n p)). Qed.
Lemma lem214000 (m : nat) (n : nat) : (term160 m n) = (term148 m n).
Proof. exact (fun_ext (fun p : nat => @lem213999 m n p)). Qed.
Lemma lem214001 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214002 (m : nat) (n : nat) : (term161 m n) = (term162 m n).
Proof. exact (MK_COMB (@lem214001) (@lem214000 m n)). Qed.
Lemma lem214003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214004 (m : nat) (n : nat) : (term163 m n) = (term164 m n).
Proof. exact (MK_COMB (@lem214003) (@lem214002 m n)). Qed.
Lemma lem214005 (n : nat) (m : nat) (p : nat) : (term155 n m p) = ((term152 m n p) = (term152 n m p)).
Proof. exact (eq_refl (term155 n m p)). Qed.
Lemma lem214006 (n : nat) (m : nat) : (term165 n m) = (term149 n m).
Proof. exact (fun_ext (fun p : nat => @lem214005 n m p)). Qed.
Lemma lem214007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214008 (n : nat) (m : nat) : (term166 n m) = (term167 n m).
Proof. exact (MK_COMB (@lem214007) (@lem214006 n m)). Qed.
Lemma lem214009 (n : nat) (m : nat) : (term147 n m) = (term168 n m).
Proof. exact (MK_COMB (@lem214004 m n) (@lem214008 n m)). Qed.
Lemma lem214010 (n : nat) (m : nat) : ((term146 n m) = (term147 n m)) = ((term142 n m) = (term168 n m)).
Proof. exact (MK_COMB (@lem213998 n m) (@lem214009 n m)). Qed.
Lemma lem214011 (n : nat) (m : nat) : (term142 n m) = (term168 n m).
Proof. exact (EQ_MP (@lem214010 n m) (@lem213988 n m)). Qed.
Lemma lem214022 (n : nat) (m : nat) : (term143 n m) = (term169 n m).
Proof. exact (MK_COMB (@lem213984 n m) (@lem214011 n m)). Qed.
Lemma lem214025 (n : nat) (m : nat) : (term22 n m) = (term169 n m).
Proof. exact (TRANS (@lem213976 n m) (@lem214022 n m)). Qed.
Lemma lem214026 (n : nat) : (term170 n) = (term171 n).
Proof. exact (fun_ext (fun m : nat => @lem214025 n m)). Qed.
Lemma lem214027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214028 (n : nat) : (term23 n) = (term172 n).
Proof. exact (MK_COMB (@lem214027) (@lem214026 n)). Qed.
Lemma lem214030 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem214031 (P : nat -> Prop) (Q : nat -> Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem214030 nat P Q). Qed.
Lemma lem214032 (n : nat) : (term173 n) = (term174 n).
Proof. exact (@lem214031 (term175 n) (term176 n)). Qed.
Lemma lem214033 (n : nat) (m : nat) : (term177 n m) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term177 n m)). Qed.
Lemma lem214034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214035 (n : nat) (m : nat) : (term178 n m) = (term126 n m).
Proof. exact (MK_COMB (@lem214034) (@lem214033 n m)). Qed.
Lemma lem214036 (n : nat) (m : nat) : (term179 n m) = (term168 n m).
Proof. exact (eq_refl (term179 n m)). Qed.
Lemma lem214037 (n : nat) (m : nat) : (term180 n m) = (term169 n m).
Proof. exact (MK_COMB (@lem214035 n m) (@lem214036 n m)). Qed.
Lemma lem214038 (n : nat) : (term181 n) = (term171 n).
Proof. exact (fun_ext (fun m : nat => @lem214037 n m)). Qed.
Lemma lem214039 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214040 (n : nat) : (term173 n) = (term172 n).
Proof. exact (MK_COMB (@lem214039) (@lem214038 n)). Qed.
Lemma lem214041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem214042 (n : nat) : (term182 n) = (term183 n).
Proof. exact (MK_COMB (@lem214041) (@lem214040 n)). Qed.
Lemma lem214043 (n : nat) (m : nat) : (term177 n m) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term177 n m)). Qed.
Lemma lem214044 (n : nat) : (term184 n) = (term175 n).
Proof. exact (fun_ext (fun m : nat => @lem214043 n m)). Qed.
Lemma lem214045 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214046 (n : nat) : (term185 n) = (term186 n).
Proof. exact (MK_COMB (@lem214045) (@lem214044 n)). Qed.
Lemma lem214047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214048 (n : nat) : (term187 n) = (term188 n).
Proof. exact (MK_COMB (@lem214047) (@lem214046 n)). Qed.
Lemma lem214049 (n : nat) (m : nat) : (term179 n m) = (term168 n m).
Proof. exact (eq_refl (term179 n m)). Qed.
Lemma lem214050 (n : nat) : (term189 n) = (term176 n).
Proof. exact (fun_ext (fun m : nat => @lem214049 n m)). Qed.
Lemma lem214051 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214052 (n : nat) : (term190 n) = (term191 n).
Proof. exact (MK_COMB (@lem214051) (@lem214050 n)). Qed.
Lemma lem214053 (n : nat) : (term174 n) = (term192 n).
Proof. exact (MK_COMB (@lem214048 n) (@lem214052 n)). Qed.
Lemma lem214054 (n : nat) : ((term173 n) = (term174 n)) = ((term172 n) = (term192 n)).
Proof. exact (MK_COMB (@lem214042 n) (@lem214053 n)). Qed.
Lemma lem214055 (n : nat) : (term172 n) = (term192 n).
Proof. exact (EQ_MP (@lem214054 n) (@lem214032 n)). Qed.
Lemma lem214063 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem214064 (P : nat -> Prop) (Q : nat -> Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem214063 nat P Q). Qed.
Lemma lem214065 (n : nat) : (term193 n) = (term194 n).
Proof. exact (@lem214064 (term195 n) (term196 n)). Qed.
Lemma lem214066 (m : nat) (n : nat) : (term197 n m) = (term162 m n).
Proof. exact (eq_refl (term197 n m)). Qed.
Lemma lem214067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214068 (m : nat) (n : nat) : (term198 n m) = (term164 m n).
Proof. exact (MK_COMB (@lem214067) (@lem214066 m n)). Qed.
Lemma lem214069 (n : nat) (m : nat) : (term199 n m) = (term167 n m).
Proof. exact (eq_refl (term199 n m)). Qed.
Lemma lem214070 (n : nat) (m : nat) : (term200 n m) = (term168 n m).
Proof. exact (MK_COMB (@lem214068 m n) (@lem214069 n m)). Qed.
Lemma lem214071 (n : nat) : (term201 n) = (term176 n).
Proof. exact (fun_ext (fun m : nat => @lem214070 n m)). Qed.
Lemma lem214072 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214073 (n : nat) : (term193 n) = (term191 n).
Proof. exact (MK_COMB (@lem214072) (@lem214071 n)). Qed.
Lemma lem214074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem214075 (n : nat) : (term202 n) = (term203 n).
Proof. exact (MK_COMB (@lem214074) (@lem214073 n)). Qed.
Lemma lem214076 (m : nat) (n : nat) : (term197 n m) = (term162 m n).
Proof. exact (eq_refl (term197 n m)). Qed.
Lemma lem214077 (n : nat) : (term204 n) = (term195 n).
Proof. exact (fun_ext (fun m : nat => @lem214076 m n)). Qed.
Lemma lem214078 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214079 (n : nat) : (term205 n) = (term206 n).
Proof. exact (MK_COMB (@lem214078) (@lem214077 n)). Qed.
Lemma lem214080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214081 (n : nat) : (term207 n) = (term208 n).
Proof. exact (MK_COMB (@lem214080) (@lem214079 n)). Qed.
Lemma lem214082 (n : nat) (m : nat) : (term199 n m) = (term167 n m).
Proof. exact (eq_refl (term199 n m)). Qed.
Lemma lem214083 (n : nat) : (term209 n) = (term196 n).
Proof. exact (fun_ext (fun m : nat => @lem214082 n m)). Qed.
Lemma lem214084 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214085 (n : nat) : (term210 n) = (term211 n).
Proof. exact (MK_COMB (@lem214084) (@lem214083 n)). Qed.
Lemma lem214086 (n : nat) : (term194 n) = (term212 n).
Proof. exact (MK_COMB (@lem214081 n) (@lem214085 n)). Qed.
Lemma lem214087 (n : nat) : ((term193 n) = (term194 n)) = ((term191 n) = (term212 n)).
Proof. exact (MK_COMB (@lem214075 n) (@lem214086 n)). Qed.
Lemma lem214088 (n : nat) : (term191 n) = (term212 n).
Proof. exact (EQ_MP (@lem214087 n) (@lem214065 n)). Qed.
Lemma lem214107 (n : nat) : (term188 n) = (term188 n).
Proof. exact (eq_refl (term188 n)). Qed.
Lemma lem214108 (n : nat) : (term192 n) = (term213 n).
Proof. exact (MK_COMB (@lem214107 n) (@lem214088 n)). Qed.
Lemma lem214111 (n : nat) : (term172 n) = (term213 n).
Proof. exact (TRANS (@lem214055 n) (@lem214108 n)). Qed.
Lemma lem214112 (n : nat) : (term23 n) = (term213 n).
Proof. exact (TRANS (@lem214028 n) (@lem214111 n)). Qed.
Lemma lem214113 : term214 = term215.
Proof. exact (fun_ext (fun n : nat => @lem214112 n)). Qed.
Lemma lem214114 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214115 : term24 = term216.
Proof. exact (MK_COMB (@lem214114) (@lem214113)). Qed.
Lemma lem214117 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem214118 (P : nat -> Prop) (Q : nat -> Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem214117 nat P Q). Qed.
Lemma lem214119 : term217 = term218.
Proof. exact (@lem214118 term219 term220). Qed.
Lemma lem214120 (n : nat) : (term221 n) = (term186 n).
Proof. exact (eq_refl (term221 n)). Qed.
Lemma lem214121 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214122 (n : nat) : (term222 n) = (term188 n).
Proof. exact (MK_COMB (@lem214121) (@lem214120 n)). Qed.
Lemma lem214123 (n : nat) : (term223 n) = (term212 n).
Proof. exact (eq_refl (term223 n)). Qed.
Lemma lem214124 (n : nat) : (term224 n) = (term213 n).
Proof. exact (MK_COMB (@lem214122 n) (@lem214123 n)). Qed.
Lemma lem214125 : term225 = term215.
Proof. exact (fun_ext (fun n : nat => @lem214124 n)). Qed.
Lemma lem214126 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214127 : term217 = term216.
Proof. exact (MK_COMB (@lem214126) (@lem214125)). Qed.
Lemma lem214128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem214129 : term226 = term227.
Proof. exact (MK_COMB (@lem214128) (@lem214127)). Qed.
Lemma lem214130 (n : nat) : (term221 n) = (term186 n).
Proof. exact (eq_refl (term221 n)). Qed.
Lemma lem214131 : term228 = term219.
Proof. exact (fun_ext (fun n : nat => @lem214130 n)). Qed.
Lemma lem214132 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214133 : term229 = term230.
Proof. exact (MK_COMB (@lem214132) (@lem214131)). Qed.
Lemma lem214134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214135 : term231 = term232.
Proof. exact (MK_COMB (@lem214134) (@lem214133)). Qed.
Lemma lem214136 (n : nat) : (term223 n) = (term212 n).
Proof. exact (eq_refl (term223 n)). Qed.
Lemma lem214137 : term233 = term220.
Proof. exact (fun_ext (fun n : nat => @lem214136 n)). Qed.
Lemma lem214138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214139 : term234 = term235.
Proof. exact (MK_COMB (@lem214138) (@lem214137)). Qed.
Lemma lem214140 : term218 = term236.
Proof. exact (MK_COMB (@lem214135) (@lem214139)). Qed.
Lemma lem214141 : (term217 = term218) = (term216 = term236).
Proof. exact (MK_COMB (@lem214129) (@lem214140)). Qed.
Lemma lem214142 : term216 = term236.
Proof. exact (EQ_MP (@lem214141) (@lem214119)). Qed.
Lemma lem214154 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem214155 (P : nat -> Prop) (Q : nat -> Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem214154 nat P Q). Qed.
Lemma lem214156 : term237 = term238.
Proof. exact (@lem214155 term239 term240). Qed.
Lemma lem214157 (n : nat) : (term241 n) = (term206 n).
Proof. exact (eq_refl (term241 n)). Qed.
Lemma lem214158 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214159 (n : nat) : (term242 n) = (term208 n).
Proof. exact (MK_COMB (@lem214158) (@lem214157 n)). Qed.
Lemma lem214160 (n : nat) : (term243 n) = (term211 n).
Proof. exact (eq_refl (term243 n)). Qed.
Lemma lem214161 (n : nat) : (term244 n) = (term212 n).
Proof. exact (MK_COMB (@lem214159 n) (@lem214160 n)). Qed.
Lemma lem214162 : term245 = term220.
Proof. exact (fun_ext (fun n : nat => @lem214161 n)). Qed.
Lemma lem214163 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214164 : term237 = term235.
Proof. exact (MK_COMB (@lem214163) (@lem214162)). Qed.
Lemma lem214165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem214166 : term246 = term247.
Proof. exact (MK_COMB (@lem214165) (@lem214164)). Qed.
Lemma lem214167 (n : nat) : (term241 n) = (term206 n).
Proof. exact (eq_refl (term241 n)). Qed.
Lemma lem214168 : term248 = term239.
Proof. exact (fun_ext (fun n : nat => @lem214167 n)). Qed.
Lemma lem214169 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214170 : term249 = term250.
Proof. exact (MK_COMB (@lem214169) (@lem214168)). Qed.
Lemma lem214171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214172 : term251 = term252.
Proof. exact (MK_COMB (@lem214171) (@lem214170)). Qed.
Lemma lem214173 (n : nat) : (term243 n) = (term211 n).
Proof. exact (eq_refl (term243 n)). Qed.
Lemma lem214174 : term253 = term240.
Proof. exact (fun_ext (fun n : nat => @lem214173 n)). Qed.
Lemma lem214175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214176 : term254 = term255.
Proof. exact (MK_COMB (@lem214175) (@lem214174)). Qed.
Lemma lem214177 : term238 = term256.
Proof. exact (MK_COMB (@lem214172) (@lem214176)). Qed.
Lemma lem214178 : (term237 = term238) = (term235 = term256).
Proof. exact (MK_COMB (@lem214166) (@lem214177)). Qed.
Lemma lem214179 : term235 = term256.
Proof. exact (EQ_MP (@lem214178) (@lem214156)). Qed.
Lemma lem214206 : term232 = term232.
Proof. exact (eq_refl term232). Qed.
Lemma lem214207 : term236 = term257.
Proof. exact (MK_COMB (@lem214206) (@lem214179)). Qed.
Lemma lem214210 : term216 = term257.
Proof. exact (TRANS (@lem214142) (@lem214207)). Qed.
Lemma lem214211 : term24 = term257.
Proof. exact (TRANS (@lem214115) (@lem214210)). Qed.
Lemma lem214212 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem214213 : term258 = term259.
Proof. exact (MK_COMB (@lem214212) (@lem214211)). Qed.
Lemma lem214215 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem214216 : term260 = term261.
Proof. exact (@lem214215 term262). Qed.
Lemma lem214233 : term263 = term264.
Proof. exact (MK_COMB (@lem214213) (@lem214216)). Qed.
Lemma lem214236 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term265 c b k a d) = (term265 c b k a d).
Proof. exact (eq_refl (term265 c b k a d)). Qed.
Lemma lem214237 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term266 c b k a d) = (term267 c b k a d).
Proof. exact (MK_COMB (@lem214236 c b k a d) (@lem214233)). Qed.
Lemma lem214240 (b : nat) (c : nat) (a : nat) (d : nat) : (term268 b c a d) = (term268 b c a d).
Proof. exact (eq_refl (term268 b c a d)). Qed.
Lemma lem214241 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term269 c b k a d) = (term270 c b k a d).
Proof. exact (MK_COMB (@lem214240 b c a d) (@lem214237 c b k a d)). Qed.
Lemma lem214244 (b : nat) : (term271 b) = (term271 b).
Proof. exact (eq_refl (term271 b)). Qed.
Lemma lem214245 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term272 c b k a d) = (term273 c b k a d).
Proof. exact (MK_COMB (@lem214244 b) (@lem214241 c b k a d)). Qed.
Lemma lem214248 (d : nat) : (term271 d) = (term271 d).
Proof. exact (eq_refl (term271 d)). Qed.
Lemma lem214249 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term112 c b k a d) = (term274 c b k a d).
Proof. exact (MK_COMB (@lem214248 d) (@lem214245 c b k a d)). Qed.
Lemma lem214252 (b : nat) (k : nat) (a : nat) (d : nat) : (term275 b k a d) = (term276 b k a d).
Proof. exact (fun_ext (fun c : nat => @lem214249 c b k a d)). Qed.
Lemma lem214253 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214254 (b : nat) (k : nat) (a : nat) (d : nat) : (term277 b k a d) = (term278 b k a d).
Proof. exact (MK_COMB (@lem214253) (@lem214252 b k a d)). Qed.
Lemma lem214259 (k : nat) (a : nat) (d : nat) : (term279 k a d) = (term280 k a d).
Proof. exact (fun_ext (fun b : nat => @lem214254 b k a d)). Qed.
Lemma lem214260 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214261 (k : nat) (a : nat) (d : nat) : (term281 k a d) = (term282 k a d).
Proof. exact (MK_COMB (@lem214260) (@lem214259 k a d)). Qed.
Lemma lem214266 (a : nat) (d : nat) : (term283 a d) = (term284 a d).
Proof. exact (fun_ext (fun k : nat => @lem214261 k a d)). Qed.
Lemma lem214267 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214268 (a : nat) (d : nat) : (term285 a d) = (term286 a d).
Proof. exact (MK_COMB (@lem214267) (@lem214266 a d)). Qed.
Lemma lem214273 (d : nat) : (term287 d) = (term288 d).
Proof. exact (fun_ext (fun a : nat => @lem214268 a d)). Qed.
Lemma lem214274 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214275 (d : nat) : (term289 d) = (term290 d).
Proof. exact (MK_COMB (@lem214274) (@lem214273 d)). Qed.
Lemma lem214280 : term291 = term292.
Proof. exact (fun_ext (fun d : nat => @lem214275 d)). Qed.
Lemma lem214281 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214290 : term293 = term294.
Proof. exact (MK_COMB (@lem214281) (@lem214280)). Qed.
Lemma lem214299 (n : nat) (m : nat) (p : nat) : (term295 n m p) = (term295 n m p).
Proof. exact (eq_refl (term295 n m p)). Qed.
Lemma lem214300 (n : nat) (m : nat) : (term296 n m) = (term296 n m).
Proof. exact (fun_ext (fun p : nat => @lem214299 n m p)). Qed.
Lemma lem214301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214302 (n : nat) (m : nat) : (term297 n m) = (term297 n m).
Proof. exact (MK_COMB (@lem214301) (@lem214300 n m)). Qed.
Lemma lem214303 (m : nat) : (term298 m) = (term298 m).
Proof. exact (fun_ext (fun n : nat => @lem214302 n m)). Qed.
Lemma lem214304 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214305 (m : nat) : (term299 m) = (term299 m).
Proof. exact (MK_COMB (@lem214304) (@lem214303 m)). Qed.
Lemma lem214306 : term300 = term300.
Proof. exact (fun_ext (fun m : nat => @lem214305 m)). Qed.
Lemma lem214307 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214308 : term262 = term262.
Proof. exact (MK_COMB (@lem214307) (@lem214306)). Qed.
Lemma lem214309 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem214310 : term261 = term261.
Proof. exact (MK_COMB (@lem214309) (@lem214308)). Qed.
Lemma lem214311 (n : nat) (m : nat) (p : nat) : ((term152 m n p) = (term152 n m p)) = ((term152 m n p) = (term152 n m p)).
Proof. exact (eq_refl ((term152 m n p) = (term152 n m p))). Qed.
Lemma lem214312 (n : nat) (m : nat) : (term149 n m) = (term149 n m).
Proof. exact (fun_ext (fun p : nat => @lem214311 n m p)). Qed.
Lemma lem214313 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214314 (n : nat) (m : nat) : (term167 n m) = (term167 n m).
Proof. exact (MK_COMB (@lem214313) (@lem214312 n m)). Qed.
Lemma lem214315 (n : nat) : (term196 n) = (term196 n).
Proof. exact (fun_ext (fun m : nat => @lem214314 n m)). Qed.
Lemma lem214316 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214317 (n : nat) : (term211 n) = (term211 n).
Proof. exact (MK_COMB (@lem214316) (@lem214315 n)). Qed.
Lemma lem214318 : term240 = term240.
Proof. exact (fun_ext (fun n : nat => @lem214317 n)). Qed.
Lemma lem214319 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214320 : term255 = term255.
Proof. exact (MK_COMB (@lem214319) (@lem214318)). Qed.
Lemma lem214321 (m : nat) (n : nat) (p : nat) : ((term151 m n p) = (term152 m n p)) = ((term151 m n p) = (term152 m n p)).
Proof. exact (eq_refl ((term151 m n p) = (term152 m n p))). Qed.
Lemma lem214322 (m : nat) (n : nat) : (term148 m n) = (term148 m n).
Proof. exact (fun_ext (fun p : nat => @lem214321 m n p)). Qed.
Lemma lem214323 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214324 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (MK_COMB (@lem214323) (@lem214322 m n)). Qed.
Lemma lem214325 (n : nat) : (term195 n) = (term195 n).
Proof. exact (fun_ext (fun m : nat => @lem214324 m n)). Qed.
Lemma lem214326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214327 (n : nat) : (term206 n) = (term206 n).
Proof. exact (MK_COMB (@lem214326) (@lem214325 n)). Qed.
Lemma lem214328 : term239 = term239.
Proof. exact (fun_ext (fun n : nat => @lem214327 n)). Qed.
Lemma lem214329 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214330 : term250 = term250.
Proof. exact (MK_COMB (@lem214329) (@lem214328)). Qed.
Lemma lem214331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214332 : term252 = term252.
Proof. exact (MK_COMB (@lem214331) (@lem214330)). Qed.
Lemma lem214333 : term256 = term256.
Proof. exact (MK_COMB (@lem214332) (@lem214320)). Qed.
Lemma lem214334 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem214335 (n : nat) : (term175 n) = (term175 n).
Proof. exact (fun_ext (fun m : nat => @lem214334 n m)). Qed.
Lemma lem214336 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214337 (n : nat) : (term186 n) = (term186 n).
Proof. exact (MK_COMB (@lem214336) (@lem214335 n)). Qed.
Lemma lem214338 : term219 = term219.
Proof. exact (fun_ext (fun n : nat => @lem214337 n)). Qed.
Lemma lem214339 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214340 : term230 = term230.
Proof. exact (MK_COMB (@lem214339) (@lem214338)). Qed.
Lemma lem214341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214342 : term232 = term232.
Proof. exact (MK_COMB (@lem214341) (@lem214340)). Qed.
Lemma lem214343 : term257 = term257.
Proof. exact (MK_COMB (@lem214342) (@lem214333)). Qed.
Lemma lem214344 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem214345 : term259 = term259.
Proof. exact (MK_COMB (@lem214344) (@lem214343)). Qed.
Lemma lem214346 : term264 = term264.
Proof. exact (MK_COMB (@lem214345) (@lem214310)). Qed.
Lemma lem214355 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term265 c b k a d) = (term265 c b k a d).
Proof. exact (eq_refl (term265 c b k a d)). Qed.
Lemma lem214356 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term267 c b k a d) = (term267 c b k a d).
Proof. exact (MK_COMB (@lem214355 c b k a d) (@lem214346)). Qed.
Lemma lem214359 (b : nat) (c : nat) (a : nat) (d : nat) : (term268 b c a d) = (term268 b c a d).
Proof. exact (eq_refl (term268 b c a d)). Qed.
Lemma lem214360 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term270 c b k a d) = (term270 c b k a d).
Proof. exact (MK_COMB (@lem214359 b c a d) (@lem214356 c b k a d)). Qed.
Lemma lem214365 (b : nat) : (term271 b) = (term271 b).
Proof. exact (eq_refl (term271 b)). Qed.
Lemma lem214366 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term273 c b k a d) = (term273 c b k a d).
Proof. exact (MK_COMB (@lem214365 b) (@lem214360 c b k a d)). Qed.
Lemma lem214371 (d : nat) : (term271 d) = (term271 d).
Proof. exact (eq_refl (term271 d)). Qed.
Lemma lem214372 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term274 c b k a d) = (term274 c b k a d).
Proof. exact (MK_COMB (@lem214371 d) (@lem214366 c b k a d)). Qed.
Lemma lem214373 (b : nat) (k : nat) (a : nat) (d : nat) : (term276 b k a d) = (term276 b k a d).
Proof. exact (fun_ext (fun c : nat => @lem214372 c b k a d)). Qed.
Lemma lem214374 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214375 (b : nat) (k : nat) (a : nat) (d : nat) : (term278 b k a d) = (term278 b k a d).
Proof. exact (MK_COMB (@lem214374) (@lem214373 b k a d)). Qed.
Lemma lem214376 (k : nat) (a : nat) (d : nat) : (term280 k a d) = (term280 k a d).
Proof. exact (fun_ext (fun b : nat => @lem214375 b k a d)). Qed.
Lemma lem214377 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214378 (k : nat) (a : nat) (d : nat) : (term282 k a d) = (term282 k a d).
Proof. exact (MK_COMB (@lem214377) (@lem214376 k a d)). Qed.
Lemma lem214379 (a : nat) (d : nat) : (term284 a d) = (term284 a d).
Proof. exact (fun_ext (fun k : nat => @lem214378 k a d)). Qed.
Lemma lem214380 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214381 (a : nat) (d : nat) : (term286 a d) = (term286 a d).
Proof. exact (MK_COMB (@lem214380) (@lem214379 a d)). Qed.
Lemma lem214382 (d : nat) : (term288 d) = (term288 d).
Proof. exact (fun_ext (fun a : nat => @lem214381 a d)). Qed.
Lemma lem214383 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214384 (d : nat) : (term290 d) = (term290 d).
Proof. exact (MK_COMB (@lem214383) (@lem214382 d)). Qed.
Lemma lem214385 : term292 = term292.
Proof. exact (fun_ext (fun d : nat => @lem214384 d)). Qed.
Lemma lem214386 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214387 : term294 = term294.
Proof. exact (MK_COMB (@lem214386) (@lem214385)). Qed.
Lemma lem214506 : term293 = term294.
Proof. exact (TRANS (@lem214290) (@lem214387)). Qed.
Lemma lem214507 : term294 = term293.
Proof. exact (SYM (@lem214506)). Qed.
Lemma lem214511 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) : term111 c b k a d.
Proof. exact (h1). Qed.
Lemma lem214512 (h1 : term257) : term257.
Proof. exact (h1). Qed.
Lemma lem214513 (h1 : term262) : term262.
Proof. exact (h1). Qed.
Lemma lem214531 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term95 b c a d) : term95 b c a d.
Proof. exact (h1). Qed.
Lemma lem214542 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term111 c b k a d) = (term301 c b k a d).
Proof. exact (@lem17362 (term302 d k b c) (term303 b k a d)). Qed.
Lemma lem214544 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem214545 (n : nat) : (term175 n) = (term175 n).
Proof. exact (fun_ext (fun m : nat => @lem214544 n m)). Qed.
Lemma lem214546 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214547 (n : nat) : (term186 n) = (term186 n).
Proof. exact (MK_COMB (@lem214546) (@lem214545 n)). Qed.
Lemma lem214548 : term219 = term219.
Proof. exact (fun_ext (fun n : nat => @lem214547 n)). Qed.
Lemma lem214549 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214550 : term230 = term230.
Proof. exact (MK_COMB (@lem214549) (@lem214548)). Qed.
Lemma lem214551 (m : nat) (n : nat) (p : nat) : ((term151 m n p) = (term152 m n p)) = ((term151 m n p) = (term152 m n p)).
Proof. exact (eq_refl ((term151 m n p) = (term152 m n p))). Qed.
Lemma lem214552 (m : nat) (n : nat) : (term148 m n) = (term148 m n).
Proof. exact (fun_ext (fun p : nat => @lem214551 m n p)). Qed.
Lemma lem214553 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214554 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (MK_COMB (@lem214553) (@lem214552 m n)). Qed.
Lemma lem214555 (n : nat) : (term195 n) = (term195 n).
Proof. exact (fun_ext (fun m : nat => @lem214554 m n)). Qed.
Lemma lem214556 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214557 (n : nat) : (term206 n) = (term206 n).
Proof. exact (MK_COMB (@lem214556) (@lem214555 n)). Qed.
Lemma lem214558 : term239 = term239.
Proof. exact (fun_ext (fun n : nat => @lem214557 n)). Qed.
Lemma lem214559 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214560 : term250 = term250.
Proof. exact (MK_COMB (@lem214559) (@lem214558)). Qed.
Lemma lem214561 (n : nat) (m : nat) (p : nat) : ((term152 m n p) = (term152 n m p)) = ((term152 m n p) = (term152 n m p)).
Proof. exact (eq_refl ((term152 m n p) = (term152 n m p))). Qed.
Lemma lem214562 (n : nat) (m : nat) : (term149 n m) = (term149 n m).
Proof. exact (fun_ext (fun p : nat => @lem214561 n m p)). Qed.
Lemma lem214563 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214564 (n : nat) (m : nat) : (term167 n m) = (term167 n m).
Proof. exact (MK_COMB (@lem214563) (@lem214562 n m)). Qed.
Lemma lem214565 (n : nat) : (term196 n) = (term196 n).
Proof. exact (fun_ext (fun m : nat => @lem214564 n m)). Qed.
Lemma lem214566 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214567 (n : nat) : (term211 n) = (term211 n).
Proof. exact (MK_COMB (@lem214566) (@lem214565 n)). Qed.
Lemma lem214568 : term240 = term240.
Proof. exact (fun_ext (fun n : nat => @lem214567 n)). Qed.
Lemma lem214569 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214570 : term255 = term255.
Proof. exact (MK_COMB (@lem214569) (@lem214568)). Qed.
Lemma lem214571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214572 : term252 = term252.
Proof. exact (MK_COMB (@lem214571) (@lem214560)). Qed.
Lemma lem214573 : term256 = term256.
Proof. exact (MK_COMB (@lem214572) (@lem214570)). Qed.
Lemma lem214574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214575 : term232 = term232.
Proof. exact (MK_COMB (@lem214574) (@lem214550)). Qed.
Lemma lem214612 : term257 = term257.
Proof. exact (MK_COMB (@lem214575) (@lem214573)). Qed.
Lemma lem214613 (h1 : term257) : term257.
Proof. exact (EQ_MP (@lem214612) (@lem214512 h1)). Qed.
Lemma lem214620 (m : nat) (n : nat) (p : nat) : (term304 m n p) = (term305 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.lt n p)). Qed.
Lemma lem214621 (m : nat) (p : nat) : (Peano.lt m p) = (Peano.lt m p).
Proof. exact (eq_refl (Peano.lt m p)). Qed.
Lemma lem214622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem214623 (m : nat) (n : nat) (p : nat) : (term306 m n p) = (term307 m n p).
Proof. exact (MK_COMB (@lem214622) (@lem214620 m n p)). Qed.
Lemma lem214624 (n : nat) (m : nat) (p : nat) : (term308 n m p) = (term309 n m p).
Proof. exact (MK_COMB (@lem214623 m n p) (@lem214621 m p)). Qed.
Lemma lem214625 (n : nat) (m : nat) (p : nat) : (term295 n m p) = (term308 n m p).
Proof. exact (@lem17265 (term310 m n p) (Peano.lt m p)). Qed.
Lemma lem214626 (n : nat) (m : nat) (p : nat) : (term295 n m p) = (term309 n m p).
Proof. exact (TRANS (@lem214625 n m p) (@lem214624 n m p)). Qed.
Lemma lem214627 (n : nat) (m : nat) : (term296 n m) = (term311 n m).
Proof. exact (fun_ext (fun p : nat => @lem214626 n m p)). Qed.
Lemma lem214628 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214629 (n : nat) (m : nat) : (term297 n m) = (term312 n m).
Proof. exact (MK_COMB (@lem214628) (@lem214627 n m)). Qed.
Lemma lem214630 (m : nat) : (term298 m) = (term313 m).
Proof. exact (fun_ext (fun n : nat => @lem214629 n m)). Qed.
Lemma lem214631 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214632 (m : nat) : (term299 m) = (term314 m).
Proof. exact (MK_COMB (@lem214631) (@lem214630 m)). Qed.
Lemma lem214633 : term300 = term315.
Proof. exact (fun_ext (fun m : nat => @lem214632 m)). Qed.
Lemma lem214634 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214695 : term262 = term316.
Proof. exact (MK_COMB (@lem214634) (@lem214633)). Qed.
Lemma lem214696 (h1 : term262) : term316.
Proof. exact (EQ_MP (@lem214695) (@lem214513 h1)). Qed.
Lemma lem214738 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term95 b c a d) : term95 b c a d.
Proof. exact (h1). Qed.
Lemma lem214786 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) : term301 c b k a d.
Proof. exact (EQ_MP (@lem214542 c b k a d) (@lem214511 c b k a d h1)). Qed.
Lemma lem214807 (n : nat) (m : nat) (p : nat) : ((term152 m n p) = (term152 n m p)) = ((term152 m n p) = (term152 n m p)).
Proof. exact (eq_refl ((term152 m n p) = (term152 n m p))). Qed.
Lemma lem214808 (n : nat) (m : nat) : (term149 n m) = (term149 n m).
Proof. exact (fun_ext (fun p : nat => @lem214807 n m p)). Qed.
Lemma lem214809 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214810 (n : nat) (m : nat) : (term167 n m) = (term167 n m).
Proof. exact (MK_COMB (@lem214809) (@lem214808 n m)). Qed.
Lemma lem214811 (n : nat) : (term196 n) = (term196 n).
Proof. exact (fun_ext (fun m : nat => @lem214810 n m)). Qed.
Lemma lem214812 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214813 (n : nat) : (term211 n) = (term211 n).
Proof. exact (MK_COMB (@lem214812) (@lem214811 n)). Qed.
Lemma lem214814 : term240 = term240.
Proof. exact (fun_ext (fun n : nat => @lem214813 n)). Qed.
Lemma lem214815 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214816 : term255 = term255.
Proof. exact (MK_COMB (@lem214815) (@lem214814)). Qed.
Lemma lem214837 (m : nat) (n : nat) (p : nat) : ((term151 m n p) = (term152 m n p)) = ((term151 m n p) = (term152 m n p)).
Proof. exact (eq_refl ((term151 m n p) = (term152 m n p))). Qed.
Lemma lem214838 (m : nat) (n : nat) : (term148 m n) = (term148 m n).
Proof. exact (fun_ext (fun p : nat => @lem214837 m n p)). Qed.
Lemma lem214839 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214840 (m : nat) (n : nat) : (term162 m n) = (term162 m n).
Proof. exact (MK_COMB (@lem214839) (@lem214838 m n)). Qed.
Lemma lem214841 (n : nat) : (term195 n) = (term195 n).
Proof. exact (fun_ext (fun m : nat => @lem214840 m n)). Qed.
Lemma lem214842 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214843 (n : nat) : (term206 n) = (term206 n).
Proof. exact (MK_COMB (@lem214842) (@lem214841 n)). Qed.
Lemma lem214844 : term239 = term239.
Proof. exact (fun_ext (fun n : nat => @lem214843 n)). Qed.
Lemma lem214845 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214846 : term250 = term250.
Proof. exact (MK_COMB (@lem214845) (@lem214844)). Qed.
Lemma lem214847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214848 : term252 = term252.
Proof. exact (MK_COMB (@lem214847) (@lem214846)). Qed.
Lemma lem214849 : term256 = term256.
Proof. exact (MK_COMB (@lem214848) (@lem214816)). Qed.
Lemma lem214862 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem214863 (n : nat) : (term175 n) = (term175 n).
Proof. exact (fun_ext (fun m : nat => @lem214862 n m)). Qed.
Lemma lem214864 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214865 (n : nat) : (term186 n) = (term186 n).
Proof. exact (MK_COMB (@lem214864) (@lem214863 n)). Qed.
Lemma lem214866 : term219 = term219.
Proof. exact (fun_ext (fun n : nat => @lem214865 n)). Qed.
Lemma lem214867 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214868 : term230 = term230.
Proof. exact (MK_COMB (@lem214867) (@lem214866)). Qed.
Lemma lem214869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem214870 : term232 = term232.
Proof. exact (MK_COMB (@lem214869) (@lem214868)). Qed.
Lemma lem214871 : term257 = term257.
Proof. exact (MK_COMB (@lem214870) (@lem214849)). Qed.
Lemma lem214872 (h1 : term257) : term257.
Proof. exact (EQ_MP (@lem214871) (@lem214613 h1)). Qed.
Lemma lem214897 (n : nat) (m : nat) (p : nat) : (term309 n m p) = (term309 n m p).
Proof. exact (eq_refl (term309 n m p)). Qed.
Lemma lem214898 (n : nat) (m : nat) : (term311 n m) = (term311 n m).
Proof. exact (fun_ext (fun p : nat => @lem214897 n m p)). Qed.
Lemma lem214899 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214900 (n : nat) (m : nat) : (term312 n m) = (term312 n m).
Proof. exact (MK_COMB (@lem214899) (@lem214898 n m)). Qed.
Lemma lem214901 (m : nat) : (term313 m) = (term313 m).
Proof. exact (fun_ext (fun n : nat => @lem214900 n m)). Qed.
Lemma lem214902 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214903 (m : nat) : (term314 m) = (term314 m).
Proof. exact (MK_COMB (@lem214902) (@lem214901 m)). Qed.
Lemma lem214904 : term315 = term315.
Proof. exact (fun_ext (fun m : nat => @lem214903 m)). Qed.
Lemma lem214905 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214906 : term316 = term316.
Proof. exact (MK_COMB (@lem214905) (@lem214904)). Qed.
Lemma lem214907 (h1 : term262) : term316.
Proof. exact (EQ_MP (@lem214906) (@lem214696 h1)). Qed.
Lemma lem214908 (h1 : term257) : term256.
Proof. exact (proj2 (@lem214872 h1)). Qed.
Lemma lem214909 (h1 : term257) : term230.
Proof. exact (proj1 (@lem214872 h1)). Qed.
Lemma lem214910 (h1 : term257) : term255.
Proof. exact (proj2 (@lem214908 h1)). Qed.
Lemma lem214925 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term95 b c a d) : term95 b c a d.
Proof. exact (h1). Qed.
Lemma lem214939 (n : nat) (m : nat) (p : nat) : (term309 n m p) = (term309 n m p).
Proof. exact (eq_refl (term309 n m p)). Qed.
Lemma lem214940 (n : nat) (m : nat) : (term311 n m) = (term311 n m).
Proof. exact (fun_ext (fun p : nat => @lem214939 n m p)). Qed.
Lemma lem214941 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214942 (n : nat) (m : nat) : (term312 n m) = (term312 n m).
Proof. exact (MK_COMB (@lem214941) (@lem214940 n m)). Qed.
Lemma lem214943 (m : nat) : (term313 m) = (term313 m).
Proof. exact (fun_ext (fun n : nat => @lem214942 n m)). Qed.
Lemma lem214944 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214945 (m : nat) : (term314 m) = (term314 m).
Proof. exact (MK_COMB (@lem214944) (@lem214943 m)). Qed.
Lemma lem214946 : term315 = term315.
Proof. exact (fun_ext (fun m : nat => @lem214945 m)). Qed.
Lemma lem214947 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214949 : term316 = term316.
Proof. exact (MK_COMB (@lem214947) (@lem214946)). Qed.
Lemma lem214950 (h1 : term262) : term316.
Proof. exact (EQ_MP (@lem214949) (@lem214907 h1)). Qed.
Lemma lem214952 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem214953 (n : nat) : (term175 n) = (term175 n).
Proof. exact (fun_ext (fun m : nat => @lem214952 n m)). Qed.
Lemma lem214954 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214955 (n : nat) : (term186 n) = (term186 n).
Proof. exact (MK_COMB (@lem214954) (@lem214953 n)). Qed.
Lemma lem214956 : term219 = term219.
Proof. exact (fun_ext (fun n : nat => @lem214955 n)). Qed.
Lemma lem214957 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214959 : term230 = term230.
Proof. exact (MK_COMB (@lem214957) (@lem214956)). Qed.
Lemma lem214960 (h1 : term257) : term230.
Proof. exact (EQ_MP (@lem214959) (@lem214909 h1)). Qed.
Lemma lem214975 (n : nat) (m : nat) (p : nat) : ((term152 m n p) = (term152 n m p)) = ((term152 m n p) = (term152 n m p)).
Proof. exact (eq_refl ((term152 m n p) = (term152 n m p))). Qed.
Lemma lem214976 (n : nat) (m : nat) : (term149 n m) = (term149 n m).
Proof. exact (fun_ext (fun p : nat => @lem214975 n m p)). Qed.
Lemma lem214977 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214978 (n : nat) (m : nat) : (term167 n m) = (term167 n m).
Proof. exact (MK_COMB (@lem214977) (@lem214976 n m)). Qed.
Lemma lem214979 (n : nat) : (term196 n) = (term196 n).
Proof. exact (fun_ext (fun m : nat => @lem214978 n m)). Qed.
Lemma lem214980 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214981 (n : nat) : (term211 n) = (term211 n).
Proof. exact (MK_COMB (@lem214980) (@lem214979 n)). Qed.
Lemma lem214982 : term240 = term240.
Proof. exact (fun_ext (fun n : nat => @lem214981 n)). Qed.
Lemma lem214983 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem214985 : term255 = term255.
Proof. exact (MK_COMB (@lem214983) (@lem214982)). Qed.
Lemma lem214986 (h1 : term257) : term255.
Proof. exact (EQ_MP (@lem214985) (@lem214910 h1)). Qed.
Lemma lem214995 (_4325 : nat) (h1 : term262) : term317 _4325.
Proof. exact (@lem214950 h1 _4325). Qed.
Lemma lem214996 (_4325 : nat) : (term317 _4325) = (term314 _4325).
Proof. exact (eq_refl (term317 _4325)). Qed.
Lemma lem214997 (_4325 : nat) (h1 : term262) : term314 _4325.
Proof. exact (EQ_MP (@lem214996 _4325) (@lem214995 _4325 h1)). Qed.
Lemma lem214998 (_4325 : nat) (_4326 : nat) (h1 : term262) : term318 _4325 _4326.
Proof. exact (@lem214997 _4325 h1 _4326). Qed.
Lemma lem214999 (_4326 : nat) (_4325 : nat) : (term318 _4325 _4326) = (term312 _4326 _4325).
Proof. exact (eq_refl (term318 _4325 _4326)). Qed.
Lemma lem215000 (_4326 : nat) (_4325 : nat) (h1 : term262) : term312 _4326 _4325.
Proof. exact (EQ_MP (@lem214999 _4326 _4325) (@lem214998 _4325 _4326 h1)). Qed.
Lemma lem215001 (_4326 : nat) (_4325 : nat) (_4327 : nat) (h1 : term262) : term319 _4326 _4325 _4327.
Proof. exact (@lem215000 _4326 _4325 h1 _4327). Qed.
Lemma lem215002 (_4326 : nat) (_4325 : nat) (_4327 : nat) : (term319 _4326 _4325 _4327) = (term309 _4326 _4325 _4327).
Proof. exact (eq_refl (term319 _4326 _4325 _4327)). Qed.
Lemma lem215003 (_4326 : nat) (_4325 : nat) (_4327 : nat) (h1 : term262) : term309 _4326 _4325 _4327.
Proof. exact (EQ_MP (@lem215002 _4326 _4325 _4327) (@lem215001 _4326 _4325 _4327 h1)). Qed.
Lemma lem215004 (_4328 : nat) (h1 : term257) : term221 _4328.
Proof. exact (@lem214960 h1 _4328). Qed.
Lemma lem215005 (_4328 : nat) : (term221 _4328) = (term186 _4328).
Proof. exact (eq_refl (term221 _4328)). Qed.
Lemma lem215006 (_4328 : nat) (h1 : term257) : term186 _4328.
Proof. exact (EQ_MP (@lem215005 _4328) (@lem215004 _4328 h1)). Qed.
Lemma lem215007 (_4328 : nat) (_4329 : nat) (h1 : term257) : term177 _4328 _4329.
Proof. exact (@lem215006 _4328 h1 _4329). Qed.
Lemma lem215008 (_4328 : nat) (_4329 : nat) : (term177 _4328 _4329) = ((Nat.mul _4329 _4328) = (Nat.mul _4328 _4329)).
Proof. exact (eq_refl (term177 _4328 _4329)). Qed.
Lemma lem215019 (_4333 : nat) (h1 : term257) : term243 _4333.
Proof. exact (@lem214986 h1 _4333). Qed.
Lemma lem215020 (_4333 : nat) : (term243 _4333) = (term211 _4333).
Proof. exact (eq_refl (term243 _4333)). Qed.
Lemma lem215021 (_4333 : nat) (h1 : term257) : term211 _4333.
Proof. exact (EQ_MP (@lem215020 _4333) (@lem215019 _4333 h1)). Qed.
Lemma lem215022 (_4333 : nat) (_4334 : nat) (h1 : term257) : term199 _4333 _4334.
Proof. exact (@lem215021 _4333 h1 _4334). Qed.
Lemma lem215023 (_4333 : nat) (_4334 : nat) : (term199 _4333 _4334) = (term167 _4333 _4334).
Proof. exact (eq_refl (term199 _4333 _4334)). Qed.
Lemma lem215024 (_4333 : nat) (_4334 : nat) (h1 : term257) : term167 _4333 _4334.
Proof. exact (EQ_MP (@lem215023 _4333 _4334) (@lem215022 _4333 _4334 h1)). Qed.
Lemma lem215025 (_4333 : nat) (_4334 : nat) (_4335 : nat) (h1 : term257) : term155 _4333 _4334 _4335.
Proof. exact (@lem215024 _4333 _4334 h1 _4335). Qed.
Lemma lem215026 (_4333 : nat) (_4334 : nat) (_4335 : nat) : (term155 _4333 _4334 _4335) = ((term152 _4334 _4333 _4335) = (term152 _4333 _4334 _4335)).
Proof. exact (eq_refl (term155 _4333 _4334 _4335)). Qed.
Lemma lem215033 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term95 b c a d) : term95 b c a d.
Proof. exact (h1). Qed.
Lemma lem215044 (_4326 : nat) (_4325 : nat) (_4327 : nat) : (term309 _4326 _4325 _4327) = (term320 _4326 _4325 _4327).
Proof. exact (@lem213296 (term54 _4325 _4326) (term321 _4326 _4327) (Peano.lt _4325 _4327)). Qed.
Lemma lem215045 (_4326 : nat) (_4325 : nat) (_4327 : nat) (h1 : term262) : term320 _4326 _4325 _4327.
Proof. exact (EQ_MP (@lem215044 _4326 _4325 _4327) (@lem215003 _4326 _4325 _4327 h1)). Qed.
Lemma lem215055 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) : term322 b k a d.
Proof. exact (proj2 (@lem214786 c b k a d h1)). Qed.
Lemma lem215056 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem215057 (_4336 : nat) (_4338 : nat) (h1 : _4336 = _4338) : _4336 = _4338.
Proof. exact (h1). Qed.
Lemma lem215058 (_4337 : nat) (_4339 : nat) (h1 : _4337 = _4339) : _4337 = _4339.
Proof. exact (h1). Qed.
Lemma lem215059 (_4336 : nat) (_4338 : nat) (h1 : _4336 = _4338) : (Peano.le _4336) = (Peano.le _4338).
Proof. exact (MK_COMB (@lem215056) (@lem215057 _4336 _4338 h1)). Qed.
Lemma lem215060 (_4336 : nat) (_4338 : nat) (_4337 : nat) (_4339 : nat) (h1 : _4336 = _4338) (h2 : _4337 = _4339) : (Peano.le _4336 _4337) = (Peano.le _4338 _4339).
Proof. exact (MK_COMB (@lem215059 _4336 _4338 h1) (@lem215058 _4337 _4339 h2)). Qed.
Lemma lem215062 (b : Prop) (a : Prop) : term323 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem215063 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : term324 _4338 _4339 _4336 _4337.
Proof. exact (@lem215062 (Peano.le _4338 _4339) (Peano.le _4336 _4337)). Qed.
Lemma lem215064 (_4336 : nat) (_4338 : nat) (_4337 : nat) (_4339 : nat) (h1 : _4336 = _4338) (h2 : _4337 = _4339) : term325 _4338 _4339 _4336 _4337.
Proof. exact (@lem215063 _4338 _4339 _4336 _4337 (@lem215060 _4336 _4338 _4337 _4339 h1 h2)). Qed.
Lemma lem215065 (_4339 : nat) (_4337 : nat) (_4336 : nat) (_4338 : nat) (h1 : _4336 = _4338) : term326 _4338 _4339 _4336 _4337.
Proof. exact (fun h0 : _4337 = _4339 => @lem215064 _4336 _4338 _4337 _4339 h1 h0). Qed.
Lemma lem215067 (a : Prop) (b : Prop) : (a -> b) = (term327 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem215068 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : (term326 _4338 _4339 _4336 _4337) = (term328 _4338 _4339 _4336 _4337).
Proof. exact (@lem215067 (_4337 = _4339) (term325 _4338 _4339 _4336 _4337)). Qed.
Lemma lem215069 (_4339 : nat) (_4337 : nat) (_4336 : nat) (_4338 : nat) (h1 : _4336 = _4338) : term328 _4338 _4339 _4336 _4337.
Proof. exact (EQ_MP (@lem215068 _4338 _4339 _4336 _4337) (@lem215065 _4339 _4337 _4336 _4338 h1)). Qed.
Lemma lem215070 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : term329 _4338 _4339 _4336 _4337.
Proof. exact (fun h0 : _4336 = _4338 => @lem215069 _4339 _4337 _4336 _4338 h0). Qed.
Lemma lem215072 (a : Prop) (b : Prop) : (a -> b) = (term327 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem215073 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : (term329 _4338 _4339 _4336 _4337) = (term330 _4338 _4339 _4336 _4337).
Proof. exact (@lem215072 (_4336 = _4338) (term328 _4338 _4339 _4336 _4337)). Qed.
Lemma lem215074 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : term330 _4338 _4339 _4336 _4337.
Proof. exact (EQ_MP (@lem215073 _4338 _4339 _4336 _4337) (@lem215070 _4338 _4339 _4336 _4337)). Qed.
Lemma lem215141 (x : nat) (y : nat) (z : nat) : term331 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem215143 (_4333 : nat) (_4334 : nat) (_4335 : nat) (h1 : term257) : (term152 _4334 _4333 _4335) = (term152 _4333 _4334 _4335).
Proof. exact (EQ_MP (@lem215026 _4333 _4334 _4335) (@lem215025 _4333 _4334 _4335 h1)). Qed.
Lemma lem215144 (b : nat) (d : nat) (k : nat) (h1 : term257) : (term152 d b k) = (term152 b d k).
Proof. exact (@lem215143 b d k h1). Qed.
Lemma lem215145 (b : nat) (d : nat) (k : nat) (h1 : term257) : term332 b d k.
Proof. exact (fun h0 : term333 b d k => @lem215144 b d k h1). Qed.
Lemma lem215147 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem215148 (b : nat) (d : nat) (k : nat) : (term332 b d k) = ((term152 d b k) = (term152 b d k)).
Proof. exact (@lem215147 ((term152 d b k) = (term152 b d k))). Qed.
Lemma lem215149 (b : nat) (d : nat) (k : nat) (h1 : term257) : (term152 d b k) = (term152 b d k).
Proof. exact (EQ_MP (@lem215148 b d k) (@lem215145 b d k h1)). Qed.
Lemma lem215151 (_4328 : nat) (_4329 : nat) (h1 : term257) : (Nat.mul _4329 _4328) = (Nat.mul _4328 _4329).
Proof. exact (EQ_MP (@lem215008 _4328 _4329) (@lem215007 _4328 _4329 h1)). Qed.
Lemma lem215152 (b : nat) (k : nat) (d : nat) (h1 : term257) : (term152 d b k) = (term151 b k d).
Proof. exact (@lem215151 (Nat.mul b k) d h1). Qed.
Lemma lem215153 (b : nat) (k : nat) (d : nat) (h1 : term257) : term334 b k d.
Proof. exact (fun h0 : term335 b k d => @lem215152 b k d h1). Qed.
Lemma lem215155 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem215156 (b : nat) (k : nat) (d : nat) : (term334 b k d) = ((term152 d b k) = (term151 b k d)).
Proof. exact (@lem215155 ((term152 d b k) = (term151 b k d))). Qed.
Lemma lem215157 (b : nat) (k : nat) (d : nat) (h1 : term257) : (term152 d b k) = (term151 b k d).
Proof. exact (EQ_MP (@lem215156 b k d) (@lem215153 b k d h1)). Qed.
Lemma lem215175 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem215176 (y : nat) (x : nat) (z : nat) : (term336 x y z) = (term337 y x z).
Proof. exact (@lem215175 (y = z) (term338 x z)). Qed.
Lemma lem215186 (x : nat) (y : nat) : (term339 x y) = (term339 x y).
Proof. exact (eq_refl (term339 x y)). Qed.
Lemma lem215187 (y : nat) (x : nat) (z : nat) : (term331 x y z) = (term340 y x z).
Proof. exact (MK_COMB (@lem215186 x y) (@lem215176 y x z)). Qed.
Lemma lem215191 (q : Prop) (p : Prop) (r : Prop) : (term20 p q r) = (term20 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem215192 (y : nat) (x : nat) (z : nat) : (term340 y x z) = (term341 y x z).
Proof. exact (@lem215191 (y = z) (term338 x y) (term338 x z)). Qed.
Lemma lem215214 (y : nat) (x : nat) (z : nat) : (term331 x y z) = (term341 y x z).
Proof. exact (TRANS (@lem215187 y x z) (@lem215192 y x z)). Qed.
Lemma lem215215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem215216 (y : nat) (x : nat) (z : nat) : (term342 x y z) = (term343 y x z).
Proof. exact (MK_COMB (@lem215215) (@lem215214 y x z)). Qed.
Lemma lem215238 (y : nat) (x : nat) (z : nat) : (term341 y x z) = (term341 y x z).
Proof. exact (eq_refl (term341 y x z)). Qed.
Lemma lem215239 (y : nat) (x : nat) (z : nat) : ((term331 x y z) = (term341 y x z)) = ((term341 y x z) = (term341 y x z)).
Proof. exact (MK_COMB (@lem215216 y x z) (@lem215238 y x z)). Qed.
Lemma lem215241 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem215242 (x : Prop) : (x = x) = True.
Proof. exact (@lem215241 Prop x). Qed.
Lemma lem215243 (y : nat) (x : nat) (z : nat) : ((term341 y x z) = (term341 y x z)) = True.
Proof. exact (@lem215242 (term341 y x z)). Qed.
Lemma lem215244 (y : nat) (x : nat) (z : nat) : ((term331 x y z) = (term341 y x z)) = True.
Proof. exact (TRANS (@lem215239 y x z) (@lem215243 y x z)). Qed.
Lemma lem215245 (y : nat) (x : nat) (z : nat) : True = ((term331 x y z) = (term341 y x z)).
Proof. exact (SYM (@lem215244 y x z)). Qed.
Lemma lem215246 (y : nat) (x : nat) (z : nat) : (term331 x y z) = (term341 y x z).
Proof. exact (EQ_MP (@lem215245 y x z) (@lem0)). Qed.
Lemma lem215247 (y : nat) (x : nat) (z : nat) : term341 y x z.
Proof. exact (EQ_MP (@lem215246 y x z) (@lem215141 x y z)). Qed.
Lemma lem215249 (b : Prop) (a : Prop) : (a \/ b) = (term67 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem215250 (x : nat) (y : nat) (z : nat) : (term341 y x z) = (term344 x y z).
Proof. exact (@lem215249 (term345 y x z) (y = z)). Qed.
Lemma lem215252 (a : Prop) (b : Prop) : (term346 a b) = (term347 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem215253 (y : nat) (x : nat) (z : nat) : (term348 y x z) = (term349 y x z).
Proof. exact (@lem215252 (term338 x y) (term338 x z)). Qed.
Lemma lem215255 (a : Prop) : (term69 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem215256 (x : nat) (y : nat) : (term350 x y) = (x = y).
Proof. exact (@lem215255 (x = y)). Qed.
Lemma lem215257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem215258 (x : nat) (y : nat) : (term351 x y) = (term352 x y).
Proof. exact (MK_COMB (@lem215257) (@lem215256 x y)). Qed.
Lemma lem215260 (a : Prop) : (term69 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem215261 (x : nat) (z : nat) : (term350 x z) = (x = z).
Proof. exact (@lem215260 (x = z)). Qed.
Lemma lem215262 (y : nat) (x : nat) (z : nat) : (term349 y x z) = (term353 y x z).
Proof. exact (MK_COMB (@lem215258 x y) (@lem215261 x z)). Qed.
Lemma lem215263 (y : nat) (x : nat) (z : nat) : (term348 y x z) = (term353 y x z).
Proof. exact (TRANS (@lem215253 y x z) (@lem215262 y x z)). Qed.
Lemma lem215264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem215265 (y : nat) (x : nat) (z : nat) : (term354 y x z) = (term355 y x z).
Proof. exact (MK_COMB (@lem215264) (@lem215263 y x z)). Qed.
Lemma lem215266 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem215267 (x : nat) (y : nat) (z : nat) : (term344 x y z) = (term356 x y z).
Proof. exact (MK_COMB (@lem215265 y x z) (@lem215266 y z)). Qed.
Lemma lem215268 (x : nat) (y : nat) (z : nat) : (term341 y x z) = (term356 x y z).
Proof. exact (TRANS (@lem215250 x y z) (@lem215267 x y z)). Qed.
Lemma lem215270 (b : nat) (k : nat) (d : nat) (h1 : term257) : term357 b k d.
Proof. exact (conj (@lem215149 b d k h1) (@lem215157 b k d h1)). Qed.
Lemma lem215272 (x : nat) (y : nat) (z : nat) : term356 x y z.
Proof. exact (EQ_MP (@lem215268 x y z) (@lem215247 y x z)). Qed.
Lemma lem215273 (b : nat) (k : nat) (d : nat) : term358 b k d.
Proof. exact (@lem215272 (term152 d b k) (term152 b d k) (term151 b k d)). Qed.
Lemma lem215276 (b : nat) (k : nat) (d : nat) (h1 : term257) : (term152 b d k) = (term151 b k d).
Proof. exact (@lem215273 b k d (@lem215270 b k d h1)). Qed.
Lemma lem215277 (b : nat) (k : nat) (d : nat) (h1 : term257) : term359 b k d.
Proof. exact (fun h0 : term360 b k d => @lem215276 b k d h1). Qed.
Lemma lem215279 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem215280 (b : nat) (k : nat) (d : nat) : (term359 b k d) = ((term152 b d k) = (term151 b k d)).
Proof. exact (@lem215279 ((term152 b d k) = (term151 b k d))). Qed.
Lemma lem215281 (b : nat) (k : nat) (d : nat) (h1 : term257) : (term152 b d k) = (term151 b k d).
Proof. exact (EQ_MP (@lem215280 b k d) (@lem215277 b k d h1)). Qed.
Lemma lem215283 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem215284 (b : nat) (c : nat) : (Nat.mul b c) = (Nat.mul b c).
Proof. exact (@lem215283 (Nat.mul b c)). Qed.
Lemma lem215285 (b : nat) (c : nat) : term361 b c.
Proof. exact (fun h0 : term362 b c => @lem215284 b c). Qed.
Lemma lem215287 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem215288 (b : nat) (c : nat) : (term361 b c) = ((Nat.mul b c) = (Nat.mul b c)).
Proof. exact (@lem215287 ((Nat.mul b c) = (Nat.mul b c))). Qed.
Lemma lem215289 (b : nat) (c : nat) : (Nat.mul b c) = (Nat.mul b c).
Proof. exact (EQ_MP (@lem215288 b c) (@lem215285 b c)). Qed.
Lemma lem215291 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) : term302 d k b c.
Proof. exact (proj1 (@lem214786 c b k a d h1)). Qed.
Lemma lem215292 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) : term363 d k b c.
Proof. exact (fun h0 : term364 d k b c => @lem215291 c b k a d h1). Qed.
Lemma lem215294 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem215295 (d : nat) (k : nat) (b : nat) (c : nat) : (term363 d k b c) = (term302 d k b c).
Proof. exact (@lem215294 (term302 d k b c)). Qed.
Lemma lem215296 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) : term302 d k b c.
Proof. exact (EQ_MP (@lem215295 d k b c) (@lem215292 c b k a d h1)). Qed.
Lemma lem215314 (q : Prop) (p : Prop) (r : Prop) : (term20 p q r) = (term20 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem215315 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : (term328 _4338 _4339 _4336 _4337) = (term365 _4338 _4339 _4336 _4337).
Proof. exact (@lem215314 (Peano.le _4338 _4339) (term338 _4337 _4339) (term54 _4336 _4337)). Qed.
Lemma lem215329 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem215330 (_4336 : nat) (_4337 : nat) (_4339 : nat) : (term366 _4339 _4336 _4337) = (term367 _4336 _4337 _4339).
Proof. exact (@lem215329 (term54 _4336 _4337) (term338 _4337 _4339)). Qed.
Lemma lem215338 (_4338 : nat) (_4339 : nat) : (term368 _4338 _4339) = (term368 _4338 _4339).
Proof. exact (eq_refl (term368 _4338 _4339)). Qed.
Lemma lem215339 (_4338 : nat) (_4336 : nat) (_4337 : nat) (_4339 : nat) : (term365 _4338 _4339 _4336 _4337) = (term369 _4338 _4336 _4337 _4339).
Proof. exact (MK_COMB (@lem215338 _4338 _4339) (@lem215330 _4336 _4337 _4339)). Qed.
Lemma lem215350 (_4338 : nat) (_4336 : nat) (_4337 : nat) (_4339 : nat) : (term328 _4338 _4339 _4336 _4337) = (term369 _4338 _4336 _4337 _4339).
Proof. exact (TRANS (@lem215315 _4338 _4339 _4336 _4337) (@lem215339 _4338 _4336 _4337 _4339)). Qed.
Lemma lem215351 (_4336 : nat) (_4338 : nat) : (term339 _4336 _4338) = (term339 _4336 _4338).
Proof. exact (eq_refl (term339 _4336 _4338)). Qed.
Lemma lem215352 (_4338 : nat) (_4336 : nat) (_4337 : nat) (_4339 : nat) : (term330 _4338 _4339 _4336 _4337) = (term370 _4338 _4336 _4337 _4339).
Proof. exact (MK_COMB (@lem215351 _4336 _4338) (@lem215350 _4338 _4336 _4337 _4339)). Qed.
Lemma lem215356 (q : Prop) (p : Prop) (r : Prop) : (term20 p q r) = (term20 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem215357 (_4338 : nat) (_4336 : nat) (_4337 : nat) (_4339 : nat) : (term370 _4338 _4336 _4337 _4339) = (term371 _4338 _4336 _4337 _4339).
Proof. exact (@lem215356 (Peano.le _4338 _4339) (term338 _4336 _4338) (term367 _4336 _4337 _4339)). Qed.
Lemma lem215371 (q : Prop) (p : Prop) (r : Prop) : (term20 p q r) = (term20 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem215372 (_4336 : nat) (_4338 : nat) (_4337 : nat) (_4339 : nat) : (term372 _4338 _4336 _4337 _4339) = (term373 _4336 _4338 _4337 _4339).
Proof. exact (@lem215371 (term54 _4336 _4337) (term338 _4336 _4338) (term338 _4337 _4339)). Qed.
Lemma lem215392 (_4338 : nat) (_4339 : nat) : (term368 _4338 _4339) = (term368 _4338 _4339).
Proof. exact (eq_refl (term368 _4338 _4339)). Qed.
Lemma lem215393 (_4336 : nat) (_4338 : nat) (_4337 : nat) (_4339 : nat) : (term371 _4338 _4336 _4337 _4339) = (term374 _4336 _4338 _4337 _4339).
Proof. exact (MK_COMB (@lem215392 _4338 _4339) (@lem215372 _4336 _4338 _4337 _4339)). Qed.
Lemma lem215404 (_4336 : nat) (_4338 : nat) (_4337 : nat) (_4339 : nat) : (term370 _4338 _4336 _4337 _4339) = (term374 _4336 _4338 _4337 _4339).
Proof. exact (TRANS (@lem215357 _4338 _4336 _4337 _4339) (@lem215393 _4336 _4338 _4337 _4339)). Qed.
Lemma lem215405 (_4336 : nat) (_4338 : nat) (_4337 : nat) (_4339 : nat) : (term330 _4338 _4339 _4336 _4337) = (term374 _4336 _4338 _4337 _4339).
Proof. exact (TRANS (@lem215352 _4338 _4336 _4337 _4339) (@lem215404 _4336 _4338 _4337 _4339)). Qed.
Lemma lem215406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem215407 (_4336 : nat) (_4338 : nat) (_4337 : nat) (_4339 : nat) : (term375 _4338 _4339 _4336 _4337) = (term376 _4336 _4338 _4337 _4339).
Proof. exact (MK_COMB (@lem215406) (@lem215405 _4336 _4338 _4337 _4339)). Qed.
Lemma lem215433 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem215434 (_4336 : nat) (_4337 : nat) (_4339 : nat) : (term366 _4339 _4336 _4337) = (term367 _4336 _4337 _4339).
Proof. exact (@lem215433 (term54 _4336 _4337) (term338 _4337 _4339)). Qed.
Lemma lem215442 (_4336 : nat) (_4338 : nat) : (term339 _4336 _4338) = (term339 _4336 _4338).
Proof. exact (eq_refl (term339 _4336 _4338)). Qed.
Lemma lem215443 (_4338 : nat) (_4336 : nat) (_4337 : nat) (_4339 : nat) : (term377 _4338 _4339 _4336 _4337) = (term372 _4338 _4336 _4337 _4339).
Proof. exact (MK_COMB (@lem215442 _4336 _4338) (@lem215434 _4336 _4337 _4339)). Qed.
Lemma lem215447 (q : Prop) (p : Prop) (r : Prop) : (term20 p q r) = (term20 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem215448 (_4336 : nat) (_4338 : nat) (_4337 : nat) (_4339 : nat) : (term372 _4338 _4336 _4337 _4339) = (term373 _4336 _4338 _4337 _4339).
Proof. exact (@lem215447 (term54 _4336 _4337) (term338 _4336 _4338) (term338 _4337 _4339)). Qed.
Lemma lem215468 (_4336 : nat) (_4338 : nat) (_4337 : nat) (_4339 : nat) : (term377 _4338 _4339 _4336 _4337) = (term373 _4336 _4338 _4337 _4339).
Proof. exact (TRANS (@lem215443 _4338 _4336 _4337 _4339) (@lem215448 _4336 _4338 _4337 _4339)). Qed.
Lemma lem215469 (_4338 : nat) (_4339 : nat) : (term368 _4338 _4339) = (term368 _4338 _4339).
Proof. exact (eq_refl (term368 _4338 _4339)). Qed.
Lemma lem215470 (_4336 : nat) (_4338 : nat) (_4337 : nat) (_4339 : nat) : (term378 _4338 _4339 _4336 _4337) = (term374 _4336 _4338 _4337 _4339).
Proof. exact (MK_COMB (@lem215469 _4338 _4339) (@lem215468 _4336 _4338 _4337 _4339)). Qed.
Lemma lem215481 (_4336 : nat) (_4338 : nat) (_4337 : nat) (_4339 : nat) : ((term330 _4338 _4339 _4336 _4337) = (term378 _4338 _4339 _4336 _4337)) = ((term374 _4336 _4338 _4337 _4339) = (term374 _4336 _4338 _4337 _4339)).
Proof. exact (MK_COMB (@lem215407 _4336 _4338 _4337 _4339) (@lem215470 _4336 _4338 _4337 _4339)). Qed.
Lemma lem215483 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem215484 (x : Prop) : (x = x) = True.
Proof. exact (@lem215483 Prop x). Qed.
Lemma lem215485 (_4336 : nat) (_4338 : nat) (_4337 : nat) (_4339 : nat) : ((term374 _4336 _4338 _4337 _4339) = (term374 _4336 _4338 _4337 _4339)) = True.
Proof. exact (@lem215484 (term374 _4336 _4338 _4337 _4339)). Qed.
Lemma lem215486 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : ((term330 _4338 _4339 _4336 _4337) = (term378 _4338 _4339 _4336 _4337)) = True.
Proof. exact (TRANS (@lem215481 _4336 _4338 _4337 _4339) (@lem215485 _4336 _4338 _4337 _4339)). Qed.
Lemma lem215487 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : True = ((term330 _4338 _4339 _4336 _4337) = (term378 _4338 _4339 _4336 _4337)).
Proof. exact (SYM (@lem215486 _4338 _4339 _4336 _4337)). Qed.
Lemma lem215488 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : (term330 _4338 _4339 _4336 _4337) = (term378 _4338 _4339 _4336 _4337).
Proof. exact (EQ_MP (@lem215487 _4338 _4339 _4336 _4337) (@lem0)). Qed.
Lemma lem215489 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : term378 _4338 _4339 _4336 _4337.
Proof. exact (EQ_MP (@lem215488 _4338 _4339 _4336 _4337) (@lem215074 _4338 _4339 _4336 _4337)). Qed.
Lemma lem215491 (b : Prop) (a : Prop) : (a \/ b) = (term67 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem215492 (_4336 : nat) (_4337 : nat) (_4338 : nat) (_4339 : nat) : (term378 _4338 _4339 _4336 _4337) = (term379 _4336 _4337 _4338 _4339).
Proof. exact (@lem215491 (term377 _4338 _4339 _4336 _4337) (Peano.le _4338 _4339)). Qed.
Lemma lem215494 (a : Prop) (b : Prop) : (term346 a b) = (term347 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem215495 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : (term380 _4338 _4339 _4336 _4337) = (term381 _4338 _4339 _4336 _4337).
Proof. exact (@lem215494 (term338 _4336 _4338) (term366 _4339 _4336 _4337)). Qed.
Lemma lem215497 (a : Prop) : (term69 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem215498 (_4336 : nat) (_4338 : nat) : (term350 _4336 _4338) = (_4336 = _4338).
Proof. exact (@lem215497 (_4336 = _4338)). Qed.
Lemma lem215499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem215500 (_4336 : nat) (_4338 : nat) : (term351 _4336 _4338) = (term352 _4336 _4338).
Proof. exact (MK_COMB (@lem215499) (@lem215498 _4336 _4338)). Qed.
Lemma lem215502 (a : Prop) (b : Prop) : (term346 a b) = (term347 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem215503 (_4339 : nat) (_4336 : nat) (_4337 : nat) : (term382 _4339 _4336 _4337) = (term383 _4339 _4336 _4337).
Proof. exact (@lem215502 (term338 _4337 _4339) (term54 _4336 _4337)). Qed.
Lemma lem215505 (a : Prop) : (term69 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem215506 (_4337 : nat) (_4339 : nat) : (term350 _4337 _4339) = (_4337 = _4339).
Proof. exact (@lem215505 (_4337 = _4339)). Qed.
Lemma lem215507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem215508 (_4337 : nat) (_4339 : nat) : (term351 _4337 _4339) = (term352 _4337 _4339).
Proof. exact (MK_COMB (@lem215507) (@lem215506 _4337 _4339)). Qed.
Lemma lem215510 (a : Prop) : (term69 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem215511 (_4336 : nat) (_4337 : nat) : (term70 _4336 _4337) = (Peano.le _4336 _4337).
Proof. exact (@lem215510 (Peano.le _4336 _4337)). Qed.
Lemma lem215512 (_4339 : nat) (_4336 : nat) (_4337 : nat) : (term383 _4339 _4336 _4337) = (term384 _4339 _4336 _4337).
Proof. exact (MK_COMB (@lem215508 _4337 _4339) (@lem215511 _4336 _4337)). Qed.
Lemma lem215513 (_4339 : nat) (_4336 : nat) (_4337 : nat) : (term382 _4339 _4336 _4337) = (term384 _4339 _4336 _4337).
Proof. exact (TRANS (@lem215503 _4339 _4336 _4337) (@lem215512 _4339 _4336 _4337)). Qed.
Lemma lem215514 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : (term381 _4338 _4339 _4336 _4337) = (term385 _4338 _4339 _4336 _4337).
Proof. exact (MK_COMB (@lem215500 _4336 _4338) (@lem215513 _4339 _4336 _4337)). Qed.
Lemma lem215515 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : (term380 _4338 _4339 _4336 _4337) = (term385 _4338 _4339 _4336 _4337).
Proof. exact (TRANS (@lem215495 _4338 _4339 _4336 _4337) (@lem215514 _4338 _4339 _4336 _4337)). Qed.
Lemma lem215516 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem215517 (_4338 : nat) (_4339 : nat) (_4336 : nat) (_4337 : nat) : (term386 _4338 _4339 _4336 _4337) = (term387 _4338 _4339 _4336 _4337).
Proof. exact (MK_COMB (@lem215516) (@lem215515 _4338 _4339 _4336 _4337)). Qed.
Lemma lem215518 (_4338 : nat) (_4339 : nat) : (Peano.le _4338 _4339) = (Peano.le _4338 _4339).
Proof. exact (eq_refl (Peano.le _4338 _4339)). Qed.
Lemma lem215519 (_4336 : nat) (_4337 : nat) (_4338 : nat) (_4339 : nat) : (term379 _4336 _4337 _4338 _4339) = (term388 _4336 _4337 _4338 _4339).
Proof. exact (MK_COMB (@lem215517 _4338 _4339 _4336 _4337) (@lem215518 _4338 _4339)). Qed.
Lemma lem215520 (_4336 : nat) (_4337 : nat) (_4338 : nat) (_4339 : nat) : (term378 _4338 _4339 _4336 _4337) = (term388 _4336 _4337 _4338 _4339).
Proof. exact (TRANS (@lem215492 _4336 _4337 _4338 _4339) (@lem215519 _4336 _4337 _4338 _4339)). Qed.
Lemma lem215522 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) : term389 d k b c.
Proof. exact (conj (@lem215289 b c) (@lem215296 c b k a d h1)). Qed.
Lemma lem215523 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) (h2 : term257) : term390 d k b c.
Proof. exact (conj (@lem215281 b k d h2) (@lem215522 c b k a d h1)). Qed.
Lemma lem215525 (_4336 : nat) (_4337 : nat) (_4338 : nat) (_4339 : nat) : term388 _4336 _4337 _4338 _4339.
Proof. exact (EQ_MP (@lem215520 _4336 _4337 _4338 _4339) (@lem215489 _4338 _4339 _4336 _4337)). Qed.
Lemma lem215526 (k : nat) (d : nat) (b : nat) (c : nat) : term391 k d b c.
Proof. exact (@lem215525 (term152 b d k) (Nat.mul b c) (term151 b k d) (Nat.mul b c)). Qed.
Lemma lem215529 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) (h2 : term257) : term392 k d b c.
Proof. exact (@lem215526 k d b c (@lem215523 c b k a d h1 h2)). Qed.
Lemma lem215530 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) (h2 : term257) : term393 k d b c.
Proof. exact (fun h0 : term394 k d b c => @lem215529 c b k a d h1 h2). Qed.
Lemma lem215532 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem215533 (k : nat) (d : nat) (b : nat) (c : nat) : (term393 k d b c) = (term392 k d b c).
Proof. exact (@lem215532 (term392 k d b c)). Qed.
Lemma lem215534 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) (h2 : term257) : term392 k d b c.
Proof. exact (EQ_MP (@lem215533 k d b c) (@lem215530 c b k a d h1 h2)). Qed.
Lemma lem215536 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term95 b c a d) : term95 b c a d.
Proof. exact (h1). Qed.
Lemma lem215537 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term95 b c a d) : term395 b c a d.
Proof. exact (fun h0 : term396 b c a d => @lem215536 b c a d h1). Qed.
Lemma lem215539 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem215540 (b : nat) (c : nat) (a : nat) (d : nat) : (term395 b c a d) = (term95 b c a d).
Proof. exact (@lem215539 (term95 b c a d)). Qed.
Lemma lem215541 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term95 b c a d) : term95 b c a d.
Proof. exact (EQ_MP (@lem215540 b c a d) (@lem215537 b c a d h1)). Qed.
Lemma lem215547 (q : Prop) (p : Prop) (r : Prop) : (term20 p q r) = (term20 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem215548 (_4326 : nat) (_4325 : nat) (_4327 : nat) : (term320 _4326 _4325 _4327) = (term397 _4326 _4325 _4327).
Proof. exact (@lem215547 (term321 _4326 _4327) (term54 _4325 _4326) (Peano.lt _4325 _4327)). Qed.
Lemma lem215562 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem215563 (_4327 : nat) (_4325 : nat) (_4326 : nat) : (term398 _4326 _4325 _4327) = (term399 _4327 _4325 _4326).
Proof. exact (@lem215562 (Peano.lt _4325 _4327) (term54 _4325 _4326)). Qed.
Lemma lem215569 (_4326 : nat) (_4327 : nat) : (term400 _4326 _4327) = (term400 _4326 _4327).
Proof. exact (eq_refl (term400 _4326 _4327)). Qed.
Lemma lem215570 (_4327 : nat) (_4325 : nat) (_4326 : nat) : (term397 _4326 _4325 _4327) = (term401 _4327 _4325 _4326).
Proof. exact (MK_COMB (@lem215569 _4326 _4327) (@lem215563 _4327 _4325 _4326)). Qed.
Lemma lem215574 (q : Prop) (p : Prop) (r : Prop) : (term20 p q r) = (term20 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem215575 (_4327 : nat) (_4325 : nat) (_4326 : nat) : (term401 _4327 _4325 _4326) = (term402 _4327 _4325 _4326).
Proof. exact (@lem215574 (Peano.lt _4325 _4327) (term321 _4326 _4327) (term54 _4325 _4326)). Qed.
Lemma lem215591 (_4327 : nat) (_4325 : nat) (_4326 : nat) : (term397 _4326 _4325 _4327) = (term402 _4327 _4325 _4326).
Proof. exact (TRANS (@lem215570 _4327 _4325 _4326) (@lem215575 _4327 _4325 _4326)). Qed.
Lemma lem215592 (_4327 : nat) (_4325 : nat) (_4326 : nat) : (term320 _4326 _4325 _4327) = (term402 _4327 _4325 _4326).
Proof. exact (TRANS (@lem215548 _4326 _4325 _4327) (@lem215591 _4327 _4325 _4326)). Qed.
Lemma lem215593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem215594 (_4327 : nat) (_4325 : nat) (_4326 : nat) : (term403 _4326 _4325 _4327) = (term404 _4327 _4325 _4326).
Proof. exact (MK_COMB (@lem215593) (@lem215592 _4327 _4325 _4326)). Qed.
Lemma lem215608 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem215609 (_4327 : nat) (_4325 : nat) (_4326 : nat) : (term305 _4325 _4326 _4327) = (term405 _4327 _4325 _4326).
Proof. exact (@lem215608 (term321 _4326 _4327) (term54 _4325 _4326)). Qed.
Lemma lem215615 (_4325 : nat) (_4327 : nat) : (term406 _4325 _4327) = (term406 _4325 _4327).
Proof. exact (eq_refl (term406 _4325 _4327)). Qed.
Lemma lem215616 (_4327 : nat) (_4325 : nat) (_4326 : nat) : (term407 _4325 _4326 _4327) = (term402 _4327 _4325 _4326).
Proof. exact (MK_COMB (@lem215615 _4325 _4327) (@lem215609 _4327 _4325 _4326)). Qed.
Lemma lem215627 (_4327 : nat) (_4325 : nat) (_4326 : nat) : ((term320 _4326 _4325 _4327) = (term407 _4325 _4326 _4327)) = ((term402 _4327 _4325 _4326) = (term402 _4327 _4325 _4326)).
Proof. exact (MK_COMB (@lem215594 _4327 _4325 _4326) (@lem215616 _4327 _4325 _4326)). Qed.
Lemma lem215629 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem215630 (x : Prop) : (x = x) = True.
Proof. exact (@lem215629 Prop x). Qed.
Lemma lem215631 (_4327 : nat) (_4325 : nat) (_4326 : nat) : ((term402 _4327 _4325 _4326) = (term402 _4327 _4325 _4326)) = True.
Proof. exact (@lem215630 (term402 _4327 _4325 _4326)). Qed.
Lemma lem215632 (_4325 : nat) (_4326 : nat) (_4327 : nat) : ((term320 _4326 _4325 _4327) = (term407 _4325 _4326 _4327)) = True.
Proof. exact (TRANS (@lem215627 _4327 _4325 _4326) (@lem215631 _4327 _4325 _4326)). Qed.
Lemma lem215633 (_4325 : nat) (_4326 : nat) (_4327 : nat) : True = ((term320 _4326 _4325 _4327) = (term407 _4325 _4326 _4327)).
Proof. exact (SYM (@lem215632 _4325 _4326 _4327)). Qed.
Lemma lem215634 (_4325 : nat) (_4326 : nat) (_4327 : nat) : (term320 _4326 _4325 _4327) = (term407 _4325 _4326 _4327).
Proof. exact (EQ_MP (@lem215633 _4325 _4326 _4327) (@lem0)). Qed.
Lemma lem215635 (_4325 : nat) (_4326 : nat) (_4327 : nat) (h1 : term262) : term407 _4325 _4326 _4327.
Proof. exact (EQ_MP (@lem215634 _4325 _4326 _4327) (@lem215045 _4326 _4325 _4327 h1)). Qed.
Lemma lem215637 (b : Prop) (a : Prop) : (a \/ b) = (term67 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem215638 (_4326 : nat) (_4325 : nat) (_4327 : nat) : (term407 _4325 _4326 _4327) = (term408 _4326 _4325 _4327).
Proof. exact (@lem215637 (term305 _4325 _4326 _4327) (Peano.lt _4325 _4327)). Qed.
Lemma lem215640 (a : Prop) (b : Prop) : (term346 a b) = (term347 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem215641 (_4325 : nat) (_4326 : nat) (_4327 : nat) : (term409 _4325 _4326 _4327) = (term410 _4325 _4326 _4327).
Proof. exact (@lem215640 (term54 _4325 _4326) (term321 _4326 _4327)). Qed.
Lemma lem215643 (a : Prop) : (term69 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem215644 (_4325 : nat) (_4326 : nat) : (term70 _4325 _4326) = (Peano.le _4325 _4326).
Proof. exact (@lem215643 (Peano.le _4325 _4326)). Qed.
Lemma lem215645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem215646 (_4325 : nat) (_4326 : nat) : (term411 _4325 _4326) = (term412 _4325 _4326).
Proof. exact (MK_COMB (@lem215645) (@lem215644 _4325 _4326)). Qed.
Lemma lem215648 (a : Prop) : (term69 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem215649 (_4326 : nat) (_4327 : nat) : (term413 _4326 _4327) = (Peano.lt _4326 _4327).
Proof. exact (@lem215648 (Peano.lt _4326 _4327)). Qed.
Lemma lem215650 (_4325 : nat) (_4326 : nat) (_4327 : nat) : (term410 _4325 _4326 _4327) = (term310 _4325 _4326 _4327).
Proof. exact (MK_COMB (@lem215646 _4325 _4326) (@lem215649 _4326 _4327)). Qed.
Lemma lem215651 (_4325 : nat) (_4326 : nat) (_4327 : nat) : (term409 _4325 _4326 _4327) = (term310 _4325 _4326 _4327).
Proof. exact (TRANS (@lem215641 _4325 _4326 _4327) (@lem215650 _4325 _4326 _4327)). Qed.
Lemma lem215652 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem215653 (_4325 : nat) (_4326 : nat) (_4327 : nat) : (term414 _4325 _4326 _4327) = (term415 _4325 _4326 _4327).
Proof. exact (MK_COMB (@lem215652) (@lem215651 _4325 _4326 _4327)). Qed.
Lemma lem215654 (_4325 : nat) (_4327 : nat) : (Peano.lt _4325 _4327) = (Peano.lt _4325 _4327).
Proof. exact (eq_refl (Peano.lt _4325 _4327)). Qed.
Lemma lem215655 (_4326 : nat) (_4325 : nat) (_4327 : nat) : (term408 _4326 _4325 _4327) = (term295 _4326 _4325 _4327).
Proof. exact (MK_COMB (@lem215653 _4325 _4326 _4327) (@lem215654 _4325 _4327)). Qed.
Lemma lem215656 (_4326 : nat) (_4325 : nat) (_4327 : nat) : (term407 _4325 _4326 _4327) = (term295 _4326 _4325 _4327).
Proof. exact (TRANS (@lem215638 _4326 _4325 _4327) (@lem215655 _4326 _4325 _4327)). Qed.
Lemma lem215658 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) (h2 : term257) (h3 : term95 b c a d) : term416 k b c a d.
Proof. exact (conj (@lem215534 c b k a d h1 h2) (@lem215541 b c a d h3)). Qed.
Lemma lem215660 (_4326 : nat) (_4325 : nat) (_4327 : nat) (h1 : term262) : term295 _4326 _4325 _4327.
Proof. exact (EQ_MP (@lem215656 _4326 _4325 _4327) (@lem215635 _4325 _4326 _4327 h1)). Qed.
Lemma lem215661 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term262) : term417 c b k a d.
Proof. exact (@lem215660 (Nat.mul b c) (term151 b k d) (term92 a d) h1). Qed.
Lemma lem215664 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : term303 b k a d.
Proof. exact (@lem215661 c b k a d h1 (@lem215658 k b c a d h2 h3 h4)). Qed.
Lemma lem215665 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : term418 b k a d.
Proof. exact (fun h0 : term322 b k a d => @lem215664 k b c a d h1 h2 h3 h4). Qed.
Lemma lem215667 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem215668 (b : nat) (k : nat) (a : nat) (d : nat) : (term418 b k a d) = (term303 b k a d).
Proof. exact (@lem215667 (term303 b k a d)). Qed.
Lemma lem215669 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : term303 b k a d.
Proof. exact (EQ_MP (@lem215668 b k a d) (@lem215665 k b c a d h1 h2 h3 h4)). Qed.
Lemma lem215672 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem215674 (b : nat) (k : nat) (a : nat) (d : nat) : (term322 b k a d) = (term419 b k a d).
Proof. exact (@lem215672 (term303 b k a d)). Qed.
Lemma lem215677 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) : term419 b k a d.
Proof. exact (EQ_MP (@lem215674 b k a d) (@lem215055 c b k a d h1)). Qed.
Lemma lem215680 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : False.
Proof. exact (@lem215677 c b k a d h2 (@lem215669 k b c a d h1 h2 h3 h4)). Qed.
Lemma lem215681 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : term76.
Proof. exact (fun h0 : ~ False => @lem215680 k b c a d h1 h2 h3 h4). Qed.
Lemma lem215683 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem215684 : term76 = False.
Proof. exact (@lem215683 False). Qed.
Lemma lem215685 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : False.
Proof. exact (EQ_MP (@lem215684) (@lem215681 k b c a d h1 h2 h3 h4)). Qed.
Lemma lem215686 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : (term95 b c a d) = False.
Proof. exact (prop_ext (fun h5 : term95 b c a d => @lem215685 k b c a d h1 h2 h3 h4) (fun h5 : False => @lem215033 b c a d h4)). Qed.
Lemma lem215687 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : False.
Proof. exact (EQ_MP (@lem215686 k b c a d h1 h2 h3 h4) (@lem215033 b c a d h4)). Qed.
Lemma lem215688 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : (term95 b c a d) = False.
Proof. exact (prop_ext (fun h5 : term95 b c a d => @lem215687 k b c a d h1 h2 h3 h4) (fun h5 : False => @lem214925 b c a d h4)). Qed.
Lemma lem215689 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : False.
Proof. exact (EQ_MP (@lem215688 k b c a d h1 h2 h3 h4) (@lem214925 b c a d h4)). Qed.
Lemma lem215690 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : (term95 b c a d) = False.
Proof. exact (prop_ext (fun h5 : term95 b c a d => @lem215689 k b c a d h1 h2 h3 h4) (fun h5 : False => @lem214925 b c a d h4)). Qed.
Lemma lem215691 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : False.
Proof. exact (EQ_MP (@lem215690 k b c a d h1 h2 h3 h4) (@lem214925 b c a d h4)). Qed.
Lemma lem215692 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : term257 = False.
Proof. exact (prop_ext (fun h5 : term257 => @lem215691 k b c a d h1 h2 h3 h4) (fun h5 : False => @lem214872 h3)). Qed.
Lemma lem215693 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : False.
Proof. exact (EQ_MP (@lem215692 k b c a d h1 h2 h3 h4) (@lem214872 h3)). Qed.
Lemma lem215694 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : (term95 b c a d) = False.
Proof. exact (prop_ext (fun h5 : term95 b c a d => @lem215693 k b c a d h1 h2 h3 h4) (fun h5 : False => @lem214738 b c a d h4)). Qed.
Lemma lem215695 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : False.
Proof. exact (EQ_MP (@lem215694 k b c a d h1 h2 h3 h4) (@lem214738 b c a d h4)). Qed.
Lemma lem215696 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : term257 = False.
Proof. exact (prop_ext (fun h5 : term257 => @lem215695 k b c a d h1 h2 h3 h4) (fun h5 : False => @lem214613 h3)). Qed.
Lemma lem215697 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : False.
Proof. exact (EQ_MP (@lem215696 k b c a d h1 h2 h3 h4) (@lem214613 h3)). Qed.
Lemma lem215698 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : (term95 b c a d) = False.
Proof. exact (prop_ext (fun h5 : term95 b c a d => @lem215697 k b c a d h1 h2 h3 h4) (fun h5 : False => @lem214531 b c a d h4)). Qed.
Lemma lem215699 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term262) (h2 : term111 c b k a d) (h3 : term257) (h4 : term95 b c a d) : False.
Proof. exact (EQ_MP (@lem215698 k b c a d h1 h2 h3 h4) (@lem214531 b c a d h4)). Qed.
Lemma lem215700 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) (h2 : term257) (h3 : term95 b c a d) : term260.
Proof. exact (fun h0 : term262 => @lem215699 k b c a d h0 h1 h2 h3). Qed.
Lemma lem215701 : term260 = term261.
Proof. exact (@lem69 term262). Qed.
Lemma lem215702 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) (h2 : term257) (h3 : term95 b c a d) : term261.
Proof. exact (EQ_MP (@lem215701) (@lem215700 k b c a d h1 h2 h3)). Qed.
Lemma lem215703 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term111 c b k a d) (h2 : term95 b c a d) : term264.
Proof. exact (fun h0 : term257 => @lem215702 k b c a d h1 h0 h2). Qed.
Lemma lem215704 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term95 b c a d) : term267 c b k a d.
Proof. exact (fun h0 : term111 c b k a d => @lem215703 k b c a d h0 h1). Qed.
Lemma lem215705 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : term270 c b k a d.
Proof. exact (fun h0 : term95 b c a d => @lem215704 k b c a d h0). Qed.
Lemma lem215706 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : term273 c b k a d.
Proof. exact (fun h0 : term83 b => @lem215705 c b k a d). Qed.
Lemma lem215707 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : term274 c b k a d.
Proof. exact (fun h0 : term83 d => @lem215706 c b k a d). Qed.
Lemma lem215712 (b : nat) (k : nat) (a : nat) (d : nat) : term278 b k a d.
Proof. exact (fun c : nat => @lem215707 c b k a d). Qed.
Lemma lem215717 (k : nat) (a : nat) (d : nat) : term282 k a d.
Proof. exact (fun b : nat => @lem215712 b k a d). Qed.
Lemma lem215722 (a : nat) (d : nat) : term286 a d.
Proof. exact (fun k : nat => @lem215717 k a d). Qed.
Lemma lem215727 (d : nat) : term290 d.
Proof. exact (fun a : nat => @lem215722 a d). Qed.
Lemma lem215732 : term294.
Proof. exact (fun d : nat => @lem215727 d). Qed.
Lemma lem215733 : term293.
Proof. exact (EQ_MP (@lem214507) (@lem215732)). Qed.
Lemma lem215734 (d : nat) : term420 d.
Proof. exact (@lem215733 d). Qed.
Lemma lem215735 (d : nat) : (term420 d) = (term289 d).
Proof. exact (eq_refl (term420 d)). Qed.
Lemma lem215736 (d : nat) : term289 d.
Proof. exact (EQ_MP (@lem215735 d) (@lem215734 d)). Qed.
Lemma lem215737 (d : nat) (a : nat) : term421 d a.
Proof. exact (@lem215736 d a). Qed.
Lemma lem215738 (a : nat) (d : nat) : (term421 d a) = (term285 a d).
Proof. exact (eq_refl (term421 d a)). Qed.
Lemma lem215739 (a : nat) (d : nat) : term285 a d.
Proof. exact (EQ_MP (@lem215738 a d) (@lem215737 d a)). Qed.
Lemma lem215740 (a : nat) (d : nat) (k : nat) : term422 a d k.
Proof. exact (@lem215739 a d k). Qed.
Lemma lem215741 (k : nat) (a : nat) (d : nat) : (term422 a d k) = (term281 k a d).
Proof. exact (eq_refl (term422 a d k)). Qed.
Lemma lem215742 (k : nat) (a : nat) (d : nat) : term281 k a d.
Proof. exact (EQ_MP (@lem215741 k a d) (@lem215740 a d k)). Qed.
Lemma lem215743 (k : nat) (a : nat) (d : nat) (b : nat) : term423 k a d b.
Proof. exact (@lem215742 k a d b). Qed.
Lemma lem215744 (b : nat) (k : nat) (a : nat) (d : nat) : (term423 k a d b) = (term277 b k a d).
Proof. exact (eq_refl (term423 k a d b)). Qed.
Lemma lem215745 (b : nat) (k : nat) (a : nat) (d : nat) : term277 b k a d.
Proof. exact (EQ_MP (@lem215744 b k a d) (@lem215743 k a d b)). Qed.
Lemma lem215746 (b : nat) (k : nat) (a : nat) (d : nat) (c : nat) : term424 b k a d c.
Proof. exact (@lem215745 b k a d c). Qed.
Lemma lem215747 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : (term424 b k a d c) = (term112 c b k a d).
Proof. exact (eq_refl (term424 b k a d c)). Qed.
Lemma lem215748 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : term112 c b k a d.
Proof. exact (EQ_MP (@lem215747 c b k a d) (@lem215746 b k a d c)). Qed.
Lemma lem215750 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) : term112 c b k a d.
Proof. exact (@lem213909 c b k a d (@lem215748 c b k a d)). Qed.
Lemma lem215751 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term83 d) : term272 c b k a d.
Proof. exact (@lem215750 c b k a d (@lem213728 d h1)). Qed.
Lemma lem215752 (c : nat) (k : nat) (a : nat) (b : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) : term269 c b k a d.
Proof. exact (@lem215751 c b k a d h2 (@lem213885 b h1)). Qed.
Lemma lem215753 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term95 b c a d) : term266 c b k a d.
Proof. exact (@lem215752 c k a b d h1 h2 (@lem213884 b c a d h3)). Qed.
Lemma lem215754 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term111 c b k a d) (h4 : term95 b c a d) : term263.
Proof. exact (@lem215753 k b c a d h1 h2 h4 (@lem213894 c b k a d h3)). Qed.
Lemma lem215755 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term111 c b k a d) (h4 : term95 b c a d) : term260.
Proof. exact (@lem215754 k b c a d h1 h2 h3 h4 (@lem213299)). Qed.
Lemma lem215756 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term111 c b k a d) (h4 : term95 b c a d) : False.
Proof. exact (@lem215755 k b c a d h1 h2 h3 h4 (@lem95173)). Qed.
Lemma lem215757 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term111 c b k a d) (h4 : term95 b c a d) : (term111 c b k a d) = False.
Proof. exact (prop_ext (fun h5 : term111 c b k a d => @lem215756 k b c a d h1 h2 h3 h4) (fun h5 : False => @lem213894 c b k a d h3)). Qed.
Lemma lem215758 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term111 c b k a d) (h4 : term95 b c a d) : False.
Proof. exact (EQ_MP (@lem215757 k b c a d h1 h2 h3 h4) (@lem213894 c b k a d h3)). Qed.
Lemma lem215759 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term95 b c a d) : term110 c b k a d.
Proof. exact (fun h0 : term111 c b k a d => @lem215758 k b c a d h1 h2 h0 h3). Qed.
Lemma lem215760 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term95 b c a d) : term109 c b k a d.
Proof. exact (EQ_MP (@lem213893 c b k a d) (@lem215759 k b c a d h1 h2 h3)). Qed.
Lemma lem215762 (A : Prop) (C : Prop) (B : Prop) (D : Prop) : term10 A C B D.
Proof. exact (@lem213285 A C B D (@lem7250 A C B D)). Qed.
Lemma lem215763 (c : nat) (d : nat) (k : nat) (a : nat) (b : nat) : term425 c d k a b.
Proof. exact (@lem215762 (term302 d k b c) (term303 b k a d) (term426 k c d) (term426 k a b)). Qed.
Lemma lem215764 (a : nat) : term427 a.
Proof. exact (@lem188842 a). Qed.
Lemma lem215765 (a : nat) : (term427 a) = (term428 a).
Proof. exact (eq_refl (term427 a)). Qed.
Lemma lem215766 (a : nat) : term428 a.
Proof. exact (EQ_MP (@lem215765 a) (@lem215764 a)). Qed.
Lemma lem215767 (a : nat) (b : nat) : term429 a b.
Proof. exact (@lem215766 a b). Qed.
Lemma lem215768 (a : nat) (b : nat) : (term429 a b) = (term430 a b).
Proof. exact (eq_refl (term429 a b)). Qed.
Lemma lem215769 (a : nat) (b : nat) : term430 a b.
Proof. exact (EQ_MP (@lem215768 a b) (@lem215767 a b)). Qed.
Lemma lem215770 (a : nat) (b : nat) (n : nat) : term431 a b n.
Proof. exact (@lem215769 a b n). Qed.
Lemma lem215771 (a : nat) (n : nat) (b : nat) : (term431 a b n) = (term432 a n b).
Proof. exact (eq_refl (term431 a b n)). Qed.
Lemma lem215772 (a : nat) (n : nat) (b : nat) : term432 a n b.
Proof. exact (EQ_MP (@lem215771 a n b) (@lem215770 a b n)). Qed.
Lemma lem215773 (a : nat) (h1 : term83 a) : term83 a.
Proof. exact (h1). Qed.
Lemma lem215774 (n : nat) (b : nat) (a : nat) (h1 : term83 a) : (term426 n b a) = (term433 a n b).
Proof. exact (@lem215772 a n b (@lem215773 a h1)). Qed.
Lemma lem215780 (m : nat) : term434 m.
Proof. exact (@lem105963 m). Qed.
Lemma lem215781 (m : nat) : (term434 m) = (term435 m).
Proof. exact (eq_refl (term434 m)). Qed.
Lemma lem215782 (m : nat) : term435 m.
Proof. exact (EQ_MP (@lem215781 m) (@lem215780 m)). Qed.
Lemma lem215783 (m : nat) (n : nat) : term436 m n.
Proof. exact (@lem215782 m n). Qed.
Lemma lem215784 (m : nat) (n : nat) : (term436 m n) = (term437 m n).
Proof. exact (eq_refl (term436 m n)). Qed.
Lemma lem215785 (m : nat) (n : nat) : term437 m n.
Proof. exact (EQ_MP (@lem215784 m n) (@lem215783 m n)). Qed.
Lemma lem215786 (m : nat) (n : nat) (p : nat) : term438 m n p.
Proof. exact (@lem215785 m n p). Qed.
Lemma lem215787 (m : nat) (n : nat) (p : nat) : (term438 m n p) = ((term439 m n p) = (term440 m n p)).
Proof. exact (eq_refl (term438 m n p)). Qed.
Lemma lem215789 (m : nat) : term441 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem215790 (m : nat) : (term441 m) = (term442 m).
Proof. exact (eq_refl (term441 m)). Qed.
Lemma lem215791 (m : nat) : term442 m.
Proof. exact (EQ_MP (@lem215790 m) (@lem215789 m)). Qed.
Lemma lem215792 (m : nat) (n : nat) : term443 m n.
Proof. exact (@lem215791 m n). Qed.
Lemma lem215793 (m : nat) (n : nat) : (term443 m n) = (term444 m n).
Proof. exact (eq_refl (term443 m n)). Qed.
Lemma lem215794 (m : nat) (n : nat) : term444 m n.
Proof. exact (EQ_MP (@lem215793 m n) (@lem215792 m n)). Qed.
Lemma lem215795 (m : nat) (n : nat) (p : nat) : term445 m n p.
Proof. exact (@lem215794 m n p). Qed.
Lemma lem215796 (m : nat) (n : nat) (p : nat) : (term445 m n p) = ((term446 n m p) = (term447 m n p)).
Proof. exact (eq_refl (term445 m n p)). Qed.
Lemma lem215798 (d : nat) : term448 d.
Proof. exact (@lem82 (d = (NUMERAL 0))). Qed.
Lemma lem215811 (b : nat) : term448 b.
Proof. exact (@lem82 (b = (NUMERAL 0))). Qed.
Lemma lem215831 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term449 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem215832 (p : Prop) (q : Prop) (p' : Prop) : term450 p q p'.
Proof. exact (fun q' : Prop => @lem215831 p q p' q'). Qed.
Lemma lem215833 (p : Prop) (q : Prop) : term451 p q.
Proof. exact (fun p' : Prop => @lem215832 p q p'). Qed.
Lemma lem215834 (d : nat) (k : nat) (b : nat) (c : nat) : term452 d k b c.
Proof. exact (@lem215833 (term426 k c d) (term302 d k b c)). Qed.
Lemma lem215835 (d : nat) (k : nat) (b : nat) (c : nat) (p' : Prop) : term453 d k b c p'.
Proof. exact (@lem215834 d k b c p'). Qed.
Lemma lem215836 (d : nat) (k : nat) (b : nat) (c : nat) (p' : Prop) : (term453 d k b c p') = (term454 d k b c p').
Proof. exact (eq_refl (term453 d k b c p')). Qed.
Lemma lem215837 (d : nat) (k : nat) (b : nat) (c : nat) (p' : Prop) : term454 d k b c p'.
Proof. exact (EQ_MP (@lem215836 d k b c p') (@lem215835 d k b c p')). Qed.
Lemma lem215838 (d : nat) (k : nat) (b : nat) (c : nat) (p' : Prop) (q' : Prop) : term455 d k b c p' q'.
Proof. exact (@lem215837 d k b c p' q'). Qed.
Lemma lem215839 (d : nat) (k : nat) (b : nat) (c : nat) (p' : Prop) (q' : Prop) : (term455 d k b c p' q') = (term456 d k b c p' q').
Proof. exact (eq_refl (term455 d k b c p' q')). Qed.
Lemma lem215840 (d : nat) (k : nat) (b : nat) (c : nat) (p' : Prop) (q' : Prop) : term456 d k b c p' q'.
Proof. exact (EQ_MP (@lem215839 d k b c p' q') (@lem215838 d k b c p' q')). Qed.
Lemma lem215842 (a : nat) (n : nat) (b : nat) : term432 a n b.
Proof. exact (fun h0 : term83 a => @lem215774 n b a h0). Qed.
Lemma lem215843 (d : nat) (k : nat) (c : nat) : term432 d k c.
Proof. exact (@lem215842 d k c). Qed.
Lemma lem215845 (d : nat) (h1 : term83 d) : (d = (NUMERAL 0)) = False.
Proof. exact (@lem215798 d (@lem213728 d h1)). Qed.
Lemma lem215846 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem215847 (d : nat) (h1 : term83 d) : (term83 d) = (~ False).
Proof. exact (MK_COMB (@lem215846) (@lem215845 d h1)). Qed.
Lemma lem215849 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem215850 (d : nat) (h1 : term83 d) : (term83 d) = True.
Proof. exact (TRANS (@lem215847 d h1) (@lem215849)). Qed.
Lemma lem215851 (d : nat) (h1 : term83 d) : True = (term83 d).
Proof. exact (SYM (@lem215850 d h1)). Qed.
Lemma lem215852 (d : nat) (h1 : term83 d) : term83 d.
Proof. exact (EQ_MP (@lem215851 d h1) (@lem0)). Qed.
Lemma lem215853 (k : nat) (c : nat) (d : nat) (h1 : term83 d) : (term426 k c d) = (term433 d k c).
Proof. exact (@lem215843 d k c (@lem215852 d h1)). Qed.
Lemma lem215854 (b : nat) (d : nat) (k : nat) (c : nat) (q' : Prop) : term457 b d k c q'.
Proof. exact (@lem215840 d k b c (term433 d k c) q'). Qed.
Lemma lem215855 (b : nat) (k : nat) (c : nat) (q' : Prop) (d : nat) (h1 : term83 d) : term458 b d k c q'.
Proof. exact (@lem215854 b d k c q' (@lem215853 k c d h1)). Qed.
Lemma lem215856 (d : nat) (k : nat) (c : nat) (h1 : term433 d k c) : term433 d k c.
Proof. exact (h1). Qed.
Lemma lem215857 (d : nat) (k : nat) (c : nat) : (term433 d k c) = ((term433 d k c) = True).
Proof. exact (@lem7 (term433 d k c)). Qed.
Lemma lem215860 (m : nat) (n : nat) (p : nat) : (term446 n m p) = (term447 m n p).
Proof. exact (EQ_MP (@lem215796 m n p) (@lem215795 m n p)). Qed.
Lemma lem215861 (b : nat) (d : nat) (k : nat) (c : nat) : (term302 d k b c) = (term459 b d k c).
Proof. exact (@lem215860 b (Nat.mul d k) c). Qed.
Lemma lem215865 (b : nat) (h1 : term83 b) : (b = (NUMERAL 0)) = False.
Proof. exact (@lem215811 b (@lem213885 b h1)). Qed.
Lemma lem215866 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem215867 (b : nat) (h1 : term83 b) : (term460 b) = (or False).
Proof. exact (MK_COMB (@lem215866) (@lem215865 b h1)). Qed.
Lemma lem215869 (d : nat) (k : nat) (c : nat) (h1 : term433 d k c) : (term433 d k c) = True.
Proof. exact (EQ_MP (@lem215857 d k c) (@lem215856 d k c h1)). Qed.
Lemma lem215870 (b : nat) (d : nat) (k : nat) (c : nat) (h1 : term83 b) (h2 : term433 d k c) : (term459 b d k c) = (False \/ True).
Proof. exact (MK_COMB (@lem215867 b h1) (@lem215869 d k c h2)). Qed.
Lemma lem215872 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem215873 : (False \/ True) = True.
Proof. exact (@lem215872 True). Qed.
Lemma lem215874 (b : nat) (d : nat) (k : nat) (c : nat) (h1 : term83 b) (h2 : term433 d k c) : (term459 b d k c) = True.
Proof. exact (TRANS (@lem215870 b d k c h1 h2) (@lem215873)). Qed.
Lemma lem215875 (b : nat) (d : nat) (k : nat) (c : nat) (h1 : term83 b) (h2 : term433 d k c) : (term302 d k b c) = True.
Proof. exact (TRANS (@lem215861 b d k c) (@lem215874 b d k c h1 h2)). Qed.
Lemma lem215876 (d : nat) (k : nat) (c : nat) (b : nat) (h1 : term83 b) : term461 d k b c.
Proof. exact (fun h0 : term433 d k c => @lem215875 b d k c h1 h0). Qed.
Lemma lem215877 (b : nat) (k : nat) (c : nat) (d : nat) (h1 : term83 d) : term462 b d k c.
Proof. exact (@lem215855 b k c True d h1). Qed.
Lemma lem215878 (k : nat) (c : nat) (b : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) : (term463 d k b c) = (term464 d k c).
Proof. exact (@lem215877 b k c d h2 (@lem215876 d k c b h1)). Qed.
Lemma lem215880 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem215881 (d : nat) (k : nat) (c : nat) : (term464 d k c) = True.
Proof. exact (@lem215880 (term433 d k c)). Qed.
Lemma lem215882 (k : nat) (c : nat) (b : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) : (term463 d k b c) = True.
Proof. exact (TRANS (@lem215878 k c b d h1 h2) (@lem215881 d k c)). Qed.
Lemma lem215883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem215884 (k : nat) (c : nat) (b : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) : (term465 d k b c) = (and True).
Proof. exact (MK_COMB (@lem215883) (@lem215882 k c b d h1 h2)). Qed.
Lemma lem215888 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term449 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem215889 (p : Prop) (q : Prop) (p' : Prop) : term450 p q p'.
Proof. exact (fun q' : Prop => @lem215888 p q p' q'). Qed.
Lemma lem215890 (p : Prop) (q : Prop) : term451 p q.
Proof. exact (fun p' : Prop => @lem215889 p q p'). Qed.
Lemma lem215891 (d : nat) (k : nat) (a : nat) (b : nat) : term466 d k a b.
Proof. exact (@lem215890 (term303 b k a d) (term426 k a b)). Qed.
Lemma lem215892 (d : nat) (k : nat) (a : nat) (b : nat) (p' : Prop) : term467 d k a b p'.
Proof. exact (@lem215891 d k a b p'). Qed.
Lemma lem215893 (d : nat) (k : nat) (a : nat) (b : nat) (p' : Prop) : (term467 d k a b p') = (term468 d k a b p').
Proof. exact (eq_refl (term467 d k a b p')). Qed.
Lemma lem215894 (d : nat) (k : nat) (a : nat) (b : nat) (p' : Prop) : term468 d k a b p'.
Proof. exact (EQ_MP (@lem215893 d k a b p') (@lem215892 d k a b p')). Qed.
Lemma lem215895 (d : nat) (k : nat) (a : nat) (b : nat) (p' : Prop) (q' : Prop) : term469 d k a b p' q'.
Proof. exact (@lem215894 d k a b p' q'). Qed.
Lemma lem215896 (d : nat) (k : nat) (a : nat) (b : nat) (p' : Prop) (q' : Prop) : (term469 d k a b p' q') = (term470 d k a b p' q').
Proof. exact (eq_refl (term469 d k a b p' q')). Qed.
Lemma lem215897 (d : nat) (k : nat) (a : nat) (b : nat) (p' : Prop) (q' : Prop) : term470 d k a b p' q'.
Proof. exact (EQ_MP (@lem215896 d k a b p' q') (@lem215895 d k a b p' q')). Qed.
Lemma lem215899 (m : nat) (n : nat) (p : nat) : (term439 m n p) = (term440 m n p).
Proof. exact (EQ_MP (@lem215787 m n p) (@lem215786 m n p)). Qed.
Lemma lem215900 (b : nat) (k : nat) (a : nat) (d : nat) : (term303 b k a d) = (term471 b k a d).
Proof. exact (@lem215899 (Nat.mul b k) (term0 a) d). Qed.
Lemma lem215904 (d : nat) (h1 : term83 d) : (d = (NUMERAL 0)) = False.
Proof. exact (@lem215798 d (@lem213728 d h1)). Qed.
Lemma lem215905 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem215906 (d : nat) (h1 : term83 d) : (term83 d) = (~ False).
Proof. exact (MK_COMB (@lem215905) (@lem215904 d h1)). Qed.
Lemma lem215908 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem215909 (d : nat) (h1 : term83 d) : (term83 d) = True.
Proof. exact (TRANS (@lem215906 d h1) (@lem215908)). Qed.
Lemma lem215910 (b : nat) (k : nat) (a : nat) : (term472 b k a) = (term472 b k a).
Proof. exact (eq_refl (term472 b k a)). Qed.
Lemma lem215911 (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term83 d) : (term471 b k a d) = (term473 b k a).
Proof. exact (MK_COMB (@lem215910 b k a) (@lem215909 d h1)). Qed.
Lemma lem215913 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem215914 (b : nat) (k : nat) (a : nat) : (term473 b k a) = (term474 b k a).
Proof. exact (@lem215913 (term474 b k a)). Qed.
Lemma lem215915 (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term83 d) : (term471 b k a d) = (term474 b k a).
Proof. exact (TRANS (@lem215911 b k a d h1) (@lem215914 b k a)). Qed.
Lemma lem215916 (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term83 d) : (term303 b k a d) = (term474 b k a).
Proof. exact (TRANS (@lem215900 b k a d) (@lem215915 b k a d h1)). Qed.
Lemma lem215917 (d : nat) (b : nat) (k : nat) (a : nat) (q' : Prop) : term475 d b k a q'.
Proof. exact (@lem215897 d k a b (term474 b k a) q'). Qed.
Lemma lem215918 (b : nat) (k : nat) (a : nat) (q' : Prop) (d : nat) (h1 : term83 d) : term476 d b k a q'.
Proof. exact (@lem215917 d b k a q' (@lem215916 b k a d h1)). Qed.
Lemma lem215923 (a : nat) (n : nat) (b : nat) : term432 a n b.
Proof. exact (fun h0 : term83 a => @lem215774 n b a h0). Qed.
Lemma lem215924 (b : nat) (k : nat) (a : nat) : term432 b k a.
Proof. exact (@lem215923 b k a). Qed.
Lemma lem215926 (b : nat) (h1 : term83 b) : (b = (NUMERAL 0)) = False.
Proof. exact (@lem215811 b (@lem213885 b h1)). Qed.
Lemma lem215927 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem215928 (b : nat) (h1 : term83 b) : (term83 b) = (~ False).
Proof. exact (MK_COMB (@lem215927) (@lem215926 b h1)). Qed.
Lemma lem215930 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem215931 (b : nat) (h1 : term83 b) : (term83 b) = True.
Proof. exact (TRANS (@lem215928 b h1) (@lem215930)). Qed.
Lemma lem215932 (b : nat) (h1 : term83 b) : True = (term83 b).
Proof. exact (SYM (@lem215931 b h1)). Qed.
Lemma lem215933 (b : nat) (h1 : term83 b) : term83 b.
Proof. exact (EQ_MP (@lem215932 b h1) (@lem0)). Qed.
Lemma lem215934 (k : nat) (a : nat) (b : nat) (h1 : term83 b) : (term426 k a b) = (term433 b k a).
Proof. exact (@lem215924 b k a (@lem215933 b h1)). Qed.
Lemma lem215935 (k : nat) (a : nat) (b : nat) (h1 : term83 b) : term477 b k a.
Proof. exact (fun h0 : term474 b k a => @lem215934 k a b h1). Qed.
Lemma lem215936 (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term83 d) : term478 d b k a.
Proof. exact (@lem215918 b k a (term433 b k a) d h1). Qed.
Lemma lem215937 (k : nat) (a : nat) (b : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) : (term479 d k a b) = (term480 b k a).
Proof. exact (@lem215936 b k a d h2 (@lem215935 k a b h1)). Qed.
Lemma lem215961 (c : nat) (k : nat) (a : nat) (b : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) : (term481 c d k a b) = (term482 b k a).
Proof. exact (MK_COMB (@lem215884 k c b d h1 h2) (@lem215937 k a b d h1 h2)). Qed.
Lemma lem215963 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem215964 (b : nat) (k : nat) (a : nat) : (term482 b k a) = (term480 b k a).
Proof. exact (@lem215963 (term480 b k a)). Qed.
Lemma lem215988 (c : nat) (k : nat) (a : nat) (b : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) : (term481 c d k a b) = (term480 b k a).
Proof. exact (TRANS (@lem215961 c k a b d h1 h2) (@lem215964 b k a)). Qed.
Lemma lem215989 (c : nat) (k : nat) (a : nat) (b : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) : (term480 b k a) = (term481 c d k a b).
Proof. exact (SYM (@lem215988 c k a b d h1 h2)). Qed.
Lemma lem215993 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem213276 m) (@lem213275 m)). Qed.
Lemma lem215994 (a : nat) : (term0 a) = (S a).
Proof. exact (@lem215993 a). Qed.
Lemma lem215995 (b : nat) (k : nat) : (term94 b k) = (term94 b k).
Proof. exact (eq_refl (term94 b k)). Qed.
Lemma lem215996 (b : nat) (k : nat) (a : nat) : (term474 b k a) = (term483 b k a).
Proof. exact (MK_COMB (@lem215995 b k) (@lem215994 a)). Qed.
Lemma lem215998 (m : nat) (n : nat) : (term8 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem213273 m n) (@lem213272 m n)). Qed.
Lemma lem215999 (b : nat) (k : nat) (a : nat) : (term483 b k a) = (term433 b k a).
Proof. exact (@lem215998 (Nat.mul b k) a). Qed.
Lemma lem216000 (b : nat) (k : nat) (a : nat) : (term474 b k a) = (term433 b k a).
Proof. exact (TRANS (@lem215996 b k a) (@lem215999 b k a)). Qed.
Lemma lem216001 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem216002 (b : nat) (k : nat) (a : nat) : (term484 b k a) = (term485 b k a).
Proof. exact (MK_COMB (@lem216001) (@lem216000 b k a)). Qed.
Lemma lem216003 (b : nat) (k : nat) (a : nat) : (term433 b k a) = (term433 b k a).
Proof. exact (eq_refl (term433 b k a)). Qed.
Lemma lem216004 (b : nat) (k : nat) (a : nat) : (term480 b k a) = (term486 b k a).
Proof. exact (MK_COMB (@lem216002 b k a) (@lem216003 b k a)). Qed.
Lemma lem216006 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem216007 (b : nat) (k : nat) (a : nat) : (term486 b k a) = True.
Proof. exact (@lem216006 (term433 b k a)). Qed.
Lemma lem216008 (b : nat) (k : nat) (a : nat) : (term480 b k a) = True.
Proof. exact (TRANS (@lem216004 b k a) (@lem216007 b k a)). Qed.
Lemma lem216009 (b : nat) (k : nat) (a : nat) : True = (term480 b k a).
Proof. exact (SYM (@lem216008 b k a)). Qed.
Lemma lem216010 (b : nat) (k : nat) (a : nat) : term480 b k a.
Proof. exact (EQ_MP (@lem216009 b k a) (@lem0)). Qed.
Lemma lem216011 (c : nat) (k : nat) (a : nat) (b : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) : term481 c d k a b.
Proof. exact (EQ_MP (@lem215989 c k a b d h1 h2) (@lem216010 b k a)). Qed.
Lemma lem216012 (c : nat) (k : nat) (a : nat) (b : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) : term487 c d k a b.
Proof. exact (@lem215763 c d k a b (@lem216011 c k a b d h1 h2)). Qed.
Lemma lem216013 (c : nat) (b : nat) (k : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term109 c b k a d) : term488 c d k a b.
Proof. exact (@lem216012 c k a b d h1 h2 (@lem213889 c b k a d h3)). Qed.
Lemma lem216014 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term95 b c a d) : (term109 c b k a d) = (term488 c d k a b).
Proof. exact (prop_ext (fun h4 : term109 c b k a d => @lem216013 c b k a d h1 h2 h4) (fun h4 : term488 c d k a b => @lem215760 k b c a d h1 h2 h3)). Qed.
Lemma lem216015 (k : nat) (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term95 b c a d) : term488 c d k a b.
Proof. exact (EQ_MP (@lem216014 k b c a d h1 h2 h3) (@lem215760 k b c a d h1 h2 h3)). Qed.
Lemma lem216020 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term95 b c a d) : term489 c d a b.
Proof. exact (fun k : nat => @lem216015 k b c a d h1 h2 h3). Qed.
Lemma lem216021 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term95 b c a d) : term104 c d a b.
Proof. exact (@lem213888 c d a b (@lem216020 b c a d h1 h2 h3)). Qed.
Lemma lem216022 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term98 b c a d) : term95 b c a d.
Proof. exact (proj2 (@lem213883 b c a d h1)). Qed.
Lemma lem216023 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term98 b c a d) : term83 b.
Proof. exact (proj1 (@lem213883 b c a d h1)). Qed.
Lemma lem216024 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term95 b c a d) : (term95 b c a d) = (term104 c d a b).
Proof. exact (prop_ext (fun h4 : term95 b c a d => @lem216021 b c a d h1 h2 h3) (fun h4 : term104 c d a b => @lem213884 b c a d h3)). Qed.
Lemma lem216025 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term95 b c a d) : term104 c d a b.
Proof. exact (EQ_MP (@lem216024 b c a d h1 h2 h3) (@lem213884 b c a d h3)). Qed.
Lemma lem216026 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term95 b c a d) : (term83 b) = (term104 c d a b).
Proof. exact (prop_ext (fun h4 : term83 b => @lem216025 b c a d h1 h2 h3) (fun h4 : term104 c d a b => @lem213885 b h1)). Qed.
Lemma lem216027 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term95 b c a d) : term104 c d a b.
Proof. exact (EQ_MP (@lem216026 b c a d h1 h2 h3) (@lem213885 b h1)). Qed.
Lemma lem216028 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term98 b c a d) : (term95 b c a d) = (term104 c d a b).
Proof. exact (prop_ext (fun h4 : term95 b c a d => @lem216027 b c a d h1 h2 h4) (fun h4 : term104 c d a b => @lem216022 b c a d h3)). Qed.
Lemma lem216029 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 b) (h2 : term83 d) (h3 : term98 b c a d) : term104 c d a b.
Proof. exact (EQ_MP (@lem216028 b c a d h1 h2 h3) (@lem216022 b c a d h3)). Qed.
Lemma lem216030 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 d) (h2 : term98 b c a d) : (term83 b) = (term104 c d a b).
Proof. exact (prop_ext (fun h3 : term83 b => @lem216029 b c a d h3 h1 h2) (fun h3 : term104 c d a b => @lem216023 b c a d h2)). Qed.
Lemma lem216031 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : term83 d) (h2 : term98 b c a d) : term104 c d a b.
Proof. exact (EQ_MP (@lem216030 b c a d h1 h2) (@lem216023 b c a d h2)). Qed.
Lemma lem216033 (c : nat) (a : nat) (b : nat) (d : nat) (h1 : term83 d) : term106 c d a b.
Proof. exact (fun h0 : term98 b c a d => @lem216031 b c a d h1 h0). Qed.
Lemma lem216034 (c : nat) (d : nat) (a : nat) (b : nat) : term106 c d a b.
Proof. exact (or_elim (@lem213726 d) (fun h0 : d = (NUMERAL 0) => @lem213816 c a b d h0) (fun h0 : term83 d => @lem216033 c a b d h0)). Qed.
Lemma lem216039 (c : nat) (a : nat) (b : nat) : term490 c a b.
Proof. exact (fun d : nat => @lem216034 c d a b). Qed.
Lemma lem216044 (a : nat) (b : nat) : term491 a b.
Proof. exact (fun c : nat => @lem216039 c a b). Qed.
Lemma lem216049 (a : nat) : term492 a.
Proof. exact (fun b : nat => @lem216044 a b). Qed.
Lemma lem216054 : term493.
Proof. exact (fun a : nat => @lem216049 a). Qed.
