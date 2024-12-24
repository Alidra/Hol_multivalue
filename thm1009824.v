Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1009824_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import ADD_SYM_spec.
Require Import DISJ_ACI_spec.
Require Import LT_EXISTS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17362_spec.
Require Import thm18394_spec.
Require Import thm1856_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm75543_spec.
Lemma lem1009245 : term0.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1009246 : term1.
Proof. exact (proj2 (@lem1009245)). Qed.
Lemma lem1009247 : term2.
Proof. exact (proj2 (@lem1009246)). Qed.
Lemma lem1009248 (m : nat) : term3 m.
Proof. exact (@lem1009247 m). Qed.
Lemma lem1009249 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1009250 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1009249 m) (@lem1009248 m)). Qed.
Lemma lem1009251 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem1009250 m n). Qed.
Lemma lem1009252 (m : nat) (n : nat) : (term5 m n) = ((term6 m n) = (term7 m n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem1009269 (m : nat) : term8 m.
Proof. exact (@lem100361 m). Qed.
Lemma lem1009270 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem1009271 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1009270 m) (@lem1009269 m)). Qed.
Lemma lem1009272 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem1009271 m n). Qed.
Lemma lem1009273 (n : nat) (m : nat) : (term10 m n) = ((Peano.lt m n) = (term11 n m)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem1009275 (n : nat) : term12 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem1009276 (n : nat) : (term12 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem1009285 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1009286 (n : nat) (p : nat) : ((term13 n p) = True) = (term13 n p).
Proof. exact (@lem1009285 (term13 n p)). Qed.
Lemma lem1009288 (n : nat) (m : nat) : (Peano.lt m n) = (term11 n m).
Proof. exact (EQ_MP (@lem1009273 n m) (@lem1009272 m n)). Qed.
Lemma lem1009289 (p : nat) (n : nat) : (term13 n p) = (term14 p n).
Proof. exact (@lem1009288 (NUMERAL p) (NUMERAL n)). Qed.
Lemma lem1009294 (p : nat) (n : nat) : ((term13 n p) = True) = (term14 p n).
Proof. exact (TRANS (@lem1009286 n p) (@lem1009289 p n)). Qed.
Lemma lem1009298 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1009276 n) (@lem1009275 n)). Qed.
Lemma lem1009299 (p : nat) : (NUMERAL p) = p.
Proof. exact (@lem1009298 p). Qed.
Lemma lem1009300 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1009301 (p : nat) : (term15 p) = (@eq nat p).
Proof. exact (MK_COMB (@lem1009300) (@lem1009299 p)). Qed.
Lemma lem1009303 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem1009252 m n) (@lem1009251 m n)). Qed.
Lemma lem1009304 (n : nat) (d : nat) : (term16 n d) = (term17 n d).
Proof. exact (@lem1009303 (NUMERAL n) d). Qed.
Lemma lem1009306 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1009276 n) (@lem1009275 n)). Qed.
Lemma lem1009307 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1009308 (n : nat) : (term18 n) = (Nat.add n).
Proof. exact (MK_COMB (@lem1009307) (@lem1009306 n)). Qed.
Lemma lem1009309 (d : nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1009310 (n : nat) (d : nat) : (term19 n d) = (Nat.add n d).
Proof. exact (MK_COMB (@lem1009308 n) (@lem1009309 d)). Qed.
Lemma lem1009311 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1009312 (n : nat) (d : nat) : (term17 n d) = (term7 n d).
Proof. exact (MK_COMB (@lem1009311) (@lem1009310 n d)). Qed.
Lemma lem1009313 (n : nat) (d : nat) : (term16 n d) = (term7 n d).
Proof. exact (TRANS (@lem1009304 n d) (@lem1009312 n d)). Qed.
Lemma lem1009314 (p : nat) (n : nat) (d : nat) : ((NUMERAL p) = (term16 n d)) = (p = (term7 n d)).
Proof. exact (MK_COMB (@lem1009301 p) (@lem1009313 n d)). Qed.
Lemma lem1009317 (p : nat) (n : nat) : (term20 p n) = (term21 p n).
Proof. exact (fun_ext (fun d : nat => @lem1009314 p n d)). Qed.
Lemma lem1009318 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1009319 (p : nat) (n : nat) : (term14 p n) = (term22 p n).
Proof. exact (MK_COMB (@lem1009318) (@lem1009317 p n)). Qed.
Lemma lem1009324 (p : nat) (n : nat) : ((term13 n p) = True) = (term22 p n).
Proof. exact (TRANS (@lem1009294 p n) (@lem1009319 p n)). Qed.
Lemma lem1009325 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term23 m n p).
Proof. exact (eq_refl (term23 m n p)). Qed.
Lemma lem1009326 (m : nat) (p : nat) (n : nat) : (term24 m n p) = (term25 m p n).
Proof. exact (MK_COMB (@lem1009325 m n p) (@lem1009324 p n)). Qed.
Lemma lem1009331 (m : nat) (n : nat) (p : nat) : (term25 m p n) = (term24 m n p).
Proof. exact (SYM (@lem1009326 m p n)). Qed.
Lemma lem1009333 (p : Prop) : p = (term26 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1009334 (m : nat) (p : nat) (n : nat) : (term25 m p n) = (term27 m p n).
Proof. exact (@lem1009333 (term25 m p n)). Qed.
Lemma lem1009335 (m : nat) (p : nat) (n : nat) : (term27 m p n) = (term25 m p n).
Proof. exact (SYM (@lem1009334 m p n)). Qed.
Lemma lem1009336 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term28 m p n.
Proof. exact (h1). Qed.
Lemma lem1009339 (m : nat) (p : nat) (n : nat) (h1 : term29 m p n) : term29 m p n.
Proof. exact (h1). Qed.
Lemma lem1009340 (m : nat) (p : nat) (n : nat) : term30 m p n.
Proof. exact (fun h0 : term29 m p n => @lem1009339 m p n h0). Qed.
Lemma lem1009341 (m : nat) (p : nat) (n : nat) (h1 : term30 m p n) : term30 m p n.
Proof. exact (h1). Qed.
Lemma lem1009342 (m : nat) (p : nat) (n : nat) (h1 : term29 m p n) : term29 m p n.
Proof. exact (h1). Qed.
Lemma lem1009343 (m : nat) (p : nat) (n : nat) (h1 : term29 m p n) (h2 : term30 m p n) : term29 m p n.
Proof. exact (@lem1009341 m p n h2 (@lem1009342 m p n h1)). Qed.
Lemma lem1009344 (m : nat) (p : nat) (n : nat) (h1 : term29 m p n) : term31 m p n.
Proof. exact (fun h0 : term30 m p n => @lem1009343 m p n h1 h0). Qed.
Lemma lem1009345 (m : nat) (p : nat) (n : nat) (h1 : term30 m p n) : term30 m p n.
Proof. exact (h1). Qed.
Lemma lem1009346 (m : nat) (p : nat) (n : nat) (h1 : term29 m p n) (h2 : term30 m p n) : term29 m p n.
Proof. exact (@lem1009344 m p n h1 (@lem1009345 m p n h2)). Qed.
Lemma lem1009347 (m : nat) (p : nat) (n : nat) (h1 : term30 m p n) : term30 m p n.
Proof. exact (fun h0 : term29 m p n => @lem1009346 m p n h0 h1). Qed.
Lemma lem1009348 (m : nat) (p : nat) (n : nat) : term32 m p n.
Proof. exact (fun h0 : term30 m p n => @lem1009347 m p n h0). Qed.
Lemma lem1009351 (m : nat) (p : nat) (n : nat) : term30 m p n.
Proof. exact (@lem1009348 m p n (@lem1009340 m p n)). Qed.
Lemma lem1009373 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1009374 : term33 = term34.
Proof. exact (@lem1009373 term35). Qed.
Lemma lem1009383 (m : nat) (p : nat) (n : nat) : (term36 m p n) = (term36 m p n).
Proof. exact (eq_refl (term36 m p n)). Qed.
Lemma lem1009384 (m : nat) (p : nat) (n : nat) : (term29 m p n) = (term37 m p n).
Proof. exact (MK_COMB (@lem1009383 m p n) (@lem1009374)). Qed.
Lemma lem1009387 (p : nat) (n : nat) : (term38 p n) = (term39 p n).
Proof. exact (fun_ext (fun m : nat => @lem1009384 m p n)). Qed.
Lemma lem1009388 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009389 (p : nat) (n : nat) : (term40 p n) = (term41 p n).
Proof. exact (MK_COMB (@lem1009388) (@lem1009387 p n)). Qed.
Lemma lem1009394 (n : nat) : (term42 n) = (term43 n).
Proof. exact (fun_ext (fun p : nat => @lem1009389 p n)). Qed.
Lemma lem1009395 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009396 (n : nat) : (term44 n) = (term45 n).
Proof. exact (MK_COMB (@lem1009395) (@lem1009394 n)). Qed.
Lemma lem1009401 : term46 = term47.
Proof. exact (fun_ext (fun n : nat => @lem1009396 n)). Qed.
Lemma lem1009402 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009411 : term48 = term49.
Proof. exact (MK_COMB (@lem1009402) (@lem1009401)). Qed.
Lemma lem1009412 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1009413 (m : nat) : (term50 m) = (term50 m).
Proof. exact (fun_ext (fun n : nat => @lem1009412 n m)). Qed.
Lemma lem1009414 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009415 (m : nat) : (term51 m) = (term51 m).
Proof. exact (MK_COMB (@lem1009414) (@lem1009413 m)). Qed.
Lemma lem1009416 : term52 = term52.
Proof. exact (fun_ext (fun m : nat => @lem1009415 m)). Qed.
Lemma lem1009417 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009418 : term35 = term35.
Proof. exact (MK_COMB (@lem1009417) (@lem1009416)). Qed.
Lemma lem1009419 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1009420 : term34 = term34.
Proof. exact (MK_COMB (@lem1009419) (@lem1009418)). Qed.
Lemma lem1009421 (p : nat) (n : nat) (d : nat) : (p = (term7 n d)) = (p = (term7 n d)).
Proof. exact (eq_refl (p = (term7 n d))). Qed.
Lemma lem1009422 (p : nat) (n : nat) : (term21 p n) = (term21 p n).
Proof. exact (fun_ext (fun d : nat => @lem1009421 p n d)). Qed.
Lemma lem1009423 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1009424 (p : nat) (n : nat) : (term22 p n) = (term22 p n).
Proof. exact (MK_COMB (@lem1009423) (@lem1009422 p n)). Qed.
Lemma lem1009427 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term23 m n p).
Proof. exact (eq_refl (term23 m n p)). Qed.
Lemma lem1009428 (m : nat) (p : nat) (n : nat) : (term25 m p n) = (term25 m p n).
Proof. exact (MK_COMB (@lem1009427 m n p) (@lem1009424 p n)). Qed.
Lemma lem1009429 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1009430 (m : nat) (p : nat) (n : nat) : (term28 m p n) = (term28 m p n).
Proof. exact (MK_COMB (@lem1009429) (@lem1009428 m p n)). Qed.
Lemma lem1009431 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1009432 (m : nat) (p : nat) (n : nat) : (term36 m p n) = (term36 m p n).
Proof. exact (MK_COMB (@lem1009431) (@lem1009430 m p n)). Qed.
Lemma lem1009433 (m : nat) (p : nat) (n : nat) : (term37 m p n) = (term37 m p n).
Proof. exact (MK_COMB (@lem1009432 m p n) (@lem1009420)). Qed.
Lemma lem1009434 (p : nat) (n : nat) : (term39 p n) = (term39 p n).
Proof. exact (fun_ext (fun m : nat => @lem1009433 m p n)). Qed.
Lemma lem1009435 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009436 (p : nat) (n : nat) : (term41 p n) = (term41 p n).
Proof. exact (MK_COMB (@lem1009435) (@lem1009434 p n)). Qed.
Lemma lem1009437 (n : nat) : (term43 n) = (term43 n).
Proof. exact (fun_ext (fun p : nat => @lem1009436 p n)). Qed.
Lemma lem1009438 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009439 (n : nat) : (term45 n) = (term45 n).
Proof. exact (MK_COMB (@lem1009438) (@lem1009437 n)). Qed.
Lemma lem1009440 : term47 = term47.
Proof. exact (fun_ext (fun n : nat => @lem1009439 n)). Qed.
Lemma lem1009441 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009442 : term49 = term49.
Proof. exact (MK_COMB (@lem1009441) (@lem1009440)). Qed.
Lemma lem1009485 : term48 = term49.
Proof. exact (TRANS (@lem1009411) (@lem1009442)). Qed.
Lemma lem1009486 : term49 = term48.
Proof. exact (SYM (@lem1009485)). Qed.
Lemma lem1009487 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term28 m p n.
Proof. exact (h1). Qed.
Lemma lem1009488 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem1009491 (P : nat -> Prop) : (term53 P) = (term54 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1009492 (p : nat) (n : nat) : (term55 p n) = (term56 p n).
Proof. exact (@lem1009491 (term21 p n)). Qed.
Lemma lem1009493 (p : nat) (n : nat) (d : nat) : (term57 p n d) = (p = (term7 n d)).
Proof. exact (eq_refl (term57 p n d)). Qed.
Lemma lem1009494 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1009496 (p : nat) (n : nat) (d : nat) : (term58 p n d) = (term59 p n d).
Proof. exact (MK_COMB (@lem1009494) (@lem1009493 p n d)). Qed.
Lemma lem1009497 (p : nat) (n : nat) : (term60 p n) = (term61 p n).
Proof. exact (fun_ext (fun d : nat => @lem1009496 p n d)). Qed.
Lemma lem1009498 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009499 (p : nat) (n : nat) : (term56 p n) = (term62 p n).
Proof. exact (MK_COMB (@lem1009498) (@lem1009497 p n)). Qed.
Lemma lem1009500 (p : nat) (n : nat) : (term55 p n) = (term62 p n).
Proof. exact (TRANS (@lem1009492 p n) (@lem1009499 p n)). Qed.
Lemma lem1009502 (m : nat) (n : nat) (p : nat) : (term63 m n p) = (term63 m n p).
Proof. exact (eq_refl (term63 m n p)). Qed.
Lemma lem1009503 (m : nat) (p : nat) (n : nat) : (term64 m p n) = (term65 m p n).
Proof. exact (MK_COMB (@lem1009502 m n p) (@lem1009500 p n)). Qed.
Lemma lem1009504 (m : nat) (p : nat) (n : nat) : (term28 m p n) = (term64 m p n).
Proof. exact (@lem17362 ((term7 m n) = p) (term22 p n)). Qed.
Lemma lem1009513 (m : nat) (p : nat) (n : nat) : (term28 m p n) = (term65 m p n).
Proof. exact (TRANS (@lem1009504 m p n) (@lem1009503 m p n)). Qed.
Lemma lem1009514 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term65 m p n.
Proof. exact (EQ_MP (@lem1009513 m p n) (@lem1009487 m p n h1)). Qed.
Lemma lem1009515 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1009516 (m : nat) : (term50 m) = (term50 m).
Proof. exact (fun_ext (fun n : nat => @lem1009515 n m)). Qed.
Lemma lem1009517 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009518 (m : nat) : (term51 m) = (term51 m).
Proof. exact (MK_COMB (@lem1009517) (@lem1009516 m)). Qed.
Lemma lem1009519 : term52 = term52.
Proof. exact (fun_ext (fun m : nat => @lem1009518 m)). Qed.
Lemma lem1009520 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009533 : term35 = term35.
Proof. exact (MK_COMB (@lem1009520) (@lem1009519)). Qed.
Lemma lem1009534 (h1 : term35) : term35.
Proof. exact (EQ_MP (@lem1009533) (@lem1009488 h1)). Qed.
Lemma lem1009547 (p : nat) (n : nat) (d : nat) : (term59 p n d) = (term59 p n d).
Proof. exact (eq_refl (term59 p n d)). Qed.
Lemma lem1009548 (p : nat) (n : nat) : (term61 p n) = (term61 p n).
Proof. exact (fun_ext (fun d : nat => @lem1009547 p n d)). Qed.
Lemma lem1009549 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009550 (p : nat) (n : nat) : (term62 p n) = (term62 p n).
Proof. exact (MK_COMB (@lem1009549) (@lem1009548 p n)). Qed.
Lemma lem1009563 (m : nat) (n : nat) (p : nat) : (term63 m n p) = (term63 m n p).
Proof. exact (eq_refl (term63 m n p)). Qed.
Lemma lem1009564 (m : nat) (p : nat) (n : nat) : (term65 m p n) = (term65 m p n).
Proof. exact (MK_COMB (@lem1009563 m n p) (@lem1009550 p n)). Qed.
Lemma lem1009565 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term65 m p n.
Proof. exact (EQ_MP (@lem1009564 m p n) (@lem1009514 m p n h1)). Qed.
Lemma lem1009578 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1009579 (m : nat) : (term50 m) = (term50 m).
Proof. exact (fun_ext (fun n : nat => @lem1009578 n m)). Qed.
Lemma lem1009580 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009581 (m : nat) : (term51 m) = (term51 m).
Proof. exact (MK_COMB (@lem1009580) (@lem1009579 m)). Qed.
Lemma lem1009582 : term52 = term52.
Proof. exact (fun_ext (fun m : nat => @lem1009581 m)). Qed.
Lemma lem1009583 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009584 : term35 = term35.
Proof. exact (MK_COMB (@lem1009583) (@lem1009582)). Qed.
Lemma lem1009585 (h1 : term35) : term35.
Proof. exact (EQ_MP (@lem1009584) (@lem1009534 h1)). Qed.
Lemma lem1009586 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term62 p n.
Proof. exact (proj2 (@lem1009565 m p n h1)). Qed.
Lemma lem1009589 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1009590 (m : nat) : (term50 m) = (term50 m).
Proof. exact (fun_ext (fun n : nat => @lem1009589 n m)). Qed.
Lemma lem1009591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009592 (m : nat) : (term51 m) = (term51 m).
Proof. exact (MK_COMB (@lem1009591) (@lem1009590 m)). Qed.
Lemma lem1009593 : term52 = term52.
Proof. exact (fun_ext (fun m : nat => @lem1009592 m)). Qed.
Lemma lem1009594 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009596 : term35 = term35.
Proof. exact (MK_COMB (@lem1009594) (@lem1009593)). Qed.
Lemma lem1009597 (h1 : term35) : term35.
Proof. exact (EQ_MP (@lem1009596) (@lem1009585 h1)). Qed.
Lemma lem1009603 (p : nat) (n : nat) (d : nat) : (term59 p n d) = (term59 p n d).
Proof. exact (eq_refl (term59 p n d)). Qed.
Lemma lem1009604 (p : nat) (n : nat) : (term61 p n) = (term61 p n).
Proof. exact (fun_ext (fun d : nat => @lem1009603 p n d)). Qed.
Lemma lem1009605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1009607 (p : nat) (n : nat) : (term62 p n) = (term62 p n).
Proof. exact (MK_COMB (@lem1009605) (@lem1009604 p n)). Qed.
Lemma lem1009608 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term62 p n.
Proof. exact (EQ_MP (@lem1009607 p n) (@lem1009586 m p n h1)). Qed.
Lemma lem1009609 (_16392 : nat) (h1 : term35) : term66 _16392.
Proof. exact (@lem1009597 h1 _16392). Qed.
Lemma lem1009610 (_16392 : nat) : (term66 _16392) = (term51 _16392).
Proof. exact (eq_refl (term66 _16392)). Qed.
Lemma lem1009611 (_16392 : nat) (h1 : term35) : term51 _16392.
Proof. exact (EQ_MP (@lem1009610 _16392) (@lem1009609 _16392 h1)). Qed.
Lemma lem1009612 (_16392 : nat) (_16393 : nat) (h1 : term35) : term67 _16392 _16393.
Proof. exact (@lem1009611 _16392 h1 _16393). Qed.
Lemma lem1009613 (_16393 : nat) (_16392 : nat) : (term67 _16392 _16393) = ((Nat.add _16392 _16393) = (Nat.add _16393 _16392)).
Proof. exact (eq_refl (term67 _16392 _16393)). Qed.
Lemma lem1009615 (_16394 : nat) (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term68 p n _16394.
Proof. exact (@lem1009608 m p n h1 _16394). Qed.
Lemma lem1009616 (p : nat) (n : nat) (_16394 : nat) : (term68 p n _16394) = (term59 p n _16394).
Proof. exact (eq_refl (term68 p n _16394)). Qed.
Lemma lem1009621 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : (term7 m n) = p.
Proof. exact (proj1 (@lem1009565 m p n h1)). Qed.
Lemma lem1009623 (_16394 : nat) (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term59 p n _16394.
Proof. exact (EQ_MP (@lem1009616 p n _16394) (@lem1009615 _16394 m p n h1)). Qed.
Lemma lem1009624 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : p = (term7 m n).
Proof. exact (SYM (@lem1009621 m p n h1)). Qed.
Lemma lem1009653 (n : nat) (_16394 : nat) : (term69 n _16394) = (term69 n _16394).
Proof. exact (eq_refl (term69 n _16394)). Qed.
Lemma lem1009654 (_16394 : nat) (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : (term70 n _16394 p) = (term71 _16394 m n).
Proof. exact (MK_COMB (@lem1009653 n _16394) (@lem1009624 m p n h1)). Qed.
Lemma lem1009655 (m : nat) (n : nat) (_16394 : nat) : (term71 _16394 m n) = (term72 m n _16394).
Proof. exact (eq_refl (term71 _16394 m n)). Qed.
Lemma lem1009656 (n : nat) (_16394 : nat) (p : nat) : (term73 n _16394 p) = (term73 n _16394 p).
Proof. exact (eq_refl (term73 n _16394 p)). Qed.
Lemma lem1009657 (p : nat) (m : nat) (n : nat) (_16394 : nat) : ((term70 n _16394 p) = (term71 _16394 m n)) = ((term70 n _16394 p) = (term72 m n _16394)).
Proof. exact (MK_COMB (@lem1009656 n _16394 p) (@lem1009655 m n _16394)). Qed.
Lemma lem1009658 (p : nat) (n : nat) (_16394 : nat) : (term70 n _16394 p) = (term59 p n _16394).
Proof. exact (eq_refl (term70 n _16394 p)). Qed.
Lemma lem1009659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1009660 (p : nat) (n : nat) (_16394 : nat) : (term73 n _16394 p) = (term74 p n _16394).
Proof. exact (MK_COMB (@lem1009659) (@lem1009658 p n _16394)). Qed.
Lemma lem1009661 (m : nat) (n : nat) (_16394 : nat) : (term72 m n _16394) = (term72 m n _16394).
Proof. exact (eq_refl (term72 m n _16394)). Qed.
Lemma lem1009662 (p : nat) (m : nat) (n : nat) (_16394 : nat) : ((term70 n _16394 p) = (term72 m n _16394)) = ((term59 p n _16394) = (term72 m n _16394)).
Proof. exact (MK_COMB (@lem1009660 p n _16394) (@lem1009661 m n _16394)). Qed.
Lemma lem1009663 (p : nat) (m : nat) (n : nat) (_16394 : nat) : ((term70 n _16394 p) = (term71 _16394 m n)) = ((term59 p n _16394) = (term72 m n _16394)).
Proof. exact (TRANS (@lem1009657 p m n _16394) (@lem1009662 p m n _16394)). Qed.
Lemma lem1009664 (_16394 : nat) (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : (term59 p n _16394) = (term72 m n _16394).
Proof. exact (EQ_MP (@lem1009663 p m n _16394) (@lem1009654 _16394 m p n h1)). Qed.
Lemma lem1009665 (_16394 : nat) (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term72 m n _16394.
Proof. exact (EQ_MP (@lem1009664 _16394 m p n h1) (@lem1009623 _16394 m p n h1)). Qed.
Lemma lem1009666 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1009667 (_16401 : nat) (_16402 : nat) (h1 : _16401 = _16402) : _16401 = _16402.
Proof. exact (h1). Qed.
Lemma lem1009668 (_16401 : nat) (_16402 : nat) (h1 : _16401 = _16402) : (S _16401) = (S _16402).
Proof. exact (MK_COMB (@lem1009666) (@lem1009667 _16401 _16402 h1)). Qed.
Lemma lem1009669 (_16401 : nat) (_16402 : nat) : term75 _16401 _16402.
Proof. exact (fun h0 : _16401 = _16402 => @lem1009668 _16401 _16402 h0). Qed.
Lemma lem1009671 (a : Prop) (b : Prop) : (a -> b) = (term76 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1009672 (_16401 : nat) (_16402 : nat) : (term75 _16401 _16402) = (term77 _16401 _16402).
Proof. exact (@lem1009671 (_16401 = _16402) ((S _16401) = (S _16402))). Qed.
Lemma lem1009673 (_16401 : nat) (_16402 : nat) : term77 _16401 _16402.
Proof. exact (EQ_MP (@lem1009672 _16401 _16402) (@lem1009669 _16401 _16402)). Qed.
Lemma lem1009692 (_16393 : nat) (_16392 : nat) (h1 : term35) : (Nat.add _16392 _16393) = (Nat.add _16393 _16392).
Proof. exact (EQ_MP (@lem1009613 _16393 _16392) (@lem1009612 _16392 _16393 h1)). Qed.
Lemma lem1009693 (n : nat) (m : nat) (h1 : term35) : (Nat.add m n) = (Nat.add n m).
Proof. exact (@lem1009692 n m h1). Qed.
Lemma lem1009694 (n : nat) (m : nat) (h1 : term35) : term78 n m.
Proof. exact (fun h0 : term79 n m => @lem1009693 n m h1). Qed.
Lemma lem1009696 (p : Prop) : (term80 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1009697 (n : nat) (m : nat) : (term78 n m) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (@lem1009696 ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1009698 (n : nat) (m : nat) (h1 : term35) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1009697 n m) (@lem1009694 n m h1)). Qed.
Lemma lem1009704 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1009705 (_16401 : nat) (_16402 : nat) : (term77 _16401 _16402) = (term81 _16401 _16402).
Proof. exact (@lem1009704 ((S _16401) = (S _16402)) (term82 _16401 _16402)). Qed.
Lemma lem1009715 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1009716 (_16401 : nat) (_16402 : nat) : (term83 _16401 _16402) = (term84 _16401 _16402).
Proof. exact (MK_COMB (@lem1009715) (@lem1009705 _16401 _16402)). Qed.
Lemma lem1009726 (_16401 : nat) (_16402 : nat) : (term81 _16401 _16402) = (term81 _16401 _16402).
Proof. exact (eq_refl (term81 _16401 _16402)). Qed.
Lemma lem1009727 (_16401 : nat) (_16402 : nat) : ((term77 _16401 _16402) = (term81 _16401 _16402)) = ((term81 _16401 _16402) = (term81 _16401 _16402)).
Proof. exact (MK_COMB (@lem1009716 _16401 _16402) (@lem1009726 _16401 _16402)). Qed.
Lemma lem1009729 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1009730 (x : Prop) : (x = x) = True.
Proof. exact (@lem1009729 Prop x). Qed.
Lemma lem1009731 (_16401 : nat) (_16402 : nat) : ((term81 _16401 _16402) = (term81 _16401 _16402)) = True.
Proof. exact (@lem1009730 (term81 _16401 _16402)). Qed.
Lemma lem1009732 (_16401 : nat) (_16402 : nat) : ((term77 _16401 _16402) = (term81 _16401 _16402)) = True.
Proof. exact (TRANS (@lem1009727 _16401 _16402) (@lem1009731 _16401 _16402)). Qed.
Lemma lem1009733 (_16401 : nat) (_16402 : nat) : True = ((term77 _16401 _16402) = (term81 _16401 _16402)).
Proof. exact (SYM (@lem1009732 _16401 _16402)). Qed.
Lemma lem1009734 (_16401 : nat) (_16402 : nat) : (term77 _16401 _16402) = (term81 _16401 _16402).
Proof. exact (EQ_MP (@lem1009733 _16401 _16402) (@lem0)). Qed.
Lemma lem1009735 (_16401 : nat) (_16402 : nat) : term81 _16401 _16402.
Proof. exact (EQ_MP (@lem1009734 _16401 _16402) (@lem1009673 _16401 _16402)). Qed.
Lemma lem1009737 (b : Prop) (a : Prop) : (a \/ b) = (term85 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1009738 (_16401 : nat) (_16402 : nat) : (term81 _16401 _16402) = (term86 _16401 _16402).
Proof. exact (@lem1009737 (term82 _16401 _16402) ((S _16401) = (S _16402))). Qed.
Lemma lem1009740 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1009741 (_16401 : nat) (_16402 : nat) : (term88 _16401 _16402) = (_16401 = _16402).
Proof. exact (@lem1009740 (_16401 = _16402)). Qed.
Lemma lem1009742 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1009743 (_16401 : nat) (_16402 : nat) : (term89 _16401 _16402) = (term90 _16401 _16402).
Proof. exact (MK_COMB (@lem1009742) (@lem1009741 _16401 _16402)). Qed.
Lemma lem1009744 (_16401 : nat) (_16402 : nat) : ((S _16401) = (S _16402)) = ((S _16401) = (S _16402)).
Proof. exact (eq_refl ((S _16401) = (S _16402))). Qed.
Lemma lem1009745 (_16401 : nat) (_16402 : nat) : (term86 _16401 _16402) = (term75 _16401 _16402).
Proof. exact (MK_COMB (@lem1009743 _16401 _16402) (@lem1009744 _16401 _16402)). Qed.
Lemma lem1009746 (_16401 : nat) (_16402 : nat) : (term81 _16401 _16402) = (term75 _16401 _16402).
Proof. exact (TRANS (@lem1009738 _16401 _16402) (@lem1009745 _16401 _16402)). Qed.
Lemma lem1009749 (_16401 : nat) (_16402 : nat) : term75 _16401 _16402.
Proof. exact (EQ_MP (@lem1009746 _16401 _16402) (@lem1009735 _16401 _16402)). Qed.
Lemma lem1009750 (n : nat) (m : nat) : term91 n m.
Proof. exact (@lem1009749 (Nat.add m n) (Nat.add n m)). Qed.
Lemma lem1009753 (n : nat) (m : nat) (h1 : term35) : (term7 m n) = (term7 n m).
Proof. exact (@lem1009750 n m (@lem1009698 n m h1)). Qed.
Lemma lem1009754 (n : nat) (m : nat) (h1 : term35) : term92 n m.
Proof. exact (fun h0 : term93 n m => @lem1009753 n m h1). Qed.
Lemma lem1009756 (p : Prop) : (term80 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1009757 (n : nat) (m : nat) : (term92 n m) = ((term7 m n) = (term7 n m)).
Proof. exact (@lem1009756 ((term7 m n) = (term7 n m))). Qed.
Lemma lem1009758 (n : nat) (m : nat) (h1 : term35) : (term7 m n) = (term7 n m).
Proof. exact (EQ_MP (@lem1009757 n m) (@lem1009754 n m h1)). Qed.
Lemma lem1009761 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1009763 (m : nat) (n : nat) (_16394 : nat) : (term72 m n _16394) = (term94 m n _16394).
Proof. exact (@lem1009761 ((term7 m n) = (term7 n _16394))). Qed.
Lemma lem1009766 (_16394 : nat) (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term94 m n _16394.
Proof. exact (EQ_MP (@lem1009763 m n _16394) (@lem1009665 _16394 m p n h1)). Qed.
Lemma lem1009767 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term95 n m.
Proof. exact (@lem1009766 m m p n h1). Qed.
Lemma lem1009770 (m : nat) (p : nat) (n : nat) (h1 : term35) (h2 : term28 m p n) : False.
Proof. exact (@lem1009767 m p n h2 (@lem1009758 n m h1)). Qed.
Lemma lem1009771 (m : nat) (p : nat) (n : nat) (h1 : term35) (h2 : term28 m p n) : term96.
Proof. exact (fun h0 : ~ False => @lem1009770 m p n h1 h2). Qed.
Lemma lem1009773 (p : Prop) : (term80 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1009774 : term96 = False.
Proof. exact (@lem1009773 False). Qed.
Lemma lem1009776 (m : nat) (p : nat) (n : nat) (h1 : term35) (h2 : term28 m p n) : False.
Proof. exact (EQ_MP (@lem1009774) (@lem1009771 m p n h1 h2)). Qed.
Lemma lem1009777 (m : nat) (p : nat) (n : nat) (h1 : term35) (h2 : term28 m p n) : term35 = False.
Proof. exact (prop_ext (fun h3 : term35 => @lem1009776 m p n h1 h2) (fun h3 : False => @lem1009597 h1)). Qed.
Lemma lem1009778 (m : nat) (p : nat) (n : nat) (h1 : term35) (h2 : term28 m p n) : False.
Proof. exact (EQ_MP (@lem1009777 m p n h1 h2) (@lem1009597 h1)). Qed.
Lemma lem1009779 (m : nat) (p : nat) (n : nat) (h1 : term35) (h2 : term28 m p n) : term35 = False.
Proof. exact (prop_ext (fun h3 : term35 => @lem1009778 m p n h1 h2) (fun h3 : False => @lem1009585 h1)). Qed.
Lemma lem1009780 (m : nat) (p : nat) (n : nat) (h1 : term35) (h2 : term28 m p n) : False.
Proof. exact (EQ_MP (@lem1009779 m p n h1 h2) (@lem1009585 h1)). Qed.
Lemma lem1009781 (m : nat) (p : nat) (n : nat) (h1 : term35) (h2 : term28 m p n) : term35 = False.
Proof. exact (prop_ext (fun h3 : term35 => @lem1009780 m p n h1 h2) (fun h3 : False => @lem1009534 h1)). Qed.
Lemma lem1009782 (m : nat) (p : nat) (n : nat) (h1 : term35) (h2 : term28 m p n) : False.
Proof. exact (EQ_MP (@lem1009781 m p n h1 h2) (@lem1009534 h1)). Qed.
Lemma lem1009783 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term33.
Proof. exact (fun h0 : term35 => @lem1009782 m p n h0 h1). Qed.
Lemma lem1009784 : term33 = term34.
Proof. exact (@lem69 term35). Qed.
Lemma lem1009785 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term34.
Proof. exact (EQ_MP (@lem1009784) (@lem1009783 m p n h1)). Qed.
Lemma lem1009786 (m : nat) (p : nat) (n : nat) : term37 m p n.
Proof. exact (fun h0 : term28 m p n => @lem1009785 m p n h0). Qed.
Lemma lem1009791 (p : nat) (n : nat) : term41 p n.
Proof. exact (fun m : nat => @lem1009786 m p n). Qed.
Lemma lem1009796 (n : nat) : term45 n.
Proof. exact (fun p : nat => @lem1009791 p n). Qed.
Lemma lem1009801 : term49.
Proof. exact (fun n : nat => @lem1009796 n). Qed.
Lemma lem1009802 : term48.
Proof. exact (EQ_MP (@lem1009486) (@lem1009801)). Qed.
Lemma lem1009803 (n : nat) : term97 n.
Proof. exact (@lem1009802 n). Qed.
Lemma lem1009804 (n : nat) : (term97 n) = (term44 n).
Proof. exact (eq_refl (term97 n)). Qed.
Lemma lem1009805 (n : nat) : term44 n.
Proof. exact (EQ_MP (@lem1009804 n) (@lem1009803 n)). Qed.
Lemma lem1009806 (n : nat) (p : nat) : term98 n p.
Proof. exact (@lem1009805 n p). Qed.
Lemma lem1009807 (p : nat) (n : nat) : (term98 n p) = (term40 p n).
Proof. exact (eq_refl (term98 n p)). Qed.
Lemma lem1009808 (p : nat) (n : nat) : term40 p n.
Proof. exact (EQ_MP (@lem1009807 p n) (@lem1009806 n p)). Qed.
Lemma lem1009809 (p : nat) (n : nat) (m : nat) : term99 p n m.
Proof. exact (@lem1009808 p n m). Qed.
Lemma lem1009810 (m : nat) (p : nat) (n : nat) : (term99 p n m) = (term29 m p n).
Proof. exact (eq_refl (term99 p n m)). Qed.
Lemma lem1009811 (m : nat) (p : nat) (n : nat) : term29 m p n.
Proof. exact (EQ_MP (@lem1009810 m p n) (@lem1009809 p n m)). Qed.
Lemma lem1009813 (m : nat) (p : nat) (n : nat) : term29 m p n.
Proof. exact (@lem1009351 m p n (@lem1009811 m p n)). Qed.
Lemma lem1009814 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : term33.
Proof. exact (@lem1009813 m p n (@lem1009336 m p n h1)). Qed.
Lemma lem1009815 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : False.
Proof. exact (@lem1009814 m p n h1 (@lem77775)). Qed.
Lemma lem1009816 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : (term28 m p n) = False.
Proof. exact (prop_ext (fun h2 : term28 m p n => @lem1009815 m p n h1) (fun h2 : False => @lem1009336 m p n h1)). Qed.
Lemma lem1009817 (m : nat) (p : nat) (n : nat) (h1 : term28 m p n) : False.
Proof. exact (EQ_MP (@lem1009816 m p n h1) (@lem1009336 m p n h1)). Qed.
Lemma lem1009818 (m : nat) (p : nat) (n : nat) : term27 m p n.
Proof. exact (fun h0 : term28 m p n => @lem1009817 m p n h0). Qed.
Lemma lem1009819 (m : nat) (p : nat) (n : nat) : term25 m p n.
Proof. exact (EQ_MP (@lem1009335 m p n) (@lem1009818 m p n)). Qed.
Lemma lem1009822 (m : nat) (n : nat) (p : nat) : term24 m n p.
Proof. exact (EQ_MP (@lem1009331 m n p) (@lem1009819 m p n)). Qed.
Lemma lem1009823 (m : nat) (n : nat) (p : nat) (h1 : (term7 m n) = p) : (term7 m n) = p.
Proof. exact (h1). Qed.
Lemma lem1009824 (m : nat) (n : nat) (p : nat) (h1 : (term7 m n) = p) : (term13 n p) = True.
Proof. exact (@lem1009822 m n p (@lem1009823 m n p h1)). Qed.
