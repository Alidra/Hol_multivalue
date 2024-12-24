Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_ADD_CASES_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LT_ADD2_spec.
Require Import MOD_CASES_spec.
Require Import MULT_2_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
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
Require Import thm69_spec.
Lemma lem177173 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem177174 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem177175 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem177174 t1) (@lem177173 t1)). Qed.
Lemma lem177176 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem177175 t1 t2). Qed.
Lemma lem177177 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem177178 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem177177 t1 t2) (@lem177176 t1 t2)). Qed.
Lemma lem177179 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem177178 t1 t2 t3). Qed.
Lemma lem177180 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem177181 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem177180 t1 t2 t3) (@lem177179 t1 t2 t3)). Qed.
Lemma lem177182 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem177181 t1 t2 t3)). Qed.
Lemma lem177183 (n : nat) : term7 n.
Proof. exact (@lem84996 n). Qed.
Lemma lem177184 (n : nat) : (term7 n) = ((term8 n) = (Nat.add n n)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem177186 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem177187 (n : nat) (h1 : term9) : term10 n.
Proof. exact (@lem177186 h1 n). Qed.
Lemma lem177188 (n : nat) : (term10 n) = (term11 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem177189 (n : nat) (h1 : term9) : term11 n.
Proof. exact (EQ_MP (@lem177188 n) (@lem177187 n h1)). Qed.
Lemma lem177190 (n : nat) (p : nat) (h1 : term9) : term12 n p.
Proof. exact (@lem177189 n h1 p). Qed.
Lemma lem177191 (n : nat) (p : nat) : (term12 n p) = (term13 n p).
Proof. exact (eq_refl (term12 n p)). Qed.
Lemma lem177192 (n : nat) (p : nat) (h1 : term9) : term13 n p.
Proof. exact (EQ_MP (@lem177191 n p) (@lem177190 n p h1)). Qed.
Lemma lem177193 (n : nat) (p : nat) (h1 : term14 n p) : term14 n p.
Proof. exact (h1). Qed.
Lemma lem177194 (n : nat) (p : nat) (h1 : term9) (h2 : term14 n p) : (Nat.modulo n p) = (term15 n p).
Proof. exact (@lem177192 n p h1 (@lem177193 n p h2)). Qed.
Lemma lem177195 (n : nat) (p : nat) (h1 : term14 n p) : term16 n p.
Proof. exact (fun h0 : term9 => @lem177194 n p h0 h1). Qed.
Lemma lem177196 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem177197 (n : nat) (p : nat) (h1 : term9) (h2 : term14 n p) : (Nat.modulo n p) = (term15 n p).
Proof. exact (@lem177195 n p h2 (@lem177196 h1)). Qed.
Lemma lem177198 (n : nat) (p : nat) (h1 : term9) : term13 n p.
Proof. exact (fun h0 : term14 n p => @lem177197 n p h1 h0). Qed.
Lemma lem177199 (n : nat) (h1 : term9) : term11 n.
Proof. exact (fun p : nat => @lem177198 n p h1). Qed.
Lemma lem177200 (h1 : term9) : term9.
Proof. exact (fun n : nat => @lem177199 n h1). Qed.
Lemma lem177201 : term17.
Proof. exact (fun h0 : term9 => @lem177200 h0). Qed.
Lemma lem177202 : term9.
Proof. exact (@lem177201 (@lem177172)). Qed.
Lemma lem177203 (n : nat) : term10 n.
Proof. exact (@lem177202 n). Qed.
Lemma lem177204 (n : nat) : (term10 n) = (term11 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem177205 (n : nat) : term11 n.
Proof. exact (EQ_MP (@lem177204 n) (@lem177203 n)). Qed.
Lemma lem177206 (n : nat) (p : nat) : term12 n p.
Proof. exact (@lem177205 n p). Qed.
Lemma lem177207 (n : nat) (p : nat) : (term12 n p) = (term13 n p).
Proof. exact (eq_refl (term12 n p)). Qed.
Lemma lem177209 (m : nat) (n : nat) (p : nat) (h1 : term18 m n p) : term18 m n p.
Proof. exact (h1). Qed.
Lemma lem177210 (n : nat) (p : nat) (h1 : Peano.lt n p) : Peano.lt n p.
Proof. exact (h1). Qed.
Lemma lem177211 (m : nat) (p : nat) (h1 : Peano.lt m p) : Peano.lt m p.
Proof. exact (h1). Qed.
Lemma lem177213 (n : nat) (p : nat) : term13 n p.
Proof. exact (EQ_MP (@lem177207 n p) (@lem177206 n p)). Qed.
Lemma lem177214 (m : nat) (n : nat) (p : nat) : term19 m n p.
Proof. exact (@lem177213 (Nat.add m n) p). Qed.
Lemma lem177216 (n : nat) : (term8 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem177184 n) (@lem177183 n)). Qed.
Lemma lem177217 (p : nat) : (term8 p) = (Nat.add p p).
Proof. exact (@lem177216 p). Qed.
Lemma lem177218 (m : nat) (n : nat) : (term20 m n) = (term20 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem177219 (m : nat) (n : nat) (p : nat) : (term21 m n p) = (term22 m n p).
Proof. exact (MK_COMB (@lem177218 m n) (@lem177217 p)). Qed.
Lemma lem177220 (m : nat) (n : nat) (p : nat) : (term22 m n p) = (term21 m n p).
Proof. exact (SYM (@lem177219 m n p)). Qed.
Lemma lem177222 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem177223 (m : nat) (n : nat) (p : nat) : (term22 m n p) = (term24 m n p).
Proof. exact (@lem177222 (term22 m n p)). Qed.
Lemma lem177224 (m : nat) (n : nat) (p : nat) : (term24 m n p) = (term22 m n p).
Proof. exact (SYM (@lem177223 m n p)). Qed.
Lemma lem177225 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term25 m n p.
Proof. exact (h1). Qed.
Lemma lem177228 (m : nat) (n : nat) (p : nat) (h1 : term26 m n p) : term26 m n p.
Proof. exact (h1). Qed.
Lemma lem177229 (m : nat) (n : nat) (p : nat) : term27 m n p.
Proof. exact (fun h0 : term26 m n p => @lem177228 m n p h0). Qed.
Lemma lem177230 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : term27 m n p.
Proof. exact (h1). Qed.
Lemma lem177231 (m : nat) (n : nat) (p : nat) (h1 : term26 m n p) : term26 m n p.
Proof. exact (h1). Qed.
Lemma lem177232 (m : nat) (n : nat) (p : nat) (h1 : term26 m n p) (h2 : term27 m n p) : term26 m n p.
Proof. exact (@lem177230 m n p h2 (@lem177231 m n p h1)). Qed.
Lemma lem177233 (m : nat) (n : nat) (p : nat) (h1 : term26 m n p) : term28 m n p.
Proof. exact (fun h0 : term27 m n p => @lem177232 m n p h1 h0). Qed.
Lemma lem177234 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : term27 m n p.
Proof. exact (h1). Qed.
Lemma lem177235 (m : nat) (n : nat) (p : nat) (h1 : term26 m n p) (h2 : term27 m n p) : term26 m n p.
Proof. exact (@lem177233 m n p h1 (@lem177234 m n p h2)). Qed.
Lemma lem177236 (m : nat) (n : nat) (p : nat) (h1 : term27 m n p) : term27 m n p.
Proof. exact (fun h0 : term26 m n p => @lem177235 m n p h0 h1). Qed.
Lemma lem177237 (m : nat) (n : nat) (p : nat) : term29 m n p.
Proof. exact (fun h0 : term27 m n p => @lem177236 m n p h0). Qed.
Lemma lem177240 (m : nat) (n : nat) (p : nat) : term27 m n p.
Proof. exact (@lem177237 m n p (@lem177229 m n p)). Qed.
Lemma lem177260 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem177261 : term30 = term31.
Proof. exact (@lem177260 term32). Qed.
Lemma lem177282 (m : nat) (n : nat) (p : nat) : (term33 m n p) = (term33 m n p).
Proof. exact (eq_refl (term33 m n p)). Qed.
Lemma lem177283 (m : nat) (n : nat) (p : nat) : (term34 m n p) = (term35 m n p).
Proof. exact (MK_COMB (@lem177282 m n p) (@lem177261)). Qed.
Lemma lem177286 (n : nat) (p : nat) : (term36 n p) = (term36 n p).
Proof. exact (eq_refl (term36 n p)). Qed.
Lemma lem177287 (m : nat) (n : nat) (p : nat) : (term37 m n p) = (term38 m n p).
Proof. exact (MK_COMB (@lem177286 n p) (@lem177283 m n p)). Qed.
Lemma lem177290 (m : nat) (p : nat) : (term36 m p) = (term36 m p).
Proof. exact (eq_refl (term36 m p)). Qed.
Lemma lem177291 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term39 m n p).
Proof. exact (MK_COMB (@lem177290 m p) (@lem177287 m n p)). Qed.
Lemma lem177294 (n : nat) (p : nat) : (term40 n p) = (term41 n p).
Proof. exact (fun_ext (fun m : nat => @lem177291 m n p)). Qed.
Lemma lem177295 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177296 (n : nat) (p : nat) : (term42 n p) = (term43 n p).
Proof. exact (MK_COMB (@lem177295) (@lem177294 n p)). Qed.
Lemma lem177301 (p : nat) : (term44 p) = (term45 p).
Proof. exact (fun_ext (fun n : nat => @lem177296 n p)). Qed.
Lemma lem177302 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177303 (p : nat) : (term46 p) = (term47 p).
Proof. exact (MK_COMB (@lem177302) (@lem177301 p)). Qed.
Lemma lem177308 : term48 = term49.
Proof. exact (fun_ext (fun p : nat => @lem177303 p)). Qed.
Lemma lem177309 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177318 : term50 = term51.
Proof. exact (MK_COMB (@lem177309) (@lem177308)). Qed.
Lemma lem177327 (m : nat) (n : nat) (p : nat) (q : nat) : (term52 m n p q) = (term52 m n p q).
Proof. exact (eq_refl (term52 m n p q)). Qed.
Lemma lem177328 (m : nat) (n : nat) (p : nat) : (term53 m n p) = (term53 m n p).
Proof. exact (fun_ext (fun q : nat => @lem177327 m n p q)). Qed.
Lemma lem177329 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177330 (m : nat) (n : nat) (p : nat) : (term54 m n p) = (term54 m n p).
Proof. exact (MK_COMB (@lem177329) (@lem177328 m n p)). Qed.
Lemma lem177331 (m : nat) (n : nat) : (term55 m n) = (term55 m n).
Proof. exact (fun_ext (fun p : nat => @lem177330 m n p)). Qed.
Lemma lem177332 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177333 (m : nat) (n : nat) : (term56 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem177332) (@lem177331 m n)). Qed.
Lemma lem177334 (m : nat) : (term57 m) = (term57 m).
Proof. exact (fun_ext (fun n : nat => @lem177333 m n)). Qed.
Lemma lem177335 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177336 (m : nat) : (term58 m) = (term58 m).
Proof. exact (MK_COMB (@lem177335) (@lem177334 m)). Qed.
Lemma lem177337 : term59 = term59.
Proof. exact (fun_ext (fun m : nat => @lem177336 m)). Qed.
Lemma lem177338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177339 : term32 = term32.
Proof. exact (MK_COMB (@lem177338) (@lem177337)). Qed.
Lemma lem177340 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem177341 : term31 = term31.
Proof. exact (MK_COMB (@lem177340) (@lem177339)). Qed.
Lemma lem177346 (m : nat) (n : nat) (p : nat) : (term33 m n p) = (term33 m n p).
Proof. exact (eq_refl (term33 m n p)). Qed.
Lemma lem177347 (m : nat) (n : nat) (p : nat) : (term35 m n p) = (term35 m n p).
Proof. exact (MK_COMB (@lem177346 m n p) (@lem177341)). Qed.
Lemma lem177350 (n : nat) (p : nat) : (term36 n p) = (term36 n p).
Proof. exact (eq_refl (term36 n p)). Qed.
Lemma lem177351 (m : nat) (n : nat) (p : nat) : (term38 m n p) = (term38 m n p).
Proof. exact (MK_COMB (@lem177350 n p) (@lem177347 m n p)). Qed.
Lemma lem177354 (m : nat) (p : nat) : (term36 m p) = (term36 m p).
Proof. exact (eq_refl (term36 m p)). Qed.
Lemma lem177355 (m : nat) (n : nat) (p : nat) : (term39 m n p) = (term39 m n p).
Proof. exact (MK_COMB (@lem177354 m p) (@lem177351 m n p)). Qed.
Lemma lem177356 (n : nat) (p : nat) : (term41 n p) = (term41 n p).
Proof. exact (fun_ext (fun m : nat => @lem177355 m n p)). Qed.
Lemma lem177357 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177358 (n : nat) (p : nat) : (term43 n p) = (term43 n p).
Proof. exact (MK_COMB (@lem177357) (@lem177356 n p)). Qed.
Lemma lem177359 (p : nat) : (term45 p) = (term45 p).
Proof. exact (fun_ext (fun n : nat => @lem177358 n p)). Qed.
Lemma lem177360 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177361 (p : nat) : (term47 p) = (term47 p).
Proof. exact (MK_COMB (@lem177360) (@lem177359 p)). Qed.
Lemma lem177362 : term49 = term49.
Proof. exact (fun_ext (fun p : nat => @lem177361 p)). Qed.
Lemma lem177363 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177364 : term51 = term51.
Proof. exact (MK_COMB (@lem177363) (@lem177362)). Qed.
Lemma lem177419 : term50 = term51.
Proof. exact (TRANS (@lem177318) (@lem177364)). Qed.
Lemma lem177420 : term51 = term50.
Proof. exact (SYM (@lem177419)). Qed.
Lemma lem177424 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem177430 (m : nat) (p : nat) (h1 : Peano.lt m p) : Peano.lt m p.
Proof. exact (h1). Qed.
Lemma lem177436 (n : nat) (p : nat) (h1 : Peano.lt n p) : Peano.lt n p.
Proof. exact (h1). Qed.
Lemma lem177442 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term25 m n p.
Proof. exact (h1). Qed.
Lemma lem177449 (m : nat) (p : nat) (n : nat) (q : nat) : (term60 m p n q) = (term61 m p n q).
Proof. exact (@lem17045 (Peano.lt m p) (Peano.lt n q)). Qed.
Lemma lem177450 (m : nat) (n : nat) (p : nat) (q : nat) : (term62 m n p q) = (term62 m n p q).
Proof. exact (eq_refl (term62 m n p q)). Qed.
Lemma lem177451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem177452 (m : nat) (p : nat) (n : nat) (q : nat) : (term63 m p n q) = (term64 m p n q).
Proof. exact (MK_COMB (@lem177451) (@lem177449 m p n q)). Qed.
Lemma lem177453 (m : nat) (n : nat) (p : nat) (q : nat) : (term65 m n p q) = (term66 m n p q).
Proof. exact (MK_COMB (@lem177452 m p n q) (@lem177450 m n p q)). Qed.
Lemma lem177454 (m : nat) (n : nat) (p : nat) (q : nat) : (term52 m n p q) = (term65 m n p q).
Proof. exact (@lem17265 (term67 m p n q) (term62 m n p q)). Qed.
Lemma lem177455 (m : nat) (n : nat) (p : nat) (q : nat) : (term52 m n p q) = (term66 m n p q).
Proof. exact (TRANS (@lem177454 m n p q) (@lem177453 m n p q)). Qed.
Lemma lem177456 (m : nat) (n : nat) (p : nat) : (term53 m n p) = (term68 m n p).
Proof. exact (fun_ext (fun q : nat => @lem177455 m n p q)). Qed.
Lemma lem177457 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177458 (m : nat) (n : nat) (p : nat) : (term54 m n p) = (term69 m n p).
Proof. exact (MK_COMB (@lem177457) (@lem177456 m n p)). Qed.
Lemma lem177459 (m : nat) (n : nat) : (term55 m n) = (term70 m n).
Proof. exact (fun_ext (fun p : nat => @lem177458 m n p)). Qed.
Lemma lem177460 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177461 (m : nat) (n : nat) : (term56 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem177460) (@lem177459 m n)). Qed.
Lemma lem177462 (m : nat) : (term57 m) = (term72 m).
Proof. exact (fun_ext (fun n : nat => @lem177461 m n)). Qed.
Lemma lem177463 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177464 (m : nat) : (term58 m) = (term73 m).
Proof. exact (MK_COMB (@lem177463) (@lem177462 m)). Qed.
Lemma lem177465 : term59 = term74.
Proof. exact (fun_ext (fun m : nat => @lem177464 m)). Qed.
Lemma lem177466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177531 : term32 = term75.
Proof. exact (MK_COMB (@lem177466) (@lem177465)). Qed.
Lemma lem177532 (h1 : term32) : term75.
Proof. exact (EQ_MP (@lem177531) (@lem177424 h1)). Qed.
Lemma lem177538 (m : nat) (p : nat) (h1 : Peano.lt m p) : Peano.lt m p.
Proof. exact (h1). Qed.
Lemma lem177544 (n : nat) (p : nat) (h1 : Peano.lt n p) : Peano.lt n p.
Proof. exact (h1). Qed.
Lemma lem177560 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term25 m n p.
Proof. exact (h1). Qed.
Lemma lem177593 (m : nat) (n : nat) (p : nat) (q : nat) : (term66 m n p q) = (term66 m n p q).
Proof. exact (eq_refl (term66 m n p q)). Qed.
Lemma lem177594 (m : nat) (n : nat) (p : nat) : (term68 m n p) = (term68 m n p).
Proof. exact (fun_ext (fun q : nat => @lem177593 m n p q)). Qed.
Lemma lem177595 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177596 (m : nat) (n : nat) (p : nat) : (term69 m n p) = (term69 m n p).
Proof. exact (MK_COMB (@lem177595) (@lem177594 m n p)). Qed.
Lemma lem177597 (m : nat) (n : nat) : (term70 m n) = (term70 m n).
Proof. exact (fun_ext (fun p : nat => @lem177596 m n p)). Qed.
Lemma lem177598 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177599 (m : nat) (n : nat) : (term71 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem177598) (@lem177597 m n)). Qed.
Lemma lem177600 (m : nat) : (term72 m) = (term72 m).
Proof. exact (fun_ext (fun n : nat => @lem177599 m n)). Qed.
Lemma lem177601 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177602 (m : nat) : (term73 m) = (term73 m).
Proof. exact (MK_COMB (@lem177601) (@lem177600 m)). Qed.
Lemma lem177603 : term74 = term74.
Proof. exact (fun_ext (fun m : nat => @lem177602 m)). Qed.
Lemma lem177604 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177605 : term75 = term75.
Proof. exact (MK_COMB (@lem177604) (@lem177603)). Qed.
Lemma lem177606 (h1 : term32) : term75.
Proof. exact (EQ_MP (@lem177605) (@lem177532 h1)). Qed.
Lemma lem177610 (m : nat) (p : nat) (h1 : Peano.lt m p) : Peano.lt m p.
Proof. exact (h1). Qed.
Lemma lem177614 (n : nat) (p : nat) (h1 : Peano.lt n p) : Peano.lt n p.
Proof. exact (h1). Qed.
Lemma lem177618 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term25 m n p.
Proof. exact (h1). Qed.
Lemma lem177632 (m : nat) (n : nat) (p : nat) (q : nat) : (term66 m n p q) = (term66 m n p q).
Proof. exact (eq_refl (term66 m n p q)). Qed.
Lemma lem177633 (m : nat) (n : nat) (p : nat) : (term68 m n p) = (term68 m n p).
Proof. exact (fun_ext (fun q : nat => @lem177632 m n p q)). Qed.
Lemma lem177634 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177635 (m : nat) (n : nat) (p : nat) : (term69 m n p) = (term69 m n p).
Proof. exact (MK_COMB (@lem177634) (@lem177633 m n p)). Qed.
Lemma lem177636 (m : nat) (n : nat) : (term70 m n) = (term70 m n).
Proof. exact (fun_ext (fun p : nat => @lem177635 m n p)). Qed.
Lemma lem177637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177638 (m : nat) (n : nat) : (term71 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem177637) (@lem177636 m n)). Qed.
Lemma lem177639 (m : nat) : (term72 m) = (term72 m).
Proof. exact (fun_ext (fun n : nat => @lem177638 m n)). Qed.
Lemma lem177640 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177641 (m : nat) : (term73 m) = (term73 m).
Proof. exact (MK_COMB (@lem177640) (@lem177639 m)). Qed.
Lemma lem177642 : term74 = term74.
Proof. exact (fun_ext (fun m : nat => @lem177641 m)). Qed.
Lemma lem177643 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem177645 : term75 = term75.
Proof. exact (MK_COMB (@lem177643) (@lem177642)). Qed.
Lemma lem177646 (h1 : term32) : term75.
Proof. exact (EQ_MP (@lem177645) (@lem177606 h1)). Qed.
Lemma lem177647 (_3720 : nat) (h1 : term32) : term76 _3720.
Proof. exact (@lem177646 h1 _3720). Qed.
Lemma lem177648 (_3720 : nat) : (term76 _3720) = (term73 _3720).
Proof. exact (eq_refl (term76 _3720)). Qed.
Lemma lem177649 (_3720 : nat) (h1 : term32) : term73 _3720.
Proof. exact (EQ_MP (@lem177648 _3720) (@lem177647 _3720 h1)). Qed.
Lemma lem177650 (_3720 : nat) (_3721 : nat) (h1 : term32) : term77 _3720 _3721.
Proof. exact (@lem177649 _3720 h1 _3721). Qed.
Lemma lem177651 (_3720 : nat) (_3721 : nat) : (term77 _3720 _3721) = (term71 _3720 _3721).
Proof. exact (eq_refl (term77 _3720 _3721)). Qed.
Lemma lem177652 (_3720 : nat) (_3721 : nat) (h1 : term32) : term71 _3720 _3721.
Proof. exact (EQ_MP (@lem177651 _3720 _3721) (@lem177650 _3720 _3721 h1)). Qed.
Lemma lem177653 (_3720 : nat) (_3721 : nat) (_3722 : nat) (h1 : term32) : term78 _3720 _3721 _3722.
Proof. exact (@lem177652 _3720 _3721 h1 _3722). Qed.
Lemma lem177654 (_3720 : nat) (_3721 : nat) (_3722 : nat) : (term78 _3720 _3721 _3722) = (term69 _3720 _3721 _3722).
Proof. exact (eq_refl (term78 _3720 _3721 _3722)). Qed.
Lemma lem177655 (_3720 : nat) (_3721 : nat) (_3722 : nat) (h1 : term32) : term69 _3720 _3721 _3722.
Proof. exact (EQ_MP (@lem177654 _3720 _3721 _3722) (@lem177653 _3720 _3721 _3722 h1)). Qed.
Lemma lem177656 (_3720 : nat) (_3721 : nat) (_3722 : nat) (_3723 : nat) (h1 : term32) : term79 _3720 _3721 _3722 _3723.
Proof. exact (@lem177655 _3720 _3721 _3722 h1 _3723). Qed.
Lemma lem177657 (_3720 : nat) (_3721 : nat) (_3722 : nat) (_3723 : nat) : (term79 _3720 _3721 _3722 _3723) = (term66 _3720 _3721 _3722 _3723).
Proof. exact (eq_refl (term79 _3720 _3721 _3722 _3723)). Qed.
Lemma lem177658 (_3720 : nat) (_3721 : nat) (_3722 : nat) (_3723 : nat) (h1 : term32) : term66 _3720 _3721 _3722 _3723.
Proof. exact (EQ_MP (@lem177657 _3720 _3721 _3722 _3723) (@lem177656 _3720 _3721 _3722 _3723 h1)). Qed.
Lemma lem177660 (m : nat) (p : nat) (h1 : Peano.lt m p) : Peano.lt m p.
Proof. exact (h1). Qed.
Lemma lem177662 (n : nat) (p : nat) (h1 : Peano.lt n p) : Peano.lt n p.
Proof. exact (h1). Qed.
Lemma lem177664 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term25 m n p.
Proof. exact (h1). Qed.
Lemma lem177675 (_3720 : nat) (_3721 : nat) (_3722 : nat) (_3723 : nat) : (term66 _3720 _3721 _3722 _3723) = (term80 _3720 _3721 _3722 _3723).
Proof. exact (@lem177182 (term81 _3720 _3722) (term81 _3721 _3723) (term62 _3720 _3721 _3722 _3723)). Qed.
Lemma lem177676 (_3720 : nat) (_3721 : nat) (_3722 : nat) (_3723 : nat) (h1 : term32) : term80 _3720 _3721 _3722 _3723.
Proof. exact (EQ_MP (@lem177675 _3720 _3721 _3722 _3723) (@lem177658 _3720 _3721 _3722 _3723 h1)). Qed.
Lemma lem177678 (m : nat) (p : nat) (h1 : Peano.lt m p) : Peano.lt m p.
Proof. exact (h1). Qed.
Lemma lem177679 (m : nat) (p : nat) (h1 : Peano.lt m p) : term82 m p.
Proof. exact (fun h0 : term81 m p => @lem177678 m p h1). Qed.
Lemma lem177681 (p : Prop) : (term83 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem177682 (m : nat) (p : nat) : (term82 m p) = (Peano.lt m p).
Proof. exact (@lem177681 (Peano.lt m p)). Qed.
Lemma lem177683 (m : nat) (p : nat) (h1 : Peano.lt m p) : Peano.lt m p.
Proof. exact (EQ_MP (@lem177682 m p) (@lem177679 m p h1)). Qed.
Lemma lem177685 (n : nat) (p : nat) (h1 : Peano.lt n p) : Peano.lt n p.
Proof. exact (h1). Qed.
Lemma lem177686 (n : nat) (p : nat) (h1 : Peano.lt n p) : term82 n p.
Proof. exact (fun h0 : term81 n p => @lem177685 n p h1). Qed.
Lemma lem177688 (p : Prop) : (term83 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem177689 (n : nat) (p : nat) : (term82 n p) = (Peano.lt n p).
Proof. exact (@lem177688 (Peano.lt n p)). Qed.
Lemma lem177690 (n : nat) (p : nat) (h1 : Peano.lt n p) : Peano.lt n p.
Proof. exact (EQ_MP (@lem177689 n p) (@lem177686 n p h1)). Qed.
Lemma lem177706 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem177707 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : (term84 _3720 _3721 _3722 _3723) = (term85 _3720 _3722 _3721 _3723).
Proof. exact (@lem177706 (term62 _3720 _3721 _3722 _3723) (term81 _3721 _3723)). Qed.
Lemma lem177713 (_3720 : nat) (_3722 : nat) : (term86 _3720 _3722) = (term86 _3720 _3722).
Proof. exact (eq_refl (term86 _3720 _3722)). Qed.
Lemma lem177714 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : (term80 _3720 _3721 _3722 _3723) = (term87 _3720 _3722 _3721 _3723).
Proof. exact (MK_COMB (@lem177713 _3720 _3722) (@lem177707 _3720 _3722 _3721 _3723)). Qed.
Lemma lem177718 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem177719 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : (term87 _3720 _3722 _3721 _3723) = (term88 _3720 _3722 _3721 _3723).
Proof. exact (@lem177718 (term62 _3720 _3721 _3722 _3723) (term81 _3720 _3722) (term81 _3721 _3723)). Qed.
Lemma lem177735 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : (term80 _3720 _3721 _3722 _3723) = (term88 _3720 _3722 _3721 _3723).
Proof. exact (TRANS (@lem177714 _3720 _3722 _3721 _3723) (@lem177719 _3720 _3722 _3721 _3723)). Qed.
Lemma lem177736 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem177737 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : (term89 _3720 _3721 _3722 _3723) = (term90 _3720 _3722 _3721 _3723).
Proof. exact (MK_COMB (@lem177736) (@lem177735 _3720 _3722 _3721 _3723)). Qed.
Lemma lem177753 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : (term88 _3720 _3722 _3721 _3723) = (term88 _3720 _3722 _3721 _3723).
Proof. exact (eq_refl (term88 _3720 _3722 _3721 _3723)). Qed.
Lemma lem177754 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : ((term80 _3720 _3721 _3722 _3723) = (term88 _3720 _3722 _3721 _3723)) = ((term88 _3720 _3722 _3721 _3723) = (term88 _3720 _3722 _3721 _3723)).
Proof. exact (MK_COMB (@lem177737 _3720 _3722 _3721 _3723) (@lem177753 _3720 _3722 _3721 _3723)). Qed.
Lemma lem177756 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem177757 (x : Prop) : (x = x) = True.
Proof. exact (@lem177756 Prop x). Qed.
Lemma lem177758 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : ((term88 _3720 _3722 _3721 _3723) = (term88 _3720 _3722 _3721 _3723)) = True.
Proof. exact (@lem177757 (term88 _3720 _3722 _3721 _3723)). Qed.
Lemma lem177759 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : ((term80 _3720 _3721 _3722 _3723) = (term88 _3720 _3722 _3721 _3723)) = True.
Proof. exact (TRANS (@lem177754 _3720 _3722 _3721 _3723) (@lem177758 _3720 _3722 _3721 _3723)). Qed.
Lemma lem177760 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : True = ((term80 _3720 _3721 _3722 _3723) = (term88 _3720 _3722 _3721 _3723)).
Proof. exact (SYM (@lem177759 _3720 _3722 _3721 _3723)). Qed.
Lemma lem177761 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : (term80 _3720 _3721 _3722 _3723) = (term88 _3720 _3722 _3721 _3723).
Proof. exact (EQ_MP (@lem177760 _3720 _3722 _3721 _3723) (@lem0)). Qed.
Lemma lem177762 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) (h1 : term32) : term88 _3720 _3722 _3721 _3723.
Proof. exact (EQ_MP (@lem177761 _3720 _3722 _3721 _3723) (@lem177676 _3720 _3721 _3722 _3723 h1)). Qed.
Lemma lem177764 (b : Prop) (a : Prop) : (a \/ b) = (term91 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem177765 (_3720 : nat) (_3721 : nat) (_3722 : nat) (_3723 : nat) : (term88 _3720 _3722 _3721 _3723) = (term92 _3720 _3721 _3722 _3723).
Proof. exact (@lem177764 (term61 _3720 _3722 _3721 _3723) (term62 _3720 _3721 _3722 _3723)). Qed.
Lemma lem177767 (a : Prop) (b : Prop) : (term93 a b) = (term94 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem177768 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : (term95 _3720 _3722 _3721 _3723) = (term96 _3720 _3722 _3721 _3723).
Proof. exact (@lem177767 (term81 _3720 _3722) (term81 _3721 _3723)). Qed.
Lemma lem177770 (a : Prop) : (term97 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem177771 (_3720 : nat) (_3722 : nat) : (term98 _3720 _3722) = (Peano.lt _3720 _3722).
Proof. exact (@lem177770 (Peano.lt _3720 _3722)). Qed.
Lemma lem177772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem177773 (_3720 : nat) (_3722 : nat) : (term99 _3720 _3722) = (term100 _3720 _3722).
Proof. exact (MK_COMB (@lem177772) (@lem177771 _3720 _3722)). Qed.
Lemma lem177775 (a : Prop) : (term97 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem177776 (_3721 : nat) (_3723 : nat) : (term98 _3721 _3723) = (Peano.lt _3721 _3723).
Proof. exact (@lem177775 (Peano.lt _3721 _3723)). Qed.
Lemma lem177777 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : (term96 _3720 _3722 _3721 _3723) = (term67 _3720 _3722 _3721 _3723).
Proof. exact (MK_COMB (@lem177773 _3720 _3722) (@lem177776 _3721 _3723)). Qed.
Lemma lem177778 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : (term95 _3720 _3722 _3721 _3723) = (term67 _3720 _3722 _3721 _3723).
Proof. exact (TRANS (@lem177768 _3720 _3722 _3721 _3723) (@lem177777 _3720 _3722 _3721 _3723)). Qed.
Lemma lem177779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem177780 (_3720 : nat) (_3722 : nat) (_3721 : nat) (_3723 : nat) : (term101 _3720 _3722 _3721 _3723) = (term102 _3720 _3722 _3721 _3723).
Proof. exact (MK_COMB (@lem177779) (@lem177778 _3720 _3722 _3721 _3723)). Qed.
Lemma lem177781 (_3720 : nat) (_3721 : nat) (_3722 : nat) (_3723 : nat) : (term62 _3720 _3721 _3722 _3723) = (term62 _3720 _3721 _3722 _3723).
Proof. exact (eq_refl (term62 _3720 _3721 _3722 _3723)). Qed.
Lemma lem177782 (_3720 : nat) (_3721 : nat) (_3722 : nat) (_3723 : nat) : (term92 _3720 _3721 _3722 _3723) = (term52 _3720 _3721 _3722 _3723).
Proof. exact (MK_COMB (@lem177780 _3720 _3722 _3721 _3723) (@lem177781 _3720 _3721 _3722 _3723)). Qed.
Lemma lem177783 (_3720 : nat) (_3721 : nat) (_3722 : nat) (_3723 : nat) : (term88 _3720 _3722 _3721 _3723) = (term52 _3720 _3721 _3722 _3723).
Proof. exact (TRANS (@lem177765 _3720 _3721 _3722 _3723) (@lem177782 _3720 _3721 _3722 _3723)). Qed.
Lemma lem177785 (m : nat) (n : nat) (p : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n p) : term18 m n p.
Proof. exact (conj (@lem177683 m p h1) (@lem177690 n p h2)). Qed.
Lemma lem177787 (_3720 : nat) (_3721 : nat) (_3722 : nat) (_3723 : nat) (h1 : term32) : term52 _3720 _3721 _3722 _3723.
Proof. exact (EQ_MP (@lem177783 _3720 _3721 _3722 _3723) (@lem177762 _3720 _3722 _3721 _3723 h1)). Qed.
Lemma lem177788 (m : nat) (n : nat) (p : nat) (h1 : term32) : term103 m n p.
Proof. exact (@lem177787 m n p p h1). Qed.
Lemma lem177791 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : Peano.lt m p) (h3 : Peano.lt n p) : term22 m n p.
Proof. exact (@lem177788 m n p h1 (@lem177785 m n p h2 h3)). Qed.
Lemma lem177792 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : Peano.lt m p) (h3 : Peano.lt n p) : term104 m n p.
Proof. exact (fun h0 : term25 m n p => @lem177791 m n p h1 h2 h3). Qed.
Lemma lem177794 (p : Prop) : (term83 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem177795 (m : nat) (n : nat) (p : nat) : (term104 m n p) = (term22 m n p).
Proof. exact (@lem177794 (term22 m n p)). Qed.
Lemma lem177796 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : Peano.lt m p) (h3 : Peano.lt n p) : term22 m n p.
Proof. exact (EQ_MP (@lem177795 m n p) (@lem177792 m n p h1 h2 h3)). Qed.
Lemma lem177799 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem177801 (m : nat) (n : nat) (p : nat) : (term25 m n p) = (term105 m n p).
Proof. exact (@lem177799 (term22 m n p)). Qed.
Lemma lem177804 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term105 m n p.
Proof. exact (EQ_MP (@lem177801 m n p) (@lem177664 m n p h1)). Qed.
Lemma lem177807 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (@lem177804 m n p h2 (@lem177796 m n p h1 h3 h4)). Qed.
Lemma lem177808 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : term106.
Proof. exact (fun h0 : ~ False => @lem177807 m n p h1 h2 h3 h4). Qed.
Lemma lem177810 (p : Prop) : (term83 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem177811 : term106 = False.
Proof. exact (@lem177810 False). Qed.
Lemma lem177812 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177811) (@lem177808 m n p h1 h2 h3 h4)). Qed.
Lemma lem177813 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (term25 m n p) = False.
Proof. exact (prop_ext (fun h5 : term25 m n p => @lem177812 m n p h1 h2 h3 h4) (fun h5 : False => @lem177664 m n p h2)). Qed.
Lemma lem177814 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177813 m n p h1 h2 h3 h4) (@lem177664 m n p h2)). Qed.
Lemma lem177815 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (Peano.lt n p) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt n p => @lem177814 m n p h1 h2 h3 h4) (fun h5 : False => @lem177662 n p h4)). Qed.
Lemma lem177816 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177815 m n p h1 h2 h3 h4) (@lem177662 n p h4)). Qed.
Lemma lem177817 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (Peano.lt m p) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt m p => @lem177816 m n p h1 h2 h3 h4) (fun h5 : False => @lem177660 m p h3)). Qed.
Lemma lem177818 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177817 m n p h1 h2 h3 h4) (@lem177660 m p h3)). Qed.
Lemma lem177819 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (term25 m n p) = False.
Proof. exact (prop_ext (fun h5 : term25 m n p => @lem177818 m n p h1 h2 h3 h4) (fun h5 : False => @lem177618 m n p h2)). Qed.
Lemma lem177820 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177819 m n p h1 h2 h3 h4) (@lem177618 m n p h2)). Qed.
Lemma lem177821 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (Peano.lt n p) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt n p => @lem177820 m n p h1 h2 h3 h4) (fun h5 : False => @lem177614 n p h4)). Qed.
Lemma lem177822 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177821 m n p h1 h2 h3 h4) (@lem177614 n p h4)). Qed.
Lemma lem177823 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (Peano.lt m p) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt m p => @lem177822 m n p h1 h2 h3 h4) (fun h5 : False => @lem177610 m p h3)). Qed.
Lemma lem177824 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177823 m n p h1 h2 h3 h4) (@lem177610 m p h3)). Qed.
Lemma lem177825 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (term25 m n p) = False.
Proof. exact (prop_ext (fun h5 : term25 m n p => @lem177824 m n p h1 h2 h3 h4) (fun h5 : False => @lem177618 m n p h2)). Qed.
Lemma lem177826 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177825 m n p h1 h2 h3 h4) (@lem177618 m n p h2)). Qed.
Lemma lem177827 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (Peano.lt n p) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt n p => @lem177826 m n p h1 h2 h3 h4) (fun h5 : False => @lem177614 n p h4)). Qed.
Lemma lem177828 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177827 m n p h1 h2 h3 h4) (@lem177614 n p h4)). Qed.
Lemma lem177829 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (Peano.lt m p) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt m p => @lem177828 m n p h1 h2 h3 h4) (fun h5 : False => @lem177610 m p h3)). Qed.
Lemma lem177830 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177829 m n p h1 h2 h3 h4) (@lem177610 m p h3)). Qed.
Lemma lem177831 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (term25 m n p) = False.
Proof. exact (prop_ext (fun h5 : term25 m n p => @lem177830 m n p h1 h2 h3 h4) (fun h5 : False => @lem177560 m n p h2)). Qed.
Lemma lem177832 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177831 m n p h1 h2 h3 h4) (@lem177560 m n p h2)). Qed.
Lemma lem177833 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (Peano.lt n p) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt n p => @lem177832 m n p h1 h2 h3 h4) (fun h5 : False => @lem177544 n p h4)). Qed.
Lemma lem177834 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177833 m n p h1 h2 h3 h4) (@lem177544 n p h4)). Qed.
Lemma lem177835 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (Peano.lt m p) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt m p => @lem177834 m n p h1 h2 h3 h4) (fun h5 : False => @lem177538 m p h3)). Qed.
Lemma lem177836 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177835 m n p h1 h2 h3 h4) (@lem177538 m p h3)). Qed.
Lemma lem177837 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (term25 m n p) = False.
Proof. exact (prop_ext (fun h5 : term25 m n p => @lem177836 m n p h1 h2 h3 h4) (fun h5 : False => @lem177442 m n p h2)). Qed.
Lemma lem177838 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177837 m n p h1 h2 h3 h4) (@lem177442 m n p h2)). Qed.
Lemma lem177839 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (Peano.lt n p) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt n p => @lem177838 m n p h1 h2 h3 h4) (fun h5 : False => @lem177436 n p h4)). Qed.
Lemma lem177840 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177839 m n p h1 h2 h3 h4) (@lem177436 n p h4)). Qed.
Lemma lem177841 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : (Peano.lt m p) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt m p => @lem177840 m n p h1 h2 h3 h4) (fun h5 : False => @lem177430 m p h3)). Qed.
Lemma lem177842 (m : nat) (n : nat) (p : nat) (h1 : term32) (h2 : term25 m n p) (h3 : Peano.lt m p) (h4 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177841 m n p h1 h2 h3 h4) (@lem177430 m p h3)). Qed.
Lemma lem177843 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) (h2 : Peano.lt m p) (h3 : Peano.lt n p) : term30.
Proof. exact (fun h0 : term32 => @lem177842 m n p h0 h1 h2 h3). Qed.
Lemma lem177844 : term30 = term31.
Proof. exact (@lem69 term32). Qed.
Lemma lem177845 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) (h2 : Peano.lt m p) (h3 : Peano.lt n p) : term31.
Proof. exact (EQ_MP (@lem177844) (@lem177843 m n p h1 h2 h3)). Qed.
Lemma lem177846 (m : nat) (n : nat) (p : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n p) : term35 m n p.
Proof. exact (fun h0 : term25 m n p => @lem177845 m n p h0 h1 h2). Qed.
Lemma lem177847 (n : nat) (m : nat) (p : nat) (h1 : Peano.lt m p) : term38 m n p.
Proof. exact (fun h0 : Peano.lt n p => @lem177846 m n p h1 h0). Qed.
Lemma lem177848 (m : nat) (n : nat) (p : nat) : term39 m n p.
Proof. exact (fun h0 : Peano.lt m p => @lem177847 n m p h0). Qed.
Lemma lem177853 (n : nat) (p : nat) : term43 n p.
Proof. exact (fun m : nat => @lem177848 m n p). Qed.
Lemma lem177858 (p : nat) : term47 p.
Proof. exact (fun n : nat => @lem177853 n p). Qed.
Lemma lem177863 : term51.
Proof. exact (fun p : nat => @lem177858 p). Qed.
Lemma lem177864 : term50.
Proof. exact (EQ_MP (@lem177420) (@lem177863)). Qed.
Lemma lem177865 (p : nat) : term107 p.
Proof. exact (@lem177864 p). Qed.
Lemma lem177866 (p : nat) : (term107 p) = (term46 p).
Proof. exact (eq_refl (term107 p)). Qed.
Lemma lem177867 (p : nat) : term46 p.
Proof. exact (EQ_MP (@lem177866 p) (@lem177865 p)). Qed.
Lemma lem177868 (p : nat) (n : nat) : term108 p n.
Proof. exact (@lem177867 p n). Qed.
Lemma lem177869 (n : nat) (p : nat) : (term108 p n) = (term42 n p).
Proof. exact (eq_refl (term108 p n)). Qed.
Lemma lem177870 (n : nat) (p : nat) : term42 n p.
Proof. exact (EQ_MP (@lem177869 n p) (@lem177868 p n)). Qed.
Lemma lem177871 (n : nat) (p : nat) (m : nat) : term109 n p m.
Proof. exact (@lem177870 n p m). Qed.
Lemma lem177872 (m : nat) (n : nat) (p : nat) : (term109 n p m) = (term26 m n p).
Proof. exact (eq_refl (term109 n p m)). Qed.
Lemma lem177873 (m : nat) (n : nat) (p : nat) : term26 m n p.
Proof. exact (EQ_MP (@lem177872 m n p) (@lem177871 n p m)). Qed.
Lemma lem177875 (m : nat) (n : nat) (p : nat) : term26 m n p.
Proof. exact (@lem177240 m n p (@lem177873 m n p)). Qed.
Lemma lem177876 (n : nat) (m : nat) (p : nat) (h1 : Peano.lt m p) : term37 m n p.
Proof. exact (@lem177875 m n p (@lem177211 m p h1)). Qed.
Lemma lem177877 (m : nat) (n : nat) (p : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n p) : term34 m n p.
Proof. exact (@lem177876 n m p h1 (@lem177210 n p h2)). Qed.
Lemma lem177878 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) (h2 : Peano.lt m p) (h3 : Peano.lt n p) : term30.
Proof. exact (@lem177877 m n p h2 h3 (@lem177225 m n p h1)). Qed.
Lemma lem177879 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) (h2 : Peano.lt m p) (h3 : Peano.lt n p) : False.
Proof. exact (@lem177878 m n p h1 h2 h3 (@lem101917)). Qed.
Lemma lem177880 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) (h2 : Peano.lt m p) (h3 : Peano.lt n p) : (term25 m n p) = False.
Proof. exact (prop_ext (fun h4 : term25 m n p => @lem177879 m n p h1 h2 h3) (fun h4 : False => @lem177225 m n p h1)). Qed.
Lemma lem177881 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) (h2 : Peano.lt m p) (h3 : Peano.lt n p) : False.
Proof. exact (EQ_MP (@lem177880 m n p h1 h2 h3) (@lem177225 m n p h1)). Qed.
Lemma lem177882 (m : nat) (n : nat) (p : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n p) : term24 m n p.
Proof. exact (fun h0 : term25 m n p => @lem177881 m n p h0 h1 h2). Qed.
Lemma lem177883 (m : nat) (n : nat) (p : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n p) : term22 m n p.
Proof. exact (EQ_MP (@lem177224 m n p) (@lem177882 m n p h1 h2)). Qed.
Lemma lem177884 (m : nat) (n : nat) (p : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n p) : term21 m n p.
Proof. exact (EQ_MP (@lem177220 m n p) (@lem177883 m n p h1 h2)). Qed.
Lemma lem177885 (m : nat) (n : nat) (p : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n p) : (term110 m n p) = (term111 m n p).
Proof. exact (@lem177214 m n p (@lem177884 m n p h1 h2)). Qed.
Lemma lem177886 (m : nat) (n : nat) (p : nat) (h1 : term18 m n p) : Peano.lt n p.
Proof. exact (proj2 (@lem177209 m n p h1)). Qed.
Lemma lem177887 (m : nat) (n : nat) (p : nat) (h1 : term18 m n p) : Peano.lt m p.
Proof. exact (proj1 (@lem177209 m n p h1)). Qed.
Lemma lem177888 (m : nat) (n : nat) (p : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n p) : (Peano.lt n p) = ((term110 m n p) = (term111 m n p)).
Proof. exact (prop_ext (fun h3 : Peano.lt n p => @lem177885 m n p h1 h2) (fun h3 : (term110 m n p) = (term111 m n p) => @lem177210 n p h2)). Qed.
Lemma lem177889 (m : nat) (n : nat) (p : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n p) : (term110 m n p) = (term111 m n p).
Proof. exact (EQ_MP (@lem177888 m n p h1 h2) (@lem177210 n p h2)). Qed.
Lemma lem177890 (m : nat) (n : nat) (p : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n p) : (Peano.lt m p) = ((term110 m n p) = (term111 m n p)).
Proof. exact (prop_ext (fun h3 : Peano.lt m p => @lem177889 m n p h1 h2) (fun h3 : (term110 m n p) = (term111 m n p) => @lem177211 m p h1)). Qed.
Lemma lem177891 (m : nat) (n : nat) (p : nat) (h1 : Peano.lt m p) (h2 : Peano.lt n p) : (term110 m n p) = (term111 m n p).
Proof. exact (EQ_MP (@lem177890 m n p h1 h2) (@lem177211 m p h1)). Qed.
Lemma lem177892 (n : nat) (m : nat) (p : nat) (h1 : term18 m n p) (h2 : Peano.lt m p) : (Peano.lt n p) = ((term110 m n p) = (term111 m n p)).
Proof. exact (prop_ext (fun h3 : Peano.lt n p => @lem177891 m n p h2 h3) (fun h3 : (term110 m n p) = (term111 m n p) => @lem177886 m n p h1)). Qed.
Lemma lem177893 (n : nat) (m : nat) (p : nat) (h1 : term18 m n p) (h2 : Peano.lt m p) : (term110 m n p) = (term111 m n p).
Proof. exact (EQ_MP (@lem177892 n m p h1 h2) (@lem177886 m n p h1)). Qed.
Lemma lem177894 (m : nat) (n : nat) (p : nat) (h1 : term18 m n p) : (Peano.lt m p) = ((term110 m n p) = (term111 m n p)).
Proof. exact (prop_ext (fun h2 : Peano.lt m p => @lem177893 n m p h1 h2) (fun h2 : (term110 m n p) = (term111 m n p) => @lem177887 m n p h1)). Qed.
Lemma lem177895 (m : nat) (n : nat) (p : nat) (h1 : term18 m n p) : (term110 m n p) = (term111 m n p).
Proof. exact (EQ_MP (@lem177894 m n p h1) (@lem177887 m n p h1)). Qed.
Lemma lem177896 (m : nat) (n : nat) (p : nat) : term112 m n p.
Proof. exact (fun h0 : term18 m n p => @lem177895 m n p h0). Qed.
Lemma lem177901 (m : nat) (n : nat) : term113 m n.
Proof. exact (fun p : nat => @lem177896 m n p). Qed.
Lemma lem177906 (m : nat) : term114 m.
Proof. exact (fun n : nat => @lem177901 m n). Qed.
Lemma lem177911 : term115.
Proof. exact (fun m : nat => @lem177906 m). Qed.
