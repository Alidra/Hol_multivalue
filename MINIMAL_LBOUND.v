Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MINIMAL_LBOUND_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LE_MINIMAL_spec.
Require Import NOT_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem280147 (P : nat -> Prop) : term0 P.
Proof. exact (@lem276690 P). Qed.
Lemma lem280148 (P : nat -> Prop) : (term0 P) = (term1 P).
Proof. exact (eq_refl (term0 P)). Qed.
Lemma lem280149 (P : nat -> Prop) : term1 P.
Proof. exact (EQ_MP (@lem280148 P) (@lem280147 P)). Qed.
Lemma lem280150 (P : nat -> Prop) (n : nat) : term2 P n.
Proof. exact (@lem280149 P n). Qed.
Lemma lem280151 (P : nat -> Prop) (n : nat) : (term2 P n) = (term3 P n).
Proof. exact (eq_refl (term2 P n)). Qed.
Lemma lem280152 (P : nat -> Prop) (n : nat) : term3 P n.
Proof. exact (EQ_MP (@lem280151 P n) (@lem280150 P n)). Qed.
Lemma lem280153 (P : nat -> Prop) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem280154 (n : nat) (P : nat -> Prop) (h1 : term4 P) : (term5 n P) = (term6 P n).
Proof. exact (@lem280152 P n (@lem280153 P h1)). Qed.
Lemma lem280171 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term7 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem280172 (p : Prop) (q : Prop) (p' : Prop) : term8 p q p'.
Proof. exact (fun q' : Prop => @lem280171 p q p' q'). Qed.
Lemma lem280173 (p : Prop) (q : Prop) : term9 p q.
Proof. exact (fun p' : Prop => @lem280172 p q p'). Qed.
Lemma lem280174 (n : nat) (P : nat -> Prop) : term10 n P.
Proof. exact (@lem280173 (term11 n P) (term5 n P)). Qed.
Lemma lem280175 (n : nat) (P : nat -> Prop) (p' : Prop) : term12 n P p'.
Proof. exact (@lem280174 n P p'). Qed.
Lemma lem280176 (n : nat) (P : nat -> Prop) (p' : Prop) : (term12 n P p') = (term13 n P p').
Proof. exact (eq_refl (term12 n P p')). Qed.
Lemma lem280177 (n : nat) (P : nat -> Prop) (p' : Prop) : term13 n P p'.
Proof. exact (EQ_MP (@lem280176 n P p') (@lem280175 n P p')). Qed.
Lemma lem280178 (n : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : term14 n P p' q'.
Proof. exact (@lem280177 n P p' q'). Qed.
Lemma lem280179 (n : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : (term14 n P p' q') = (term15 n P p' q').
Proof. exact (eq_refl (term14 n P p' q')). Qed.
Lemma lem280180 (n : nat) (P : nat -> Prop) (p' : Prop) (q' : Prop) : term15 n P p' q'.
Proof. exact (EQ_MP (@lem280179 n P p' q') (@lem280178 n P p' q')). Qed.
Lemma lem280214 (n : nat) (P : nat -> Prop) : (term11 n P) = (term11 n P).
Proof. exact (eq_refl (term11 n P)). Qed.
Lemma lem280215 (n : nat) (P : nat -> Prop) (q' : Prop) : term16 n P q'.
Proof. exact (@lem280180 n P (term11 n P) q'). Qed.
Lemma lem280216 (n : nat) (P : nat -> Prop) (q' : Prop) : term17 n P q'.
Proof. exact (@lem280215 n P q' (@lem280214 n P)). Qed.
Lemma lem280217 (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term11 n P.
Proof. exact (h1). Qed.
Lemma lem280231 (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term4 P.
Proof. exact (proj1 (@lem280217 n P h1)). Qed.
Lemma lem280232 (P : nat -> Prop) : (term4 P) = ((term4 P) = True).
Proof. exact (@lem7 (term4 P)). Qed.
Lemma lem280235 (P : nat -> Prop) (n : nat) : term3 P n.
Proof. exact (fun h0 : term4 P => @lem280154 n P h0). Qed.
Lemma lem280237 (n : nat) (P : nat -> Prop) (h1 : term11 n P) : (term4 P) = True.
Proof. exact (EQ_MP (@lem280232 P) (@lem280231 n P h1)). Qed.
Lemma lem280238 (n : nat) (P : nat -> Prop) (h1 : term11 n P) : True = (term4 P).
Proof. exact (SYM (@lem280237 n P h1)). Qed.
Lemma lem280239 (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term4 P.
Proof. exact (EQ_MP (@lem280238 n P h1) (@lem0)). Qed.
Lemma lem280240 (n : nat) (P : nat -> Prop) (h1 : term11 n P) : (term5 n P) = (term6 P n).
Proof. exact (@lem280235 P n (@lem280239 n P h1)). Qed.
Lemma lem280278 (P : nat -> Prop) (n : nat) : term18 P n.
Proof. exact (fun h0 : term11 n P => @lem280240 n P h0). Qed.
Lemma lem280279 (P : nat -> Prop) (n : nat) : term19 P n.
Proof. exact (@lem280216 n P (term6 P n)). Qed.
Lemma lem280280 (P : nat -> Prop) (n : nat) : (term20 n P) = (term21 P n).
Proof. exact (@lem280279 P n (@lem280278 P n)). Qed.
Lemma lem280448 (P : nat -> Prop) : (term22 P) = (term23 P).
Proof. exact (fun_ext (fun n : nat => @lem280280 P n)). Qed.
Lemma lem280616 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem280617 (P : nat -> Prop) : (term24 P) = (term25 P).
Proof. exact (MK_COMB (@lem280616) (@lem280448 P)). Qed.
Lemma lem280789 : term26 = term27.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem280617 P)). Qed.
Lemma lem280961 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem280962 : term28 = term29.
Proof. exact (MK_COMB (@lem280961) (@lem280789)). Qed.
Lemma lem281138 : term29 = term28.
Proof. exact (SYM (@lem280962)). Qed.
Lemma lem281140 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem281141 : term29 = term31.
Proof. exact (@lem281140 term29). Qed.
Lemma lem281142 : term31 = term29.
Proof. exact (SYM (@lem281141)). Qed.
Lemma lem281143 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem281146 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem281147 : term34.
Proof. exact (fun h0 : term33 => @lem281146 h0). Qed.
Lemma lem281148 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem281149 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem281150 (h1 : term33) (h2 : term34) : term33.
Proof. exact (@lem281148 h2 (@lem281149 h1)). Qed.
Lemma lem281151 (h1 : term33) : term35.
Proof. exact (fun h0 : term34 => @lem281150 h1 h0). Qed.
Lemma lem281152 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem281153 (h1 : term33) (h2 : term34) : term33.
Proof. exact (@lem281151 h1 (@lem281152 h2)). Qed.
Lemma lem281154 (h1 : term34) : term34.
Proof. exact (fun h0 : term33 => @lem281153 h0 h1). Qed.
Lemma lem281155 : term36.
Proof. exact (fun h0 : term34 => @lem281154 h0). Qed.
Lemma lem281158 : term34.
Proof. exact (@lem281155 (@lem281147)). Qed.
Lemma lem281190 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem281191 : term37 = term38.
Proof. exact (@lem281190 term39). Qed.
Lemma lem281200 : term40 = term40.
Proof. exact (eq_refl term40). Qed.
Lemma lem281207 : term33 = term41.
Proof. exact (MK_COMB (@lem281200) (@lem281191)). Qed.
Lemma lem281214 (n : nat) (m : nat) : ((term42 m n) = (Peano.le n m)) = ((term42 m n) = (Peano.le n m)).
Proof. exact (eq_refl ((term42 m n) = (Peano.le n m))). Qed.
Lemma lem281215 (m : nat) : (term43 m) = (term43 m).
Proof. exact (fun_ext (fun n : nat => @lem281214 n m)). Qed.
Lemma lem281216 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281217 (m : nat) : (term44 m) = (term44 m).
Proof. exact (MK_COMB (@lem281216) (@lem281215 m)). Qed.
Lemma lem281218 : term45 = term45.
Proof. exact (fun_ext (fun m : nat => @lem281217 m)). Qed.
Lemma lem281219 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281220 : term39 = term39.
Proof. exact (MK_COMB (@lem281219) (@lem281218)). Qed.
Lemma lem281221 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem281222 : term38 = term38.
Proof. exact (MK_COMB (@lem281221) (@lem281220)). Qed.
Lemma lem281227 (P : nat -> Prop) (n : nat) (i : nat) : (term46 P n i) = (term46 P n i).
Proof. exact (eq_refl (term46 P n i)). Qed.
Lemma lem281228 (P : nat -> Prop) (n : nat) : (term47 P n) = (term47 P n).
Proof. exact (fun_ext (fun i : nat => @lem281227 P n i)). Qed.
Lemma lem281229 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281230 (P : nat -> Prop) (n : nat) : (term6 P n) = (term6 P n).
Proof. exact (MK_COMB (@lem281229) (@lem281228 P n)). Qed.
Lemma lem281237 (n : nat) (P : nat -> Prop) (m : nat) : (term48 n P m) = (term48 n P m).
Proof. exact (eq_refl (term48 n P m)). Qed.
Lemma lem281238 (n : nat) (P : nat -> Prop) : (term49 n P) = (term49 n P).
Proof. exact (fun_ext (fun m : nat => @lem281237 n P m)). Qed.
Lemma lem281239 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281240 (n : nat) (P : nat -> Prop) : (term50 n P) = (term50 n P).
Proof. exact (MK_COMB (@lem281239) (@lem281238 n P)). Qed.
Lemma lem281241 (P : nat -> Prop) (r : nat) : (P r) = (P r).
Proof. exact (eq_refl (P r)). Qed.
Lemma lem281242 (P : nat -> Prop) : (term51 P) = (term51 P).
Proof. exact (fun_ext (fun r : nat => @lem281241 P r)). Qed.
Lemma lem281243 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem281244 (P : nat -> Prop) : (term4 P) = (term4 P).
Proof. exact (MK_COMB (@lem281243) (@lem281242 P)). Qed.
Lemma lem281245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem281246 (P : nat -> Prop) : (term52 P) = (term52 P).
Proof. exact (MK_COMB (@lem281245) (@lem281244 P)). Qed.
Lemma lem281247 (n : nat) (P : nat -> Prop) : (term11 n P) = (term11 n P).
Proof. exact (MK_COMB (@lem281246 P) (@lem281240 n P)). Qed.
Lemma lem281248 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem281249 (n : nat) (P : nat -> Prop) : (term53 n P) = (term53 n P).
Proof. exact (MK_COMB (@lem281248) (@lem281247 n P)). Qed.
Lemma lem281250 (P : nat -> Prop) (n : nat) : (term21 P n) = (term21 P n).
Proof. exact (MK_COMB (@lem281249 n P) (@lem281230 P n)). Qed.
Lemma lem281251 (P : nat -> Prop) : (term23 P) = (term23 P).
Proof. exact (fun_ext (fun n : nat => @lem281250 P n)). Qed.
Lemma lem281252 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281253 (P : nat -> Prop) : (term25 P) = (term25 P).
Proof. exact (MK_COMB (@lem281252) (@lem281251 P)). Qed.
Lemma lem281254 : term27 = term27.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem281253 P)). Qed.
Lemma lem281255 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem281256 : term29 = term29.
Proof. exact (MK_COMB (@lem281255) (@lem281254)). Qed.
Lemma lem281257 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem281258 : term32 = term32.
Proof. exact (MK_COMB (@lem281257) (@lem281256)). Qed.
Lemma lem281259 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem281260 : term40 = term40.
Proof. exact (MK_COMB (@lem281259) (@lem281258)). Qed.
Lemma lem281261 : term41 = term41.
Proof. exact (MK_COMB (@lem281260) (@lem281222)). Qed.
Lemma lem281316 : term33 = term41.
Proof. exact (TRANS (@lem281207) (@lem281261)). Qed.
Lemma lem281317 : term41 = term33.
Proof. exact (SYM (@lem281316)). Qed.
Lemma lem281318 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem281319 (h1 : term39) : term39.
Proof. exact (h1). Qed.
Lemma lem281320 (P : nat -> Prop) (r : nat) : (P r) = (P r).
Proof. exact (eq_refl (P r)). Qed.
Lemma lem281321 (P : nat -> Prop) : (term51 P) = (term51 P).
Proof. exact (fun_ext (fun r : nat => @lem281320 P r)). Qed.
Lemma lem281322 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem281323 (P : nat -> Prop) : (term4 P) = (term4 P).
Proof. exact (MK_COMB (@lem281322) (@lem281321 P)). Qed.
Lemma lem281330 (n : nat) (P : nat -> Prop) (m : nat) : (term48 n P m) = (term54 n P m).
Proof. exact (@lem17265 (Peano.lt m n) (term55 P m)). Qed.
Lemma lem281331 (n : nat) (P : nat -> Prop) : (term49 n P) = (term56 n P).
Proof. exact (fun_ext (fun m : nat => @lem281330 n P m)). Qed.
Lemma lem281332 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281333 (n : nat) (P : nat -> Prop) : (term50 n P) = (term57 n P).
Proof. exact (MK_COMB (@lem281332) (@lem281331 n P)). Qed.
Lemma lem281334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem281335 (P : nat -> Prop) : (term52 P) = (term52 P).
Proof. exact (MK_COMB (@lem281334) (@lem281323 P)). Qed.
Lemma lem281336 (n : nat) (P : nat -> Prop) : (term11 n P) = (term58 n P).
Proof. exact (MK_COMB (@lem281335 P) (@lem281333 n P)). Qed.
Lemma lem281343 (P : nat -> Prop) (n : nat) (i : nat) : (term59 P n i) = (term60 P n i).
Proof. exact (@lem17362 (P i) (Peano.le n i)). Qed.
Lemma lem281344 (P : nat -> Prop) : (term61 P) = (term62 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem281345 (P : nat -> Prop) (n : nat) : (term63 P n) = (term64 P n).
Proof. exact (@lem281344 (term47 P n)). Qed.
Lemma lem281346 (P : nat -> Prop) (n : nat) (i : nat) : (term65 P n i) = (term46 P n i).
Proof. exact (eq_refl (term65 P n i)). Qed.
Lemma lem281347 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem281348 (P : nat -> Prop) (n : nat) (i : nat) : (term66 P n i) = (term59 P n i).
Proof. exact (MK_COMB (@lem281347) (@lem281346 P n i)). Qed.
Lemma lem281349 (P : nat -> Prop) (n : nat) (i : nat) : (term66 P n i) = (term60 P n i).
Proof. exact (TRANS (@lem281348 P n i) (@lem281343 P n i)). Qed.
Lemma lem281350 (P : nat -> Prop) (n : nat) : (term67 P n) = (term68 P n).
Proof. exact (fun_ext (fun i : nat => @lem281349 P n i)). Qed.
Lemma lem281351 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem281352 (P : nat -> Prop) (n : nat) : (term64 P n) = (term69 P n).
Proof. exact (MK_COMB (@lem281351) (@lem281350 P n)). Qed.
Lemma lem281353 (P : nat -> Prop) (n : nat) : (term63 P n) = (term69 P n).
Proof. exact (TRANS (@lem281345 P n) (@lem281352 P n)). Qed.
Lemma lem281354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem281355 (n : nat) (P : nat -> Prop) : (term70 n P) = (term71 n P).
Proof. exact (MK_COMB (@lem281354) (@lem281336 n P)). Qed.
Lemma lem281356 (P : nat -> Prop) (n : nat) : (term72 P n) = (term73 P n).
Proof. exact (MK_COMB (@lem281355 n P) (@lem281353 P n)). Qed.
Lemma lem281357 (P : nat -> Prop) (n : nat) : (term74 P n) = (term72 P n).
Proof. exact (@lem17362 (term11 n P) (term6 P n)). Qed.
Lemma lem281358 (P : nat -> Prop) (n : nat) : (term74 P n) = (term73 P n).
Proof. exact (TRANS (@lem281357 P n) (@lem281356 P n)). Qed.
Lemma lem281359 (P : nat -> Prop) : (term61 P) = (term62 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem281360 (P : nat -> Prop) : (term75 P) = (term76 P).
Proof. exact (@lem281359 (term23 P)). Qed.
Lemma lem281361 (P : nat -> Prop) (n : nat) : (term77 P n) = (term21 P n).
Proof. exact (eq_refl (term77 P n)). Qed.
Lemma lem281362 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem281363 (P : nat -> Prop) (n : nat) : (term78 P n) = (term74 P n).
Proof. exact (MK_COMB (@lem281362) (@lem281361 P n)). Qed.
Lemma lem281364 (P : nat -> Prop) (n : nat) : (term78 P n) = (term73 P n).
Proof. exact (TRANS (@lem281363 P n) (@lem281358 P n)). Qed.
Lemma lem281365 (P : nat -> Prop) : (term79 P) = (term80 P).
Proof. exact (fun_ext (fun n : nat => @lem281364 P n)). Qed.
Lemma lem281366 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem281367 (P : nat -> Prop) : (term76 P) = (term81 P).
Proof. exact (MK_COMB (@lem281366) (@lem281365 P)). Qed.
Lemma lem281368 (P : nat -> Prop) : (term75 P) = (term81 P).
Proof. exact (TRANS (@lem281360 P) (@lem281367 P)). Qed.
Lemma lem281369 (P : type993) : (term82 P) = (term83 P).
Proof. exact (@lem18392 (nat -> Prop) P). Qed.
Lemma lem281370 : term32 = term84.
Proof. exact (@lem281369 term27). Qed.
Lemma lem281371 (P : nat -> Prop) : (term85 P) = (term25 P).
Proof. exact (eq_refl (term85 P)). Qed.
Lemma lem281372 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem281373 (P : nat -> Prop) : (term86 P) = (term75 P).
Proof. exact (MK_COMB (@lem281372) (@lem281371 P)). Qed.
Lemma lem281374 (P : nat -> Prop) : (term86 P) = (term81 P).
Proof. exact (TRANS (@lem281373 P) (@lem281368 P)). Qed.
Lemma lem281375 : term87 = term88.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem281374 P)). Qed.
Lemma lem281376 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem281377 : term84 = term89.
Proof. exact (MK_COMB (@lem281376) (@lem281375)). Qed.
Lemma lem281378 : term32 = term89.
Proof. exact (TRANS (@lem281370) (@lem281377)). Qed.
Lemma lem281513 {A : Type'} (P : A -> Prop) (Q : Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem281514 (P : nat -> Prop) (Q : Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem281513 nat P Q). Qed.
Lemma lem281515 (n : nat) (P : nat -> Prop) : (term58 n P) = (term94 n P).
Proof. exact (@lem281514 P (term57 n P)). Qed.
Lemma lem281516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem281517 (n : nat) (P : nat -> Prop) : (term71 n P) = (term95 n P).
Proof. exact (MK_COMB (@lem281516) (@lem281515 n P)). Qed.
Lemma lem281518 (P : nat -> Prop) (n : nat) : (term69 P n) = (term69 P n).
Proof. exact (eq_refl (term69 P n)). Qed.
Lemma lem281519 (P : nat -> Prop) (n : nat) : (term73 P n) = (term96 P n).
Proof. exact (MK_COMB (@lem281517 n P) (@lem281518 P n)). Qed.
Lemma lem281521 {A : Type'} (P : A -> Prop) (Q : Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem281522 (P : nat -> Prop) (Q : Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem281521 nat P Q). Qed.
Lemma lem281523 (P : nat -> Prop) (n : nat) : (term97 P n) = (term98 P n).
Proof. exact (@lem281522 (term99 n P) (term69 P n)). Qed.
Lemma lem281524 (r : nat) (n : nat) (P : nat -> Prop) : (term100 n P r) = (term101 r n P).
Proof. exact (eq_refl (term100 n P r)). Qed.
Lemma lem281525 (n : nat) (P : nat -> Prop) : (term102 n P) = (term99 n P).
Proof. exact (fun_ext (fun r : nat => @lem281524 r n P)). Qed.
Lemma lem281526 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem281527 (n : nat) (P : nat -> Prop) : (term103 n P) = (term94 n P).
Proof. exact (MK_COMB (@lem281526) (@lem281525 n P)). Qed.
Lemma lem281528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem281529 (n : nat) (P : nat -> Prop) : (term104 n P) = (term95 n P).
Proof. exact (MK_COMB (@lem281528) (@lem281527 n P)). Qed.
Lemma lem281530 (P : nat -> Prop) (n : nat) : (term69 P n) = (term69 P n).
Proof. exact (eq_refl (term69 P n)). Qed.
Lemma lem281531 (P : nat -> Prop) (n : nat) : (term97 P n) = (term96 P n).
Proof. exact (MK_COMB (@lem281529 n P) (@lem281530 P n)). Qed.
Lemma lem281532 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem281533 (P : nat -> Prop) (n : nat) : (term105 P n) = (term106 P n).
Proof. exact (MK_COMB (@lem281532) (@lem281531 P n)). Qed.
Lemma lem281534 (r : nat) (n : nat) (P : nat -> Prop) : (term100 n P r) = (term101 r n P).
Proof. exact (eq_refl (term100 n P r)). Qed.
Lemma lem281535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem281536 (r : nat) (n : nat) (P : nat -> Prop) : (term107 n P r) = (term108 r n P).
Proof. exact (MK_COMB (@lem281535) (@lem281534 r n P)). Qed.
Lemma lem281537 (P : nat -> Prop) (n : nat) : (term69 P n) = (term69 P n).
Proof. exact (eq_refl (term69 P n)). Qed.
Lemma lem281538 (r : nat) (P : nat -> Prop) (n : nat) : (term109 r P n) = (term110 r P n).
Proof. exact (MK_COMB (@lem281536 r n P) (@lem281537 P n)). Qed.
Lemma lem281539 (P : nat -> Prop) (n : nat) : (term111 P n) = (term112 P n).
Proof. exact (fun_ext (fun r : nat => @lem281538 r P n)). Qed.
Lemma lem281540 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem281541 (P : nat -> Prop) (n : nat) : (term98 P n) = (term113 P n).
Proof. exact (MK_COMB (@lem281540) (@lem281539 P n)). Qed.
Lemma lem281542 (P : nat -> Prop) (n : nat) : ((term97 P n) = (term98 P n)) = ((term96 P n) = (term113 P n)).
Proof. exact (MK_COMB (@lem281533 P n) (@lem281541 P n)). Qed.
Lemma lem281543 (P : nat -> Prop) (n : nat) : (term96 P n) = (term113 P n).
Proof. exact (EQ_MP (@lem281542 P n) (@lem281523 P n)). Qed.
Lemma lem281545 {A : Type'} (P : Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem281546 (P : Prop) (Q : nat -> Prop) : (term116 P Q) = (term117 P Q).
Proof. exact (@lem281545 nat P Q). Qed.
Lemma lem281547 (r : nat) (P : nat -> Prop) (n : nat) : (term118 r P n) = (term119 r P n).
Proof. exact (@lem281546 (term101 r n P) (term68 P n)). Qed.
Lemma lem281548 (P : nat -> Prop) (n : nat) (i : nat) : (term120 P n i) = (term60 P n i).
Proof. exact (eq_refl (term120 P n i)). Qed.
Lemma lem281549 (P : nat -> Prop) (n : nat) : (term121 P n) = (term68 P n).
Proof. exact (fun_ext (fun i : nat => @lem281548 P n i)). Qed.
Lemma lem281550 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem281551 (P : nat -> Prop) (n : nat) : (term122 P n) = (term69 P n).
Proof. exact (MK_COMB (@lem281550) (@lem281549 P n)). Qed.
Lemma lem281552 (r : nat) (n : nat) (P : nat -> Prop) : (term108 r n P) = (term108 r n P).
Proof. exact (eq_refl (term108 r n P)). Qed.
Lemma lem281553 (r : nat) (P : nat -> Prop) (n : nat) : (term118 r P n) = (term110 r P n).
Proof. exact (MK_COMB (@lem281552 r n P) (@lem281551 P n)). Qed.
Lemma lem281554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem281555 (r : nat) (P : nat -> Prop) (n : nat) : (term123 r P n) = (term124 r P n).
Proof. exact (MK_COMB (@lem281554) (@lem281553 r P n)). Qed.
Lemma lem281556 (P : nat -> Prop) (n : nat) (i : nat) : (term120 P n i) = (term60 P n i).
Proof. exact (eq_refl (term120 P n i)). Qed.
Lemma lem281557 (r : nat) (n : nat) (P : nat -> Prop) : (term108 r n P) = (term108 r n P).
Proof. exact (eq_refl (term108 r n P)). Qed.
Lemma lem281558 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) : (term125 r P n i) = (term126 r P n i).
Proof. exact (MK_COMB (@lem281557 r n P) (@lem281556 P n i)). Qed.
Lemma lem281559 (r : nat) (P : nat -> Prop) (n : nat) : (term127 r P n) = (term128 r P n).
Proof. exact (fun_ext (fun i : nat => @lem281558 r P n i)). Qed.
Lemma lem281560 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem281561 (r : nat) (P : nat -> Prop) (n : nat) : (term119 r P n) = (term129 r P n).
Proof. exact (MK_COMB (@lem281560) (@lem281559 r P n)). Qed.
Lemma lem281562 (r : nat) (P : nat -> Prop) (n : nat) : ((term118 r P n) = (term119 r P n)) = ((term110 r P n) = (term129 r P n)).
Proof. exact (MK_COMB (@lem281555 r P n) (@lem281561 r P n)). Qed.
Lemma lem281563 (r : nat) (P : nat -> Prop) (n : nat) : (term110 r P n) = (term129 r P n).
Proof. exact (EQ_MP (@lem281562 r P n) (@lem281547 r P n)). Qed.
Lemma lem281564 (P : nat -> Prop) (n : nat) : (term112 P n) = (term130 P n).
Proof. exact (fun_ext (fun r : nat => @lem281563 r P n)). Qed.
Lemma lem281565 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem281566 (P : nat -> Prop) (n : nat) : (term113 P n) = (term131 P n).
Proof. exact (MK_COMB (@lem281565) (@lem281564 P n)). Qed.
Lemma lem281567 (P : nat -> Prop) (n : nat) : (term96 P n) = (term131 P n).
Proof. exact (TRANS (@lem281543 P n) (@lem281566 P n)). Qed.
Lemma lem281568 (P : nat -> Prop) (n : nat) : (term73 P n) = (term131 P n).
Proof. exact (TRANS (@lem281519 P n) (@lem281567 P n)). Qed.
Lemma lem281569 (P : nat -> Prop) : (term80 P) = (term132 P).
Proof. exact (fun_ext (fun n : nat => @lem281568 P n)). Qed.
Lemma lem281570 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem281571 (P : nat -> Prop) : (term81 P) = (term133 P).
Proof. exact (MK_COMB (@lem281570) (@lem281569 P)). Qed.
Lemma lem281572 : term88 = term134.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem281571 P)). Qed.
Lemma lem281573 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem281575 : term89 = term135.
Proof. exact (MK_COMB (@lem281573) (@lem281572)). Qed.
Lemma lem281576 : term32 = term135.
Proof. exact (TRANS (@lem281378) (@lem281575)). Qed.
Lemma lem281577 (h1 : term32) : term135.
Proof. exact (EQ_MP (@lem281576) (@lem281318 h1)). Qed.
Lemma lem281581 (m : nat) (n : nat) : (term136 m n) = (Peano.lt m n).
Proof. exact (@lem16933 (Peano.lt m n)). Qed.
Lemma lem281583 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem281584 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem281585 (m : nat) (n : nat) : (term137 m n) = (term138 m n).
Proof. exact (MK_COMB (@lem281584) (@lem281581 m n)). Qed.
Lemma lem281586 (n : nat) (m : nat) : (term139 n m) = (term140 n m).
Proof. exact (MK_COMB (@lem281585 m n) (@lem281583 n m)). Qed.
Lemma lem281591 (n : nat) (m : nat) : (term141 n m) = (term141 n m).
Proof. exact (eq_refl (term141 n m)). Qed.
Lemma lem281592 (n : nat) (m : nat) : (term142 n m) = (term143 n m).
Proof. exact (MK_COMB (@lem281591 n m) (@lem281586 n m)). Qed.
Lemma lem281593 (n : nat) (m : nat) : ((term42 m n) = (Peano.le n m)) = (term142 n m).
Proof. exact (@lem17784 (term42 m n) (Peano.le n m)). Qed.
Lemma lem281594 (n : nat) (m : nat) : ((term42 m n) = (Peano.le n m)) = (term143 n m).
Proof. exact (TRANS (@lem281593 n m) (@lem281592 n m)). Qed.
Lemma lem281595 (m : nat) : (term43 m) = (term144 m).
Proof. exact (fun_ext (fun n : nat => @lem281594 n m)). Qed.
Lemma lem281596 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281597 (m : nat) : (term44 m) = (term145 m).
Proof. exact (MK_COMB (@lem281596) (@lem281595 m)). Qed.
Lemma lem281598 : term45 = term146.
Proof. exact (fun_ext (fun m : nat => @lem281597 m)). Qed.
Lemma lem281599 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281600 : term39 = term147.
Proof. exact (MK_COMB (@lem281599) (@lem281598)). Qed.
Lemma lem281606 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem281607 (P : nat -> Prop) (Q : nat -> Prop) : (term150 P Q) = (term151 P Q).
Proof. exact (@lem281606 nat P Q). Qed.
Lemma lem281608 (m : nat) : (term152 m) = (term153 m).
Proof. exact (@lem281607 (term154 m) (term155 m)). Qed.
Lemma lem281609 (n : nat) (m : nat) : (term156 m n) = (term157 n m).
Proof. exact (eq_refl (term156 m n)). Qed.
Lemma lem281610 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem281611 (n : nat) (m : nat) : (term158 m n) = (term141 n m).
Proof. exact (MK_COMB (@lem281610) (@lem281609 n m)). Qed.
Lemma lem281612 (n : nat) (m : nat) : (term159 m n) = (term140 n m).
Proof. exact (eq_refl (term159 m n)). Qed.
Lemma lem281613 (n : nat) (m : nat) : (term160 m n) = (term143 n m).
Proof. exact (MK_COMB (@lem281611 n m) (@lem281612 n m)). Qed.
Lemma lem281614 (m : nat) : (term161 m) = (term144 m).
Proof. exact (fun_ext (fun n : nat => @lem281613 n m)). Qed.
Lemma lem281615 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281616 (m : nat) : (term152 m) = (term145 m).
Proof. exact (MK_COMB (@lem281615) (@lem281614 m)). Qed.
Lemma lem281617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem281618 (m : nat) : (term162 m) = (term163 m).
Proof. exact (MK_COMB (@lem281617) (@lem281616 m)). Qed.
Lemma lem281619 (n : nat) (m : nat) : (term156 m n) = (term157 n m).
Proof. exact (eq_refl (term156 m n)). Qed.
Lemma lem281620 (m : nat) : (term164 m) = (term154 m).
Proof. exact (fun_ext (fun n : nat => @lem281619 n m)). Qed.
Lemma lem281621 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281622 (m : nat) : (term165 m) = (term166 m).
Proof. exact (MK_COMB (@lem281621) (@lem281620 m)). Qed.
Lemma lem281623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem281624 (m : nat) : (term167 m) = (term168 m).
Proof. exact (MK_COMB (@lem281623) (@lem281622 m)). Qed.
Lemma lem281625 (n : nat) (m : nat) : (term159 m n) = (term140 n m).
Proof. exact (eq_refl (term159 m n)). Qed.
Lemma lem281626 (m : nat) : (term169 m) = (term155 m).
Proof. exact (fun_ext (fun n : nat => @lem281625 n m)). Qed.
Lemma lem281627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281628 (m : nat) : (term170 m) = (term171 m).
Proof. exact (MK_COMB (@lem281627) (@lem281626 m)). Qed.
Lemma lem281629 (m : nat) : (term153 m) = (term172 m).
Proof. exact (MK_COMB (@lem281624 m) (@lem281628 m)). Qed.
Lemma lem281630 (m : nat) : ((term152 m) = (term153 m)) = ((term145 m) = (term172 m)).
Proof. exact (MK_COMB (@lem281618 m) (@lem281629 m)). Qed.
Lemma lem281631 (m : nat) : (term145 m) = (term172 m).
Proof. exact (EQ_MP (@lem281630 m) (@lem281608 m)). Qed.
Lemma lem281728 : term146 = term173.
Proof. exact (fun_ext (fun m : nat => @lem281631 m)). Qed.
Lemma lem281729 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281730 : term147 = term174.
Proof. exact (MK_COMB (@lem281729) (@lem281728)). Qed.
Lemma lem281732 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem281733 (P : nat -> Prop) (Q : nat -> Prop) : (term150 P Q) = (term151 P Q).
Proof. exact (@lem281732 nat P Q). Qed.
Lemma lem281734 : term175 = term176.
Proof. exact (@lem281733 term177 term178). Qed.
Lemma lem281735 (m : nat) : (term179 m) = (term166 m).
Proof. exact (eq_refl (term179 m)). Qed.
Lemma lem281736 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem281737 (m : nat) : (term180 m) = (term168 m).
Proof. exact (MK_COMB (@lem281736) (@lem281735 m)). Qed.
Lemma lem281738 (m : nat) : (term181 m) = (term171 m).
Proof. exact (eq_refl (term181 m)). Qed.
Lemma lem281739 (m : nat) : (term182 m) = (term172 m).
Proof. exact (MK_COMB (@lem281737 m) (@lem281738 m)). Qed.
Lemma lem281740 : term183 = term173.
Proof. exact (fun_ext (fun m : nat => @lem281739 m)). Qed.
Lemma lem281741 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281742 : term175 = term174.
Proof. exact (MK_COMB (@lem281741) (@lem281740)). Qed.
Lemma lem281743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem281744 : term184 = term185.
Proof. exact (MK_COMB (@lem281743) (@lem281742)). Qed.
Lemma lem281745 (m : nat) : (term179 m) = (term166 m).
Proof. exact (eq_refl (term179 m)). Qed.
Lemma lem281746 : term186 = term177.
Proof. exact (fun_ext (fun m : nat => @lem281745 m)). Qed.
Lemma lem281747 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281748 : term187 = term188.
Proof. exact (MK_COMB (@lem281747) (@lem281746)). Qed.
Lemma lem281749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem281750 : term189 = term190.
Proof. exact (MK_COMB (@lem281749) (@lem281748)). Qed.
Lemma lem281751 (m : nat) : (term181 m) = (term171 m).
Proof. exact (eq_refl (term181 m)). Qed.
Lemma lem281752 : term191 = term178.
Proof. exact (fun_ext (fun m : nat => @lem281751 m)). Qed.
Lemma lem281753 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281754 : term192 = term193.
Proof. exact (MK_COMB (@lem281753) (@lem281752)). Qed.
Lemma lem281755 : term176 = term194.
Proof. exact (MK_COMB (@lem281750) (@lem281754)). Qed.
Lemma lem281756 : (term175 = term176) = (term174 = term194).
Proof. exact (MK_COMB (@lem281744) (@lem281755)). Qed.
Lemma lem281757 : term174 = term194.
Proof. exact (EQ_MP (@lem281756) (@lem281734)). Qed.
Lemma lem281864 : term147 = term194.
Proof. exact (TRANS (@lem281730) (@lem281757)). Qed.
Lemma lem281865 : term39 = term194.
Proof. exact (TRANS (@lem281600) (@lem281864)). Qed.
Lemma lem281866 (h1 : term39) : term194.
Proof. exact (EQ_MP (@lem281865) (@lem281319 h1)). Qed.
Lemma lem281867 (P : nat -> Prop) (h1 : term133 P) : term133 P.
Proof. exact (h1). Qed.
Lemma lem281868 (P : nat -> Prop) (n : nat) (h1 : term131 P n) : term131 P n.
Proof. exact (h1). Qed.
Lemma lem281869 (r : nat) (P : nat -> Prop) (n : nat) (h1 : term129 r P n) : term129 r P n.
Proof. exact (h1). Qed.
Lemma lem281870 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term126 r P n i.
Proof. exact (h1). Qed.
Lemma lem281883 (n : nat) (m : nat) : (term140 n m) = (term140 n m).
Proof. exact (eq_refl (term140 n m)). Qed.
Lemma lem281884 (m : nat) : (term155 m) = (term155 m).
Proof. exact (fun_ext (fun n : nat => @lem281883 n m)). Qed.
Lemma lem281885 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281886 (m : nat) : (term171 m) = (term171 m).
Proof. exact (MK_COMB (@lem281885) (@lem281884 m)). Qed.
Lemma lem281887 : term178 = term178.
Proof. exact (fun_ext (fun m : nat => @lem281886 m)). Qed.
Lemma lem281888 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281889 : term193 = term193.
Proof. exact (MK_COMB (@lem281888) (@lem281887)). Qed.
Lemma lem281906 (n : nat) (m : nat) : (term157 n m) = (term157 n m).
Proof. exact (eq_refl (term157 n m)). Qed.
Lemma lem281907 (m : nat) : (term154 m) = (term154 m).
Proof. exact (fun_ext (fun n : nat => @lem281906 n m)). Qed.
Lemma lem281908 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281909 (m : nat) : (term166 m) = (term166 m).
Proof. exact (MK_COMB (@lem281908) (@lem281907 m)). Qed.
Lemma lem281910 : term177 = term177.
Proof. exact (fun_ext (fun m : nat => @lem281909 m)). Qed.
Lemma lem281911 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281912 : term188 = term188.
Proof. exact (MK_COMB (@lem281911) (@lem281910)). Qed.
Lemma lem281913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem281914 : term190 = term190.
Proof. exact (MK_COMB (@lem281913) (@lem281912)). Qed.
Lemma lem281915 : term194 = term194.
Proof. exact (MK_COMB (@lem281914) (@lem281889)). Qed.
Lemma lem281916 (h1 : term39) : term194.
Proof. exact (EQ_MP (@lem281915) (@lem281866 h1)). Qed.
Lemma lem281929 (P : nat -> Prop) (n : nat) (i : nat) : (term60 P n i) = (term60 P n i).
Proof. exact (eq_refl (term60 P n i)). Qed.
Lemma lem281944 (n : nat) (P : nat -> Prop) (m : nat) : (term54 n P m) = (term54 n P m).
Proof. exact (eq_refl (term54 n P m)). Qed.
Lemma lem281945 (n : nat) (P : nat -> Prop) : (term56 n P) = (term56 n P).
Proof. exact (fun_ext (fun m : nat => @lem281944 n P m)). Qed.
Lemma lem281946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281947 (n : nat) (P : nat -> Prop) : (term57 n P) = (term57 n P).
Proof. exact (MK_COMB (@lem281946) (@lem281945 n P)). Qed.
Lemma lem281952 (P : nat -> Prop) (r : nat) : (term195 P r) = (term195 P r).
Proof. exact (eq_refl (term195 P r)). Qed.
Lemma lem281953 (r : nat) (n : nat) (P : nat -> Prop) : (term101 r n P) = (term101 r n P).
Proof. exact (MK_COMB (@lem281952 P r) (@lem281947 n P)). Qed.
Lemma lem281954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem281955 (r : nat) (n : nat) (P : nat -> Prop) : (term108 r n P) = (term108 r n P).
Proof. exact (MK_COMB (@lem281954) (@lem281953 r n P)). Qed.
Lemma lem281956 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) : (term126 r P n i) = (term126 r P n i).
Proof. exact (MK_COMB (@lem281955 r n P) (@lem281929 P n i)). Qed.
Lemma lem281957 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term126 r P n i.
Proof. exact (EQ_MP (@lem281956 r P n i) (@lem281870 r P n i h1)). Qed.
Lemma lem281958 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term60 P n i.
Proof. exact (proj2 (@lem281957 r P n i h1)). Qed.
Lemma lem281959 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term101 r n P.
Proof. exact (proj1 (@lem281957 r P n i h1)). Qed.
Lemma lem281962 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term57 n P.
Proof. exact (proj2 (@lem281959 r P n i h1)). Qed.
Lemma lem281964 (h1 : term39) : term193.
Proof. exact (proj2 (@lem281916 h1)). Qed.
Lemma lem281985 (n : nat) (P : nat -> Prop) (m : nat) : (term54 n P m) = (term54 n P m).
Proof. exact (eq_refl (term54 n P m)). Qed.
Lemma lem281986 (n : nat) (P : nat -> Prop) : (term56 n P) = (term56 n P).
Proof. exact (fun_ext (fun m : nat => @lem281985 n P m)). Qed.
Lemma lem281987 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem281989 (n : nat) (P : nat -> Prop) : (term57 n P) = (term57 n P).
Proof. exact (MK_COMB (@lem281987) (@lem281986 n P)). Qed.
Lemma lem281990 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term57 n P.
Proof. exact (EQ_MP (@lem281989 n P) (@lem281962 r P n i h1)). Qed.
Lemma lem282014 (n : nat) (m : nat) : (term140 n m) = (term140 n m).
Proof. exact (eq_refl (term140 n m)). Qed.
Lemma lem282015 (m : nat) : (term155 m) = (term155 m).
Proof. exact (fun_ext (fun n : nat => @lem282014 n m)). Qed.
Lemma lem282016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282017 (m : nat) : (term171 m) = (term171 m).
Proof. exact (MK_COMB (@lem282016) (@lem282015 m)). Qed.
Lemma lem282018 : term178 = term178.
Proof. exact (fun_ext (fun m : nat => @lem282017 m)). Qed.
Lemma lem282019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem282021 : term193 = term193.
Proof. exact (MK_COMB (@lem282019) (@lem282018)). Qed.
Lemma lem282022 (h1 : term39) : term193.
Proof. exact (EQ_MP (@lem282021) (@lem281964 h1)). Qed.
Lemma lem282023 (_6457 : nat) (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term196 n P _6457.
Proof. exact (@lem281990 r P n i h1 _6457). Qed.
Lemma lem282024 (n : nat) (P : nat -> Prop) (_6457 : nat) : (term196 n P _6457) = (term54 n P _6457).
Proof. exact (eq_refl (term196 n P _6457)). Qed.
Lemma lem282032 (_6460 : nat) (h1 : term39) : term181 _6460.
Proof. exact (@lem282022 h1 _6460). Qed.
Lemma lem282033 (_6460 : nat) : (term181 _6460) = (term171 _6460).
Proof. exact (eq_refl (term181 _6460)). Qed.
Lemma lem282034 (_6460 : nat) (h1 : term39) : term171 _6460.
Proof. exact (EQ_MP (@lem282033 _6460) (@lem282032 _6460 h1)). Qed.
Lemma lem282035 (_6460 : nat) (_6461 : nat) (h1 : term39) : term159 _6460 _6461.
Proof. exact (@lem282034 _6460 h1 _6461). Qed.
Lemma lem282036 (_6461 : nat) (_6460 : nat) : (term159 _6460 _6461) = (term140 _6461 _6460).
Proof. exact (eq_refl (term159 _6460 _6461)). Qed.
Lemma lem282041 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term197 n i.
Proof. exact (proj2 (@lem281958 r P n i h1)). Qed.
Lemma lem282049 (_6457 : nat) (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term54 n P _6457.
Proof. exact (EQ_MP (@lem282024 n P _6457) (@lem282023 _6457 r P n i h1)). Qed.
Lemma lem282061 (_6461 : nat) (_6460 : nat) (h1 : term39) : term140 _6461 _6460.
Proof. exact (EQ_MP (@lem282036 _6461 _6460) (@lem282035 _6460 _6461 h1)). Qed.
Lemma lem282063 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : P i.
Proof. exact (proj1 (@lem281958 r P n i h1)). Qed.
Lemma lem282064 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term198 P i.
Proof. exact (fun h0 : term55 P i => @lem282063 r P n i h1). Qed.
Lemma lem282066 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem282067 (P : nat -> Prop) (i : nat) : (term198 P i) = (P i).
Proof. exact (@lem282066 (P i)). Qed.
Lemma lem282068 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : P i.
Proof. exact (EQ_MP (@lem282067 P i) (@lem282064 r P n i h1)). Qed.
Lemma lem282070 (b : Prop) (a : Prop) : (a \/ b) = (term200 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem282071 (P : nat -> Prop) (_6457 : nat) (n : nat) : (term54 n P _6457) = (term201 P _6457 n).
Proof. exact (@lem282070 (term55 P _6457) (term42 _6457 n)). Qed.
Lemma lem282073 (a : Prop) : (term202 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem282074 (P : nat -> Prop) (_6457 : nat) : (term203 P _6457) = (P _6457).
Proof. exact (@lem282073 (P _6457)). Qed.
Lemma lem282075 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem282076 (P : nat -> Prop) (_6457 : nat) : (term204 P _6457) = (term205 P _6457).
Proof. exact (MK_COMB (@lem282075) (@lem282074 P _6457)). Qed.
Lemma lem282077 (_6457 : nat) (n : nat) : (term42 _6457 n) = (term42 _6457 n).
Proof. exact (eq_refl (term42 _6457 n)). Qed.
Lemma lem282078 (P : nat -> Prop) (_6457 : nat) (n : nat) : (term201 P _6457 n) = (term206 P _6457 n).
Proof. exact (MK_COMB (@lem282076 P _6457) (@lem282077 _6457 n)). Qed.
Lemma lem282079 (P : nat -> Prop) (_6457 : nat) (n : nat) : (term54 n P _6457) = (term206 P _6457 n).
Proof. exact (TRANS (@lem282071 P _6457 n) (@lem282078 P _6457 n)). Qed.
Lemma lem282082 (_6457 : nat) (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term206 P _6457 n.
Proof. exact (EQ_MP (@lem282079 P _6457 n) (@lem282049 _6457 r P n i h1)). Qed.
Lemma lem282083 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term206 P i n.
Proof. exact (@lem282082 i r P n i h1). Qed.
Lemma lem282086 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term42 i n.
Proof. exact (@lem282083 r P n i h1 (@lem282068 r P n i h1)). Qed.
Lemma lem282087 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term207 i n.
Proof. exact (fun h0 : Peano.lt i n => @lem282086 r P n i h1). Qed.
Lemma lem282089 (p : Prop) : (term208 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem282090 (i : nat) (n : nat) : (term207 i n) = (term42 i n).
Proof. exact (@lem282089 (Peano.lt i n)). Qed.
Lemma lem282091 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term42 i n.
Proof. exact (EQ_MP (@lem282090 i n) (@lem282087 r P n i h1)). Qed.
Lemma lem282102 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem282103 (_6461 : nat) (_6460 : nat) : (term209 _6460 _6461) = (term140 _6461 _6460).
Proof. exact (@lem282102 (Peano.lt _6460 _6461) (Peano.le _6461 _6460)). Qed.
Lemma lem282109 (_6461 : nat) (_6460 : nat) : (term210 _6461 _6460) = (term210 _6461 _6460).
Proof. exact (eq_refl (term210 _6461 _6460)). Qed.
Lemma lem282110 (_6461 : nat) (_6460 : nat) : ((term140 _6461 _6460) = (term209 _6460 _6461)) = ((term140 _6461 _6460) = (term140 _6461 _6460)).
Proof. exact (MK_COMB (@lem282109 _6461 _6460) (@lem282103 _6461 _6460)). Qed.
Lemma lem282112 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem282113 (x : Prop) : (x = x) = True.
Proof. exact (@lem282112 Prop x). Qed.
Lemma lem282114 (_6461 : nat) (_6460 : nat) : ((term140 _6461 _6460) = (term140 _6461 _6460)) = True.
Proof. exact (@lem282113 (term140 _6461 _6460)). Qed.
Lemma lem282115 (_6460 : nat) (_6461 : nat) : ((term140 _6461 _6460) = (term209 _6460 _6461)) = True.
Proof. exact (TRANS (@lem282110 _6461 _6460) (@lem282114 _6461 _6460)). Qed.
Lemma lem282116 (_6460 : nat) (_6461 : nat) : True = ((term140 _6461 _6460) = (term209 _6460 _6461)).
Proof. exact (SYM (@lem282115 _6460 _6461)). Qed.
Lemma lem282117 (_6460 : nat) (_6461 : nat) : (term140 _6461 _6460) = (term209 _6460 _6461).
Proof. exact (EQ_MP (@lem282116 _6460 _6461) (@lem0)). Qed.
Lemma lem282118 (_6460 : nat) (_6461 : nat) (h1 : term39) : term209 _6460 _6461.
Proof. exact (EQ_MP (@lem282117 _6460 _6461) (@lem282061 _6461 _6460 h1)). Qed.
Lemma lem282120 (b : Prop) (a : Prop) : (a \/ b) = (term200 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem282123 (_6461 : nat) (_6460 : nat) : (term209 _6460 _6461) = (term211 _6461 _6460).
Proof. exact (@lem282120 (Peano.lt _6460 _6461) (Peano.le _6461 _6460)). Qed.
Lemma lem282126 (_6461 : nat) (_6460 : nat) (h1 : term39) : term211 _6461 _6460.
Proof. exact (EQ_MP (@lem282123 _6461 _6460) (@lem282118 _6460 _6461 h1)). Qed.
Lemma lem282127 (n : nat) (i : nat) (h1 : term39) : term211 n i.
Proof. exact (@lem282126 n i h1). Qed.
Lemma lem282130 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term39) (h2 : term126 r P n i) : Peano.le n i.
Proof. exact (@lem282127 n i h1 (@lem282091 r P n i h2)). Qed.
Lemma lem282131 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term39) (h2 : term126 r P n i) : term212 n i.
Proof. exact (fun h0 : term197 n i => @lem282130 r P n i h1 h2). Qed.
Lemma lem282133 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem282134 (n : nat) (i : nat) : (term212 n i) = (Peano.le n i).
Proof. exact (@lem282133 (Peano.le n i)). Qed.
Lemma lem282135 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term39) (h2 : term126 r P n i) : Peano.le n i.
Proof. exact (EQ_MP (@lem282134 n i) (@lem282131 r P n i h1 h2)). Qed.
Lemma lem282138 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem282140 (n : nat) (i : nat) : (term197 n i) = (term213 n i).
Proof. exact (@lem282138 (Peano.le n i)). Qed.
Lemma lem282143 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term126 r P n i) : term213 n i.
Proof. exact (EQ_MP (@lem282140 n i) (@lem282041 r P n i h1)). Qed.
Lemma lem282146 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term39) (h2 : term126 r P n i) : False.
Proof. exact (@lem282143 r P n i h2 (@lem282135 r P n i h1 h2)). Qed.
Lemma lem282147 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term39) (h2 : term126 r P n i) : term214.
Proof. exact (fun h0 : ~ False => @lem282146 r P n i h1 h2). Qed.
Lemma lem282149 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem282150 : term214 = False.
Proof. exact (@lem282149 False). Qed.
Lemma lem282151 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term39) (h2 : term126 r P n i) : False.
Proof. exact (EQ_MP (@lem282150) (@lem282147 r P n i h1 h2)). Qed.
Lemma lem282152 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term39) (h2 : term126 r P n i) : (term126 r P n i) = False.
Proof. exact (prop_ext (fun h3 : term126 r P n i => @lem282151 r P n i h1 h2) (fun h3 : False => @lem281957 r P n i h2)). Qed.
Lemma lem282153 (r : nat) (P : nat -> Prop) (n : nat) (i : nat) (h1 : term39) (h2 : term126 r P n i) : False.
Proof. exact (EQ_MP (@lem282152 r P n i h1 h2) (@lem281957 r P n i h2)). Qed.
Lemma lem282154 (r : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term129 r P n) : False.
Proof. exact (ex_elim (@lem281869 r P n h2) (fun i : nat => fun h0 : term128 r P n i => @lem282153 r P n i h1 h0)). Qed.
Lemma lem282155 (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term131 P n) : False.
Proof. exact (ex_elim (@lem281868 P n h2) (fun r : nat => fun h0 : term130 P n r => @lem282154 r P n h1 h0)). Qed.
Lemma lem282156 (P : nat -> Prop) (h1 : term39) (h2 : term133 P) : False.
Proof. exact (ex_elim (@lem281867 P h2) (fun n : nat => fun h0 : term132 P n => @lem282155 P n h1 h0)). Qed.
Lemma lem282157 (h1 : term39) (h2 : term32) : False.
Proof. exact (ex_elim (@lem281577 h2) (fun P : nat -> Prop => fun h0 : term134 P => @lem282156 P h1 h0)). Qed.
Lemma lem282158 (h1 : term32) : term37.
Proof. exact (fun h0 : term39 => @lem282157 h0 h1). Qed.
Lemma lem282159 : term37 = term38.
Proof. exact (@lem69 term39). Qed.
Lemma lem282160 (h1 : term32) : term38.
Proof. exact (EQ_MP (@lem282159) (@lem282158 h1)). Qed.
Lemma lem282161 : term41.
Proof. exact (fun h0 : term32 => @lem282160 h0). Qed.
Lemma lem282162 : term33.
Proof. exact (EQ_MP (@lem281317) (@lem282161)). Qed.
Lemma lem282164 : term33.
Proof. exact (@lem281158 (@lem282162)). Qed.
Lemma lem282165 (h1 : term32) : term37.
Proof. exact (@lem282164 (@lem281143 h1)). Qed.
Lemma lem282166 (h1 : term32) : False.
Proof. exact (@lem282165 h1 (@lem98377)). Qed.
Lemma lem282167 (h1 : term32) : term32 = False.
Proof. exact (prop_ext (fun h2 : term32 => @lem282166 h1) (fun h2 : False => @lem281143 h1)). Qed.
Lemma lem282168 (h1 : term32) : False.
Proof. exact (EQ_MP (@lem282167 h1) (@lem281143 h1)). Qed.
Lemma lem282169 : term31.
Proof. exact (fun h0 : term32 => @lem282168 h0). Qed.
Lemma lem282170 : term29.
Proof. exact (EQ_MP (@lem281142) (@lem282169)). Qed.
Lemma lem282171 : term28.
Proof. exact (EQ_MP (@lem281138) (@lem282170)). Qed.
