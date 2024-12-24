Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MINIMAL_UNIQUE_term_abbrevs.
Require Import LT_CASES_spec.
Require Import SELECT_UNIQUE_spec.
Require Import minimal_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem273187 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem273188 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term1 A P.
Proof. exact (@lem273187 A h1 P). Qed.
Lemma lem273189 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem273190 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem273189 A P) (@lem273188 A P h1)). Qed.
Lemma lem273191 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term3 A P x.
Proof. exact (@lem273190 A P h1 x). Qed.
Lemma lem273192 {A : Type'} (P : A -> Prop) (x : A) : (term3 A P x) = (term4 A P x).
Proof. exact (eq_refl (term3 A P x)). Qed.
Lemma lem273193 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (EQ_MP (@lem273192 A P x) (@lem273191 A P x h1)). Qed.
Lemma lem273194 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term5 A P x.
Proof. exact (h1). Qed.
Lemma lem273195 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem273193 A P x h2 (@lem273194 A P x h1)). Qed.
Lemma lem273196 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term6 A P x.
Proof. exact (fun h0 : term0 A => @lem273195 A P x h1 h0). Qed.
Lemma lem273197 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem273198 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem273196 A P x h1 (@lem273197 A h2)). Qed.
Lemma lem273199 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (fun h0 : term5 A P x => @lem273198 A P x h0 h1). Qed.
Lemma lem273200 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (fun x : A => @lem273199 A P x h1). Qed.
Lemma lem273201 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : A -> Prop => @lem273200 A P h1). Qed.
Lemma lem273202 {A : Type'} : term7 A.
Proof. exact (fun h0 : term0 A => @lem273201 A h0). Qed.
Lemma lem273203 {A : Type'} : term0 A.
Proof. exact (@lem273202 A (@lem9522 A)). Qed.
Lemma lem273204 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (@lem273203 A P). Qed.
Lemma lem273205 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem273206 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (EQ_MP (@lem273205 A P) (@lem273204 A P)). Qed.
Lemma lem273207 {A : Type'} (P : A -> Prop) (x : A) : term3 A P x.
Proof. exact (@lem273206 A P x). Qed.
Lemma lem273208 {A : Type'} (P : A -> Prop) (x : A) : (term3 A P x) = (term4 A P x).
Proof. exact (eq_refl (term3 A P x)). Qed.
Lemma lem273210 (P : nat -> Prop) : term8 P.
Proof. exact (@lem273060 P). Qed.
Lemma lem273211 (P : nat -> Prop) : (term8 P) = ((minimal P) = (term9 P)).
Proof. exact (eq_refl (term8 P)). Qed.
Lemma lem273213 (n : nat) (P : nat -> Prop) (h1 : term10 n P) : term10 n P.
Proof. exact (h1). Qed.
Lemma lem273214 (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term11 n P.
Proof. exact (h1). Qed.
Lemma lem273215 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem273219 (P : nat -> Prop) : (minimal P) = (term9 P).
Proof. exact (EQ_MP (@lem273211 P) (@lem273210 P)). Qed.
Lemma lem273228 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem273229 (P : nat -> Prop) : (term12 P) = (term13 P).
Proof. exact (MK_COMB (@lem273228) (@lem273219 P)). Qed.
Lemma lem273230 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem273231 (P : nat -> Prop) (n : nat) : ((minimal P) = n) = ((term9 P) = n).
Proof. exact (MK_COMB (@lem273229 P) (@lem273230 n)). Qed.
Lemma lem273234 (P : nat -> Prop) (n : nat) : ((term9 P) = n) = ((minimal P) = n).
Proof. exact (SYM (@lem273231 P n)). Qed.
Lemma lem273236 {A : Type'} (P : A -> Prop) (x : A) : term4 A P x.
Proof. exact (EQ_MP (@lem273208 A P x) (@lem273207 A P x)). Qed.
Lemma lem273237 (P : nat -> Prop) (x : nat) : term14 P x.
Proof. exact (@lem273236 nat P x). Qed.
Lemma lem273238 (P : nat -> Prop) (n : nat) : term15 P n.
Proof. exact (@lem273237 (term16 P) n). Qed.
Lemma lem273240 (p : Prop) : p = (term17 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem273241 (P : nat -> Prop) (n : nat) : (term18 P n) = (term19 P n).
Proof. exact (@lem273240 (term18 P n)). Qed.
Lemma lem273242 (P : nat -> Prop) (n : nat) : (term19 P n) = (term18 P n).
Proof. exact (SYM (@lem273241 P n)). Qed.
Lemma lem273243 (P : nat -> Prop) (n : nat) (h1 : term20 P n) : term20 P n.
Proof. exact (h1). Qed.
Lemma lem273246 (P : nat -> Prop) (n : nat) (h1 : term21 P n) : term21 P n.
Proof. exact (h1). Qed.
Lemma lem273247 (P : nat -> Prop) (n : nat) : term22 P n.
Proof. exact (fun h0 : term21 P n => @lem273246 P n h0). Qed.
Lemma lem273248 (P : nat -> Prop) (n : nat) (h1 : term22 P n) : term22 P n.
Proof. exact (h1). Qed.
Lemma lem273249 (P : nat -> Prop) (n : nat) (h1 : term21 P n) : term21 P n.
Proof. exact (h1). Qed.
Lemma lem273250 (P : nat -> Prop) (n : nat) (h1 : term21 P n) (h2 : term22 P n) : term21 P n.
Proof. exact (@lem273248 P n h2 (@lem273249 P n h1)). Qed.
Lemma lem273251 (P : nat -> Prop) (n : nat) (h1 : term21 P n) : term23 P n.
Proof. exact (fun h0 : term22 P n => @lem273250 P n h1 h0). Qed.
Lemma lem273252 (P : nat -> Prop) (n : nat) (h1 : term22 P n) : term22 P n.
Proof. exact (h1). Qed.
Lemma lem273253 (P : nat -> Prop) (n : nat) (h1 : term21 P n) (h2 : term22 P n) : term21 P n.
Proof. exact (@lem273251 P n h1 (@lem273252 P n h2)). Qed.
Lemma lem273254 (P : nat -> Prop) (n : nat) (h1 : term22 P n) : term22 P n.
Proof. exact (fun h0 : term21 P n => @lem273253 P n h0 h1). Qed.
Lemma lem273255 (P : nat -> Prop) (n : nat) : term24 P n.
Proof. exact (fun h0 : term22 P n => @lem273254 P n h0). Qed.
Lemma lem273258 (P : nat -> Prop) (n : nat) : term22 P n.
Proof. exact (@lem273255 P n (@lem273247 P n)). Qed.
Lemma lem273292 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem273293 : term25 = term26.
Proof. exact (@lem273292 term27). Qed.
Lemma lem273350 (P : nat -> Prop) (n : nat) : (term28 P n) = (term28 P n).
Proof. exact (eq_refl (term28 P n)). Qed.
Lemma lem273351 (P : nat -> Prop) (n : nat) : (term29 P n) = (term30 P n).
Proof. exact (MK_COMB (@lem273350 P n) (@lem273293)). Qed.
Lemma lem273354 (n : nat) (P : nat -> Prop) : (term31 n P) = (term31 n P).
Proof. exact (eq_refl (term31 n P)). Qed.
Lemma lem273355 (P : nat -> Prop) (n : nat) : (term32 P n) = (term33 P n).
Proof. exact (MK_COMB (@lem273354 n P) (@lem273351 P n)). Qed.
Lemma lem273358 (P : nat -> Prop) (n : nat) : (term34 P n) = (term34 P n).
Proof. exact (eq_refl (term34 P n)). Qed.
Lemma lem273359 (P : nat -> Prop) (n : nat) : (term21 P n) = (term35 P n).
Proof. exact (MK_COMB (@lem273358 P n) (@lem273355 P n)). Qed.
Lemma lem273362 (n : nat) : (term36 n) = (term37 n).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem273359 P n)). Qed.
Lemma lem273363 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem273364 (n : nat) : (term38 n) = (term39 n).
Proof. exact (MK_COMB (@lem273363) (@lem273362 n)). Qed.
Lemma lem273369 : term40 = term41.
Proof. exact (fun_ext (fun n : nat => @lem273364 n)). Qed.
Lemma lem273370 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273371 : term42 = term43.
Proof. exact (MK_COMB (@lem273370) (@lem273369)). Qed.
Lemma lem273376 (y : nat) (P : nat -> Prop) : (term44 P y) = (term10 y P).
Proof. exact (eq_refl (term44 P y)). Qed.
Lemma lem273377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem273378 (y : nat) (P : nat -> Prop) : (term45 P y) = (term46 y P).
Proof. exact (MK_COMB (@lem273377) (@lem273376 y P)). Qed.
Lemma lem273379 (y : nat) (n : nat) : (y = n) = (y = n).
Proof. exact (eq_refl (y = n)). Qed.
Lemma lem273380 (P : nat -> Prop) (y : nat) (n : nat) : ((term44 P y) = (y = n)) = ((term10 y P) = (y = n)).
Proof. exact (MK_COMB (@lem273378 y P) (@lem273379 y n)). Qed.
Lemma lem273381 (P : nat -> Prop) (n : nat) : (term47 P n) = (term48 P n).
Proof. exact (fun_ext (fun y : nat => @lem273380 P y n)). Qed.
Lemma lem273382 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273383 (P : nat -> Prop) (n : nat) : (term18 P n) = (term49 P n).
Proof. exact (MK_COMB (@lem273382) (@lem273381 P n)). Qed.
Lemma lem273384 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem273385 (P : nat -> Prop) (n : nat) : (term20 P n) = (term50 P n).
Proof. exact (MK_COMB (@lem273384) (@lem273383 P n)). Qed.
Lemma lem273386 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem273387 (P : nat -> Prop) (n : nat) : (term28 P n) = (term51 P n).
Proof. exact (MK_COMB (@lem273386) (@lem273385 P n)). Qed.
Lemma lem273388 : term26 = term26.
Proof. exact (eq_refl term26). Qed.
Lemma lem273389 (P : nat -> Prop) (n : nat) : (term30 P n) = (term52 P n).
Proof. exact (MK_COMB (@lem273387 P n) (@lem273388)). Qed.
Lemma lem273390 (n : nat) (P : nat -> Prop) : (term31 n P) = (term31 n P).
Proof. exact (eq_refl (term31 n P)). Qed.
Lemma lem273391 (P : nat -> Prop) (n : nat) : (term33 P n) = (term53 P n).
Proof. exact (MK_COMB (@lem273390 n P) (@lem273389 P n)). Qed.
Lemma lem273392 (P : nat -> Prop) (n : nat) : (term34 P n) = (term34 P n).
Proof. exact (eq_refl (term34 P n)). Qed.
Lemma lem273393 (P : nat -> Prop) (n : nat) : (term35 P n) = (term54 P n).
Proof. exact (MK_COMB (@lem273392 P n) (@lem273391 P n)). Qed.
Lemma lem273394 (n : nat) : (term37 n) = (term55 n).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem273393 P n)). Qed.
Lemma lem273395 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem273396 (n : nat) : (term39 n) = (term56 n).
Proof. exact (MK_COMB (@lem273395) (@lem273394 n)). Qed.
Lemma lem273397 : term41 = term57.
Proof. exact (fun_ext (fun n : nat => @lem273396 n)). Qed.
Lemma lem273398 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273399 : term43 = term58.
Proof. exact (MK_COMB (@lem273398) (@lem273397)). Qed.
Lemma lem273402 : term42 = term58.
Proof. exact (TRANS (@lem273371) (@lem273399)). Qed.
Lemma lem273411 (m : nat) (n : nat) : (term59 m n) = (term59 m n).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem273412 (m : nat) : (term60 m) = (term60 m).
Proof. exact (fun_ext (fun n : nat => @lem273411 m n)). Qed.
Lemma lem273413 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273414 (m : nat) : (term61 m) = (term61 m).
Proof. exact (MK_COMB (@lem273413) (@lem273412 m)). Qed.
Lemma lem273415 : term62 = term62.
Proof. exact (fun_ext (fun m : nat => @lem273414 m)). Qed.
Lemma lem273416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273417 : term27 = term27.
Proof. exact (MK_COMB (@lem273416) (@lem273415)). Qed.
Lemma lem273418 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem273419 : term26 = term26.
Proof. exact (MK_COMB (@lem273418) (@lem273417)). Qed.
Lemma lem273420 (y : nat) (n : nat) : (y = n) = (y = n).
Proof. exact (eq_refl (y = n)). Qed.
Lemma lem273427 (y : nat) (P : nat -> Prop) (m : nat) : (term63 y P m) = (term63 y P m).
Proof. exact (eq_refl (term63 y P m)). Qed.
Lemma lem273428 (y : nat) (P : nat -> Prop) : (term64 y P) = (term64 y P).
Proof. exact (fun_ext (fun m : nat => @lem273427 y P m)). Qed.
Lemma lem273429 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273430 (y : nat) (P : nat -> Prop) : (term11 y P) = (term11 y P).
Proof. exact (MK_COMB (@lem273429) (@lem273428 y P)). Qed.
Lemma lem273433 (P : nat -> Prop) (y : nat) : (term65 P y) = (term65 P y).
Proof. exact (eq_refl (term65 P y)). Qed.
Lemma lem273434 (y : nat) (P : nat -> Prop) : (term10 y P) = (term10 y P).
Proof. exact (MK_COMB (@lem273433 P y) (@lem273430 y P)). Qed.
Lemma lem273435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem273436 (y : nat) (P : nat -> Prop) : (term46 y P) = (term46 y P).
Proof. exact (MK_COMB (@lem273435) (@lem273434 y P)). Qed.
Lemma lem273437 (P : nat -> Prop) (y : nat) (n : nat) : ((term10 y P) = (y = n)) = ((term10 y P) = (y = n)).
Proof. exact (MK_COMB (@lem273436 y P) (@lem273420 y n)). Qed.
Lemma lem273438 (P : nat -> Prop) (n : nat) : (term48 P n) = (term48 P n).
Proof. exact (fun_ext (fun y : nat => @lem273437 P y n)). Qed.
Lemma lem273439 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273440 (P : nat -> Prop) (n : nat) : (term49 P n) = (term49 P n).
Proof. exact (MK_COMB (@lem273439) (@lem273438 P n)). Qed.
Lemma lem273441 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem273442 (P : nat -> Prop) (n : nat) : (term50 P n) = (term50 P n).
Proof. exact (MK_COMB (@lem273441) (@lem273440 P n)). Qed.
Lemma lem273443 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem273444 (P : nat -> Prop) (n : nat) : (term51 P n) = (term51 P n).
Proof. exact (MK_COMB (@lem273443) (@lem273442 P n)). Qed.
Lemma lem273445 (P : nat -> Prop) (n : nat) : (term52 P n) = (term52 P n).
Proof. exact (MK_COMB (@lem273444 P n) (@lem273419)). Qed.
Lemma lem273452 (n : nat) (P : nat -> Prop) (m : nat) : (term63 n P m) = (term63 n P m).
Proof. exact (eq_refl (term63 n P m)). Qed.
Lemma lem273453 (n : nat) (P : nat -> Prop) : (term64 n P) = (term64 n P).
Proof. exact (fun_ext (fun m : nat => @lem273452 n P m)). Qed.
Lemma lem273454 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273455 (n : nat) (P : nat -> Prop) : (term11 n P) = (term11 n P).
Proof. exact (MK_COMB (@lem273454) (@lem273453 n P)). Qed.
Lemma lem273456 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem273457 (n : nat) (P : nat -> Prop) : (term31 n P) = (term31 n P).
Proof. exact (MK_COMB (@lem273456) (@lem273455 n P)). Qed.
Lemma lem273458 (P : nat -> Prop) (n : nat) : (term53 P n) = (term53 P n).
Proof. exact (MK_COMB (@lem273457 n P) (@lem273445 P n)). Qed.
Lemma lem273461 (P : nat -> Prop) (n : nat) : (term34 P n) = (term34 P n).
Proof. exact (eq_refl (term34 P n)). Qed.
Lemma lem273462 (P : nat -> Prop) (n : nat) : (term54 P n) = (term54 P n).
Proof. exact (MK_COMB (@lem273461 P n) (@lem273458 P n)). Qed.
Lemma lem273463 (n : nat) : (term55 n) = (term55 n).
Proof. exact (fun_ext (fun P : nat -> Prop => @lem273462 P n)). Qed.
Lemma lem273464 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem273465 (n : nat) : (term56 n) = (term56 n).
Proof. exact (MK_COMB (@lem273464) (@lem273463 n)). Qed.
Lemma lem273466 : term57 = term57.
Proof. exact (fun_ext (fun n : nat => @lem273465 n)). Qed.
Lemma lem273467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273468 : term58 = term58.
Proof. exact (MK_COMB (@lem273467) (@lem273466)). Qed.
Lemma lem273529 : term42 = term58.
Proof. exact (TRANS (@lem273402) (@lem273468)). Qed.
Lemma lem273530 : term58 = term42.
Proof. exact (SYM (@lem273529)). Qed.
Lemma lem273532 (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term11 n P.
Proof. exact (h1). Qed.
Lemma lem273533 (P : nat -> Prop) (n : nat) (h1 : term50 P n) : term50 P n.
Proof. exact (h1). Qed.
Lemma lem273534 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem273540 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem273547 (n : nat) (P : nat -> Prop) (m : nat) : (term63 n P m) = (term66 n P m).
Proof. exact (@lem17265 (Peano.lt m n) (term67 P m)). Qed.
Lemma lem273548 (n : nat) (P : nat -> Prop) : (term64 n P) = (term68 n P).
Proof. exact (fun_ext (fun m : nat => @lem273547 n P m)). Qed.
Lemma lem273549 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273602 (n : nat) (P : nat -> Prop) : (term11 n P) = (term69 n P).
Proof. exact (MK_COMB (@lem273549) (@lem273548 n P)). Qed.
Lemma lem273603 (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term69 n P.
Proof. exact (EQ_MP (@lem273602 n P) (@lem273532 n P h1)). Qed.
Lemma lem273611 (P : nat -> Prop) (m : nat) : (term70 P m) = (P m).
Proof. exact (@lem16933 (P m)). Qed.
Lemma lem273613 (m : nat) (y : nat) : (term71 m y) = (term71 m y).
Proof. exact (eq_refl (term71 m y)). Qed.
Lemma lem273614 (y : nat) (P : nat -> Prop) (m : nat) : (term72 y P m) = (term73 y P m).
Proof. exact (MK_COMB (@lem273613 m y) (@lem273611 P m)). Qed.
Lemma lem273615 (y : nat) (P : nat -> Prop) (m : nat) : (term74 y P m) = (term72 y P m).
Proof. exact (@lem17362 (Peano.lt m y) (term67 P m)). Qed.
Lemma lem273616 (y : nat) (P : nat -> Prop) (m : nat) : (term74 y P m) = (term73 y P m).
Proof. exact (TRANS (@lem273615 y P m) (@lem273614 y P m)). Qed.
Lemma lem273621 (y : nat) (P : nat -> Prop) (m : nat) : (term63 y P m) = (term66 y P m).
Proof. exact (@lem17265 (Peano.lt m y) (term67 P m)). Qed.
Lemma lem273622 (P : nat -> Prop) : (term75 P) = (term76 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem273623 (y : nat) (P : nat -> Prop) : (term77 y P) = (term78 y P).
Proof. exact (@lem273622 (term64 y P)). Qed.
Lemma lem273624 (y : nat) (P : nat -> Prop) (m : nat) : (term79 y P m) = (term63 y P m).
Proof. exact (eq_refl (term79 y P m)). Qed.
Lemma lem273625 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem273626 (y : nat) (P : nat -> Prop) (m : nat) : (term80 y P m) = (term74 y P m).
Proof. exact (MK_COMB (@lem273625) (@lem273624 y P m)). Qed.
Lemma lem273627 (y : nat) (P : nat -> Prop) (m : nat) : (term80 y P m) = (term73 y P m).
Proof. exact (TRANS (@lem273626 y P m) (@lem273616 y P m)). Qed.
Lemma lem273628 (y : nat) (P : nat -> Prop) : (term81 y P) = (term82 y P).
Proof. exact (fun_ext (fun m : nat => @lem273627 y P m)). Qed.
Lemma lem273629 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273630 (y : nat) (P : nat -> Prop) : (term78 y P) = (term83 y P).
Proof. exact (MK_COMB (@lem273629) (@lem273628 y P)). Qed.
Lemma lem273631 (y : nat) (P : nat -> Prop) : (term77 y P) = (term83 y P).
Proof. exact (TRANS (@lem273623 y P) (@lem273630 y P)). Qed.
Lemma lem273632 (y : nat) (P : nat -> Prop) : (term64 y P) = (term68 y P).
Proof. exact (fun_ext (fun m : nat => @lem273621 y P m)). Qed.
Lemma lem273633 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273634 (y : nat) (P : nat -> Prop) : (term11 y P) = (term69 y P).
Proof. exact (MK_COMB (@lem273633) (@lem273632 y P)). Qed.
Lemma lem273636 (P : nat -> Prop) (y : nat) : (term84 P y) = (term84 P y).
Proof. exact (eq_refl (term84 P y)). Qed.
Lemma lem273637 (y : nat) (P : nat -> Prop) : (term85 y P) = (term86 y P).
Proof. exact (MK_COMB (@lem273636 P y) (@lem273631 y P)). Qed.
Lemma lem273638 (y : nat) (P : nat -> Prop) : (term87 y P) = (term85 y P).
Proof. exact (@lem17045 (P y) (term11 y P)). Qed.
Lemma lem273639 (y : nat) (P : nat -> Prop) : (term87 y P) = (term86 y P).
Proof. exact (TRANS (@lem273638 y P) (@lem273637 y P)). Qed.
Lemma lem273641 (P : nat -> Prop) (y : nat) : (term65 P y) = (term65 P y).
Proof. exact (eq_refl (term65 P y)). Qed.
Lemma lem273642 (y : nat) (P : nat -> Prop) : (term10 y P) = (term88 y P).
Proof. exact (MK_COMB (@lem273641 P y) (@lem273634 y P)). Qed.
Lemma lem273643 (y : nat) (n : nat) : (term89 y n) = (term89 y n).
Proof. exact (eq_refl (term89 y n)). Qed.
Lemma lem273644 (y : nat) (n : nat) : (y = n) = (y = n).
Proof. exact (eq_refl (y = n)). Qed.
Lemma lem273645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem273646 (y : nat) (P : nat -> Prop) : (term90 y P) = (term91 y P).
Proof. exact (MK_COMB (@lem273645) (@lem273639 y P)). Qed.
Lemma lem273647 (P : nat -> Prop) (y : nat) (n : nat) : (term92 P y n) = (term93 P y n).
Proof. exact (MK_COMB (@lem273646 y P) (@lem273644 y n)). Qed.
Lemma lem273648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem273649 (y : nat) (P : nat -> Prop) : (term94 y P) = (term95 y P).
Proof. exact (MK_COMB (@lem273648) (@lem273642 y P)). Qed.
Lemma lem273650 (P : nat -> Prop) (y : nat) (n : nat) : (term96 P y n) = (term97 P y n).
Proof. exact (MK_COMB (@lem273649 y P) (@lem273643 y n)). Qed.
Lemma lem273651 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem273652 (P : nat -> Prop) (y : nat) (n : nat) : (term98 P y n) = (term99 P y n).
Proof. exact (MK_COMB (@lem273651) (@lem273650 P y n)). Qed.
Lemma lem273653 (P : nat -> Prop) (y : nat) (n : nat) : (term100 P y n) = (term101 P y n).
Proof. exact (MK_COMB (@lem273652 P y n) (@lem273647 P y n)). Qed.
Lemma lem273654 (P : nat -> Prop) (y : nat) (n : nat) : (term102 P y n) = (term100 P y n).
Proof. exact (@lem17646 (term10 y P) (y = n)). Qed.
Lemma lem273655 (P : nat -> Prop) (y : nat) (n : nat) : (term102 P y n) = (term101 P y n).
Proof. exact (TRANS (@lem273654 P y n) (@lem273653 P y n)). Qed.
Lemma lem273656 (P : nat -> Prop) : (term75 P) = (term76 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem273657 (P : nat -> Prop) (n : nat) : (term50 P n) = (term103 P n).
Proof. exact (@lem273656 (term48 P n)). Qed.
Lemma lem273658 (P : nat -> Prop) (y : nat) (n : nat) : (term104 P n y) = ((term10 y P) = (y = n)).
Proof. exact (eq_refl (term104 P n y)). Qed.
Lemma lem273659 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem273660 (P : nat -> Prop) (y : nat) (n : nat) : (term105 P n y) = (term102 P y n).
Proof. exact (MK_COMB (@lem273659) (@lem273658 P y n)). Qed.
Lemma lem273661 (P : nat -> Prop) (y : nat) (n : nat) : (term105 P n y) = (term101 P y n).
Proof. exact (TRANS (@lem273660 P y n) (@lem273655 P y n)). Qed.
Lemma lem273662 (P : nat -> Prop) (n : nat) : (term106 P n) = (term107 P n).
Proof. exact (fun_ext (fun y : nat => @lem273661 P y n)). Qed.
Lemma lem273663 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273664 (P : nat -> Prop) (n : nat) : (term103 P n) = (term108 P n).
Proof. exact (MK_COMB (@lem273663) (@lem273662 P n)). Qed.
Lemma lem273665 (P : nat -> Prop) (n : nat) : (term50 P n) = (term108 P n).
Proof. exact (TRANS (@lem273657 P n) (@lem273664 P n)). Qed.
Lemma lem273667 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem273668 (P : nat -> Prop) (Q : nat -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem273667 nat P Q). Qed.
Lemma lem273669 (P : nat -> Prop) (n : nat) : (term113 P n) = (term114 P n).
Proof. exact (@lem273668 (term115 P n) (term116 P n)). Qed.
Lemma lem273670 (P : nat -> Prop) (y : nat) (n : nat) : (term117 P n y) = (term97 P y n).
Proof. exact (eq_refl (term117 P n y)). Qed.
Lemma lem273671 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem273672 (P : nat -> Prop) (y : nat) (n : nat) : (term118 P n y) = (term99 P y n).
Proof. exact (MK_COMB (@lem273671) (@lem273670 P y n)). Qed.
Lemma lem273673 (P : nat -> Prop) (y : nat) (n : nat) : (term119 P n y) = (term93 P y n).
Proof. exact (eq_refl (term119 P n y)). Qed.
Lemma lem273674 (P : nat -> Prop) (y : nat) (n : nat) : (term120 P n y) = (term101 P y n).
Proof. exact (MK_COMB (@lem273672 P y n) (@lem273673 P y n)). Qed.
Lemma lem273675 (P : nat -> Prop) (n : nat) : (term121 P n) = (term107 P n).
Proof. exact (fun_ext (fun y : nat => @lem273674 P y n)). Qed.
Lemma lem273676 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273677 (P : nat -> Prop) (n : nat) : (term113 P n) = (term108 P n).
Proof. exact (MK_COMB (@lem273676) (@lem273675 P n)). Qed.
Lemma lem273678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem273679 (P : nat -> Prop) (n : nat) : (term122 P n) = (term123 P n).
Proof. exact (MK_COMB (@lem273678) (@lem273677 P n)). Qed.
Lemma lem273680 (P : nat -> Prop) (y : nat) (n : nat) : (term117 P n y) = (term97 P y n).
Proof. exact (eq_refl (term117 P n y)). Qed.
Lemma lem273681 (P : nat -> Prop) (n : nat) : (term124 P n) = (term115 P n).
Proof. exact (fun_ext (fun y : nat => @lem273680 P y n)). Qed.
Lemma lem273682 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273683 (P : nat -> Prop) (n : nat) : (term125 P n) = (term126 P n).
Proof. exact (MK_COMB (@lem273682) (@lem273681 P n)). Qed.
Lemma lem273684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem273685 (P : nat -> Prop) (n : nat) : (term127 P n) = (term128 P n).
Proof. exact (MK_COMB (@lem273684) (@lem273683 P n)). Qed.
Lemma lem273686 (P : nat -> Prop) (y : nat) (n : nat) : (term119 P n y) = (term93 P y n).
Proof. exact (eq_refl (term119 P n y)). Qed.
Lemma lem273687 (P : nat -> Prop) (n : nat) : (term129 P n) = (term116 P n).
Proof. exact (fun_ext (fun y : nat => @lem273686 P y n)). Qed.
Lemma lem273688 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273689 (P : nat -> Prop) (n : nat) : (term130 P n) = (term131 P n).
Proof. exact (MK_COMB (@lem273688) (@lem273687 P n)). Qed.
Lemma lem273690 (P : nat -> Prop) (n : nat) : (term114 P n) = (term132 P n).
Proof. exact (MK_COMB (@lem273685 P n) (@lem273689 P n)). Qed.
Lemma lem273691 (P : nat -> Prop) (n : nat) : ((term113 P n) = (term114 P n)) = ((term108 P n) = (term132 P n)).
Proof. exact (MK_COMB (@lem273679 P n) (@lem273690 P n)). Qed.
Lemma lem273692 (P : nat -> Prop) (n : nat) : (term108 P n) = (term132 P n).
Proof. exact (EQ_MP (@lem273691 P n) (@lem273669 P n)). Qed.
Lemma lem273870 {A : Type'} (P : Prop) (Q : A -> Prop) : (term133 A P Q) = (term134 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem273871 (P : Prop) (Q : nat -> Prop) : (term135 P Q) = (term136 P Q).
Proof. exact (@lem273870 nat P Q). Qed.
Lemma lem273872 (y : nat) (P : nat -> Prop) : (term137 y P) = (term138 y P).
Proof. exact (@lem273871 (term67 P y) (term82 y P)). Qed.
Lemma lem273873 (y : nat) (P : nat -> Prop) (m : nat) : (term139 y P m) = (term73 y P m).
Proof. exact (eq_refl (term139 y P m)). Qed.
Lemma lem273874 (y : nat) (P : nat -> Prop) : (term140 y P) = (term82 y P).
Proof. exact (fun_ext (fun m : nat => @lem273873 y P m)). Qed.
Lemma lem273875 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273876 (y : nat) (P : nat -> Prop) : (term141 y P) = (term83 y P).
Proof. exact (MK_COMB (@lem273875) (@lem273874 y P)). Qed.
Lemma lem273877 (P : nat -> Prop) (y : nat) : (term84 P y) = (term84 P y).
Proof. exact (eq_refl (term84 P y)). Qed.
Lemma lem273878 (y : nat) (P : nat -> Prop) : (term137 y P) = (term86 y P).
Proof. exact (MK_COMB (@lem273877 P y) (@lem273876 y P)). Qed.
Lemma lem273879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem273880 (y : nat) (P : nat -> Prop) : (term142 y P) = (term143 y P).
Proof. exact (MK_COMB (@lem273879) (@lem273878 y P)). Qed.
Lemma lem273881 (y : nat) (P : nat -> Prop) (m : nat) : (term139 y P m) = (term73 y P m).
Proof. exact (eq_refl (term139 y P m)). Qed.
Lemma lem273882 (P : nat -> Prop) (y : nat) : (term84 P y) = (term84 P y).
Proof. exact (eq_refl (term84 P y)). Qed.
Lemma lem273883 (y : nat) (P : nat -> Prop) (m : nat) : (term144 y P m) = (term145 y P m).
Proof. exact (MK_COMB (@lem273882 P y) (@lem273881 y P m)). Qed.
Lemma lem273884 (y : nat) (P : nat -> Prop) : (term146 y P) = (term147 y P).
Proof. exact (fun_ext (fun m : nat => @lem273883 y P m)). Qed.
Lemma lem273885 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273886 (y : nat) (P : nat -> Prop) : (term138 y P) = (term148 y P).
Proof. exact (MK_COMB (@lem273885) (@lem273884 y P)). Qed.
Lemma lem273887 (y : nat) (P : nat -> Prop) : ((term137 y P) = (term138 y P)) = ((term86 y P) = (term148 y P)).
Proof. exact (MK_COMB (@lem273880 y P) (@lem273886 y P)). Qed.
Lemma lem273888 (y : nat) (P : nat -> Prop) : (term86 y P) = (term148 y P).
Proof. exact (EQ_MP (@lem273887 y P) (@lem273872 y P)). Qed.
Lemma lem273889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem273890 (y : nat) (P : nat -> Prop) : (term91 y P) = (term149 y P).
Proof. exact (MK_COMB (@lem273889) (@lem273888 y P)). Qed.
Lemma lem273891 (y : nat) (n : nat) : (y = n) = (y = n).
Proof. exact (eq_refl (y = n)). Qed.
Lemma lem273892 (P : nat -> Prop) (y : nat) (n : nat) : (term93 P y n) = (term150 P y n).
Proof. exact (MK_COMB (@lem273890 y P) (@lem273891 y n)). Qed.
Lemma lem273894 {A : Type'} (P : A -> Prop) (Q : Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem273895 (P : nat -> Prop) (Q : Prop) : (term153 P Q) = (term154 P Q).
Proof. exact (@lem273894 nat P Q). Qed.
Lemma lem273896 (P : nat -> Prop) (y : nat) (n : nat) : (term155 P y n) = (term156 P y n).
Proof. exact (@lem273895 (term147 y P) (y = n)). Qed.
Lemma lem273897 (y : nat) (P : nat -> Prop) (m : nat) : (term157 y P m) = (term145 y P m).
Proof. exact (eq_refl (term157 y P m)). Qed.
Lemma lem273898 (y : nat) (P : nat -> Prop) : (term158 y P) = (term147 y P).
Proof. exact (fun_ext (fun m : nat => @lem273897 y P m)). Qed.
Lemma lem273899 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273900 (y : nat) (P : nat -> Prop) : (term159 y P) = (term148 y P).
Proof. exact (MK_COMB (@lem273899) (@lem273898 y P)). Qed.
Lemma lem273901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem273902 (y : nat) (P : nat -> Prop) : (term160 y P) = (term149 y P).
Proof. exact (MK_COMB (@lem273901) (@lem273900 y P)). Qed.
Lemma lem273903 (y : nat) (n : nat) : (y = n) = (y = n).
Proof. exact (eq_refl (y = n)). Qed.
Lemma lem273904 (P : nat -> Prop) (y : nat) (n : nat) : (term155 P y n) = (term150 P y n).
Proof. exact (MK_COMB (@lem273902 y P) (@lem273903 y n)). Qed.
Lemma lem273905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem273906 (P : nat -> Prop) (y : nat) (n : nat) : (term161 P y n) = (term162 P y n).
Proof. exact (MK_COMB (@lem273905) (@lem273904 P y n)). Qed.
Lemma lem273907 (y : nat) (P : nat -> Prop) (m : nat) : (term157 y P m) = (term145 y P m).
Proof. exact (eq_refl (term157 y P m)). Qed.
Lemma lem273908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem273909 (y : nat) (P : nat -> Prop) (m : nat) : (term163 y P m) = (term164 y P m).
Proof. exact (MK_COMB (@lem273908) (@lem273907 y P m)). Qed.
Lemma lem273910 (y : nat) (n : nat) : (y = n) = (y = n).
Proof. exact (eq_refl (y = n)). Qed.
Lemma lem273911 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) : (term165 P m y n) = (term166 P m y n).
Proof. exact (MK_COMB (@lem273909 y P m) (@lem273910 y n)). Qed.
Lemma lem273912 (P : nat -> Prop) (y : nat) (n : nat) : (term167 P y n) = (term168 P y n).
Proof. exact (fun_ext (fun m : nat => @lem273911 P m y n)). Qed.
Lemma lem273913 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273914 (P : nat -> Prop) (y : nat) (n : nat) : (term156 P y n) = (term169 P y n).
Proof. exact (MK_COMB (@lem273913) (@lem273912 P y n)). Qed.
Lemma lem273915 (P : nat -> Prop) (y : nat) (n : nat) : ((term155 P y n) = (term156 P y n)) = ((term150 P y n) = (term169 P y n)).
Proof. exact (MK_COMB (@lem273906 P y n) (@lem273914 P y n)). Qed.
Lemma lem273916 (P : nat -> Prop) (y : nat) (n : nat) : (term150 P y n) = (term169 P y n).
Proof. exact (EQ_MP (@lem273915 P y n) (@lem273896 P y n)). Qed.
Lemma lem273917 (P : nat -> Prop) (y : nat) (n : nat) : (term93 P y n) = (term169 P y n).
Proof. exact (TRANS (@lem273892 P y n) (@lem273916 P y n)). Qed.
Lemma lem273918 (P : nat -> Prop) (n : nat) : (term116 P n) = (term170 P n).
Proof. exact (fun_ext (fun y : nat => @lem273917 P y n)). Qed.
Lemma lem273919 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273920 (P : nat -> Prop) (n : nat) : (term131 P n) = (term171 P n).
Proof. exact (MK_COMB (@lem273919) (@lem273918 P n)). Qed.
Lemma lem273921 (P : nat -> Prop) (n : nat) : (term128 P n) = (term128 P n).
Proof. exact (eq_refl (term128 P n)). Qed.
Lemma lem273922 (P : nat -> Prop) (n : nat) : (term132 P n) = (term172 P n).
Proof. exact (MK_COMB (@lem273921 P n) (@lem273920 P n)). Qed.
Lemma lem273924 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem273925 (P : nat -> Prop) (Q : nat -> Prop) : (term112 P Q) = (term111 P Q).
Proof. exact (@lem273924 nat P Q). Qed.
Lemma lem273926 (P : nat -> Prop) (n : nat) : (term173 P n) = (term174 P n).
Proof. exact (@lem273925 (term115 P n) (term170 P n)). Qed.
Lemma lem273927 (P : nat -> Prop) (y : nat) (n : nat) : (term117 P n y) = (term97 P y n).
Proof. exact (eq_refl (term117 P n y)). Qed.
Lemma lem273928 (P : nat -> Prop) (n : nat) : (term124 P n) = (term115 P n).
Proof. exact (fun_ext (fun y : nat => @lem273927 P y n)). Qed.
Lemma lem273929 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273930 (P : nat -> Prop) (n : nat) : (term125 P n) = (term126 P n).
Proof. exact (MK_COMB (@lem273929) (@lem273928 P n)). Qed.
Lemma lem273931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem273932 (P : nat -> Prop) (n : nat) : (term127 P n) = (term128 P n).
Proof. exact (MK_COMB (@lem273931) (@lem273930 P n)). Qed.
Lemma lem273933 (P : nat -> Prop) (y : nat) (n : nat) : (term175 P n y) = (term169 P y n).
Proof. exact (eq_refl (term175 P n y)). Qed.
Lemma lem273934 (P : nat -> Prop) (n : nat) : (term176 P n) = (term170 P n).
Proof. exact (fun_ext (fun y : nat => @lem273933 P y n)). Qed.
Lemma lem273935 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273936 (P : nat -> Prop) (n : nat) : (term177 P n) = (term171 P n).
Proof. exact (MK_COMB (@lem273935) (@lem273934 P n)). Qed.
Lemma lem273937 (P : nat -> Prop) (n : nat) : (term173 P n) = (term172 P n).
Proof. exact (MK_COMB (@lem273932 P n) (@lem273936 P n)). Qed.
Lemma lem273938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem273939 (P : nat -> Prop) (n : nat) : (term178 P n) = (term179 P n).
Proof. exact (MK_COMB (@lem273938) (@lem273937 P n)). Qed.
Lemma lem273940 (P : nat -> Prop) (y : nat) (n : nat) : (term117 P n y) = (term97 P y n).
Proof. exact (eq_refl (term117 P n y)). Qed.
Lemma lem273941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem273942 (P : nat -> Prop) (y : nat) (n : nat) : (term118 P n y) = (term99 P y n).
Proof. exact (MK_COMB (@lem273941) (@lem273940 P y n)). Qed.
Lemma lem273943 (P : nat -> Prop) (y : nat) (n : nat) : (term175 P n y) = (term169 P y n).
Proof. exact (eq_refl (term175 P n y)). Qed.
Lemma lem273944 (P : nat -> Prop) (y : nat) (n : nat) : (term180 P n y) = (term181 P y n).
Proof. exact (MK_COMB (@lem273942 P y n) (@lem273943 P y n)). Qed.
Lemma lem273945 (P : nat -> Prop) (n : nat) : (term182 P n) = (term183 P n).
Proof. exact (fun_ext (fun y : nat => @lem273944 P y n)). Qed.
Lemma lem273946 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273947 (P : nat -> Prop) (n : nat) : (term174 P n) = (term184 P n).
Proof. exact (MK_COMB (@lem273946) (@lem273945 P n)). Qed.
Lemma lem273948 (P : nat -> Prop) (n : nat) : ((term173 P n) = (term174 P n)) = ((term172 P n) = (term184 P n)).
Proof. exact (MK_COMB (@lem273939 P n) (@lem273947 P n)). Qed.
Lemma lem273949 (P : nat -> Prop) (n : nat) : (term172 P n) = (term184 P n).
Proof. exact (EQ_MP (@lem273948 P n) (@lem273926 P n)). Qed.
Lemma lem273951 {A : Type'} (P : Prop) (Q : A -> Prop) : (term133 A P Q) = (term134 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem273952 (P : Prop) (Q : nat -> Prop) : (term135 P Q) = (term136 P Q).
Proof. exact (@lem273951 nat P Q). Qed.
Lemma lem273953 (P : nat -> Prop) (y : nat) (n : nat) : (term185 P y n) = (term186 P y n).
Proof. exact (@lem273952 (term97 P y n) (term168 P y n)). Qed.
Lemma lem273954 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) : (term187 P y n m) = (term166 P m y n).
Proof. exact (eq_refl (term187 P y n m)). Qed.
Lemma lem273955 (P : nat -> Prop) (y : nat) (n : nat) : (term188 P y n) = (term168 P y n).
Proof. exact (fun_ext (fun m : nat => @lem273954 P m y n)). Qed.
Lemma lem273956 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273957 (P : nat -> Prop) (y : nat) (n : nat) : (term189 P y n) = (term169 P y n).
Proof. exact (MK_COMB (@lem273956) (@lem273955 P y n)). Qed.
Lemma lem273958 (P : nat -> Prop) (y : nat) (n : nat) : (term99 P y n) = (term99 P y n).
Proof. exact (eq_refl (term99 P y n)). Qed.
Lemma lem273959 (P : nat -> Prop) (y : nat) (n : nat) : (term185 P y n) = (term181 P y n).
Proof. exact (MK_COMB (@lem273958 P y n) (@lem273957 P y n)). Qed.
Lemma lem273960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem273961 (P : nat -> Prop) (y : nat) (n : nat) : (term190 P y n) = (term191 P y n).
Proof. exact (MK_COMB (@lem273960) (@lem273959 P y n)). Qed.
Lemma lem273962 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) : (term187 P y n m) = (term166 P m y n).
Proof. exact (eq_refl (term187 P y n m)). Qed.
Lemma lem273963 (P : nat -> Prop) (y : nat) (n : nat) : (term99 P y n) = (term99 P y n).
Proof. exact (eq_refl (term99 P y n)). Qed.
Lemma lem273964 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) : (term192 P y n m) = (term193 P m y n).
Proof. exact (MK_COMB (@lem273963 P y n) (@lem273962 P m y n)). Qed.
Lemma lem273965 (P : nat -> Prop) (y : nat) (n : nat) : (term194 P y n) = (term195 P y n).
Proof. exact (fun_ext (fun m : nat => @lem273964 P m y n)). Qed.
Lemma lem273966 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273967 (P : nat -> Prop) (y : nat) (n : nat) : (term186 P y n) = (term196 P y n).
Proof. exact (MK_COMB (@lem273966) (@lem273965 P y n)). Qed.
Lemma lem273968 (P : nat -> Prop) (y : nat) (n : nat) : ((term185 P y n) = (term186 P y n)) = ((term181 P y n) = (term196 P y n)).
Proof. exact (MK_COMB (@lem273961 P y n) (@lem273967 P y n)). Qed.
Lemma lem273969 (P : nat -> Prop) (y : nat) (n : nat) : (term181 P y n) = (term196 P y n).
Proof. exact (EQ_MP (@lem273968 P y n) (@lem273953 P y n)). Qed.
Lemma lem273970 (P : nat -> Prop) (n : nat) : (term183 P n) = (term197 P n).
Proof. exact (fun_ext (fun y : nat => @lem273969 P y n)). Qed.
Lemma lem273971 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem273972 (P : nat -> Prop) (n : nat) : (term184 P n) = (term198 P n).
Proof. exact (MK_COMB (@lem273971) (@lem273970 P n)). Qed.
Lemma lem273973 (P : nat -> Prop) (n : nat) : (term172 P n) = (term198 P n).
Proof. exact (TRANS (@lem273949 P n) (@lem273972 P n)). Qed.
Lemma lem273974 (P : nat -> Prop) (n : nat) : (term132 P n) = (term198 P n).
Proof. exact (TRANS (@lem273922 P n) (@lem273973 P n)). Qed.
Lemma lem273975 (P : nat -> Prop) (n : nat) : (term108 P n) = (term198 P n).
Proof. exact (TRANS (@lem273692 P n) (@lem273974 P n)). Qed.
Lemma lem273976 (P : nat -> Prop) (n : nat) : (term50 P n) = (term198 P n).
Proof. exact (TRANS (@lem273665 P n) (@lem273975 P n)). Qed.
Lemma lem273977 (P : nat -> Prop) (n : nat) (h1 : term50 P n) : term198 P n.
Proof. exact (EQ_MP (@lem273976 P n) (@lem273533 P n h1)). Qed.
Lemma lem273986 (m : nat) (n : nat) : (term59 m n) = (term59 m n).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem273987 (m : nat) : (term60 m) = (term60 m).
Proof. exact (fun_ext (fun n : nat => @lem273986 m n)). Qed.
Lemma lem273988 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem273989 (m : nat) : (term61 m) = (term61 m).
Proof. exact (MK_COMB (@lem273988) (@lem273987 m)). Qed.
Lemma lem273990 : term62 = term62.
Proof. exact (fun_ext (fun m : nat => @lem273989 m)). Qed.
Lemma lem273991 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem274048 : term27 = term27.
Proof. exact (MK_COMB (@lem273991) (@lem273990)). Qed.
Lemma lem274049 (h1 : term27) : term27.
Proof. exact (EQ_MP (@lem274048) (@lem273534 h1)). Qed.
Lemma lem274050 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term196 P y n) : term196 P y n.
Proof. exact (h1). Qed.
Lemma lem274051 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term193 P m y n) : term193 P m y n.
Proof. exact (h1). Qed.
Lemma lem274055 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem274070 (n : nat) (P : nat -> Prop) (m : nat) : (term66 n P m) = (term66 n P m).
Proof. exact (eq_refl (term66 n P m)). Qed.
Lemma lem274071 (n : nat) (P : nat -> Prop) : (term68 n P) = (term68 n P).
Proof. exact (fun_ext (fun m : nat => @lem274070 n P m)). Qed.
Lemma lem274072 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem274073 (n : nat) (P : nat -> Prop) : (term69 n P) = (term69 n P).
Proof. exact (MK_COMB (@lem274072) (@lem274071 n P)). Qed.
Lemma lem274074 (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term69 n P.
Proof. exact (EQ_MP (@lem274073 n P) (@lem273603 n P h1)). Qed.
Lemma lem274095 (m : nat) (n : nat) : (term59 m n) = (term59 m n).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem274096 (m : nat) : (term60 m) = (term60 m).
Proof. exact (fun_ext (fun n : nat => @lem274095 m n)). Qed.
Lemma lem274097 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem274098 (m : nat) : (term61 m) = (term61 m).
Proof. exact (MK_COMB (@lem274097) (@lem274096 m)). Qed.
Lemma lem274099 : term62 = term62.
Proof. exact (fun_ext (fun m : nat => @lem274098 m)). Qed.
Lemma lem274100 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem274101 : term27 = term27.
Proof. exact (MK_COMB (@lem274100) (@lem274099)). Qed.
Lemma lem274102 (h1 : term27) : term27.
Proof. exact (EQ_MP (@lem274101) (@lem274049 h1)). Qed.
Lemma lem274129 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) : (term166 P m y n) = (term166 P m y n).
Proof. exact (eq_refl (term166 P m y n)). Qed.
Lemma lem274136 (y : nat) (n : nat) : (term89 y n) = (term89 y n).
Proof. exact (eq_refl (term89 y n)). Qed.
Lemma lem274151 (y : nat) (P : nat -> Prop) (m : nat) : (term66 y P m) = (term66 y P m).
Proof. exact (eq_refl (term66 y P m)). Qed.
Lemma lem274152 (y : nat) (P : nat -> Prop) : (term68 y P) = (term68 y P).
Proof. exact (fun_ext (fun m : nat => @lem274151 y P m)). Qed.
Lemma lem274153 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem274154 (y : nat) (P : nat -> Prop) : (term69 y P) = (term69 y P).
Proof. exact (MK_COMB (@lem274153) (@lem274152 y P)). Qed.
Lemma lem274159 (P : nat -> Prop) (y : nat) : (term65 P y) = (term65 P y).
Proof. exact (eq_refl (term65 P y)). Qed.
Lemma lem274160 (y : nat) (P : nat -> Prop) : (term88 y P) = (term88 y P).
Proof. exact (MK_COMB (@lem274159 P y) (@lem274154 y P)). Qed.
Lemma lem274161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem274162 (y : nat) (P : nat -> Prop) : (term95 y P) = (term95 y P).
Proof. exact (MK_COMB (@lem274161) (@lem274160 y P)). Qed.
Lemma lem274163 (P : nat -> Prop) (y : nat) (n : nat) : (term97 P y n) = (term97 P y n).
Proof. exact (MK_COMB (@lem274162 y P) (@lem274136 y n)). Qed.
Lemma lem274164 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem274165 (P : nat -> Prop) (y : nat) (n : nat) : (term99 P y n) = (term99 P y n).
Proof. exact (MK_COMB (@lem274164) (@lem274163 P y n)). Qed.
Lemma lem274166 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) : (term193 P m y n) = (term193 P m y n).
Proof. exact (MK_COMB (@lem274165 P y n) (@lem274129 P m y n)). Qed.
Lemma lem274167 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term193 P m y n) : term193 P m y n.
Proof. exact (EQ_MP (@lem274166 P m y n) (@lem274051 P m y n h1)). Qed.
Lemma lem274168 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : term97 P y n.
Proof. exact (h1). Qed.
Lemma lem274169 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term166 P m y n) : term166 P m y n.
Proof. exact (h1). Qed.
Lemma lem274171 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : term88 y P.
Proof. exact (proj1 (@lem274168 P y n h1)). Qed.
Lemma lem274172 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : term69 y P.
Proof. exact (proj2 (@lem274171 P y n h1)). Qed.
Lemma lem274175 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term166 P m y n) : term145 y P m.
Proof. exact (proj1 (@lem274169 P m y n h1)). Qed.
Lemma lem274177 (y : nat) (P : nat -> Prop) (m : nat) (h1 : term73 y P m) : term73 y P m.
Proof. exact (h1). Qed.
Lemma lem274183 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem274191 (n : nat) (P : nat -> Prop) (m : nat) : (term66 n P m) = (term66 n P m).
Proof. exact (eq_refl (term66 n P m)). Qed.
Lemma lem274192 (n : nat) (P : nat -> Prop) : (term68 n P) = (term68 n P).
Proof. exact (fun_ext (fun m : nat => @lem274191 n P m)). Qed.
Lemma lem274193 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem274195 (n : nat) (P : nat -> Prop) : (term69 n P) = (term69 n P).
Proof. exact (MK_COMB (@lem274193) (@lem274192 n P)). Qed.
Lemma lem274196 (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term69 n P.
Proof. exact (EQ_MP (@lem274195 n P) (@lem274074 n P h1)). Qed.
Lemma lem274210 (m : nat) (n : nat) : (term59 m n) = (term59 m n).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem274211 (m : nat) : (term60 m) = (term60 m).
Proof. exact (fun_ext (fun n : nat => @lem274210 m n)). Qed.
Lemma lem274212 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem274213 (m : nat) : (term61 m) = (term61 m).
Proof. exact (MK_COMB (@lem274212) (@lem274211 m)). Qed.
Lemma lem274214 : term62 = term62.
Proof. exact (fun_ext (fun m : nat => @lem274213 m)). Qed.
Lemma lem274215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem274217 : term27 = term27.
Proof. exact (MK_COMB (@lem274215) (@lem274214)). Qed.
Lemma lem274218 (h1 : term27) : term27.
Proof. exact (EQ_MP (@lem274217) (@lem274102 h1)). Qed.
Lemma lem274234 (y : nat) (P : nat -> Prop) (m : nat) : (term66 y P m) = (term66 y P m).
Proof. exact (eq_refl (term66 y P m)). Qed.
Lemma lem274235 (y : nat) (P : nat -> Prop) : (term68 y P) = (term68 y P).
Proof. exact (fun_ext (fun m : nat => @lem274234 y P m)). Qed.
Lemma lem274236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem274238 (y : nat) (P : nat -> Prop) : (term69 y P) = (term69 y P).
Proof. exact (MK_COMB (@lem274236) (@lem274235 y P)). Qed.
Lemma lem274239 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : term69 y P.
Proof. exact (EQ_MP (@lem274238 y P) (@lem274172 P y n h1)). Qed.
Lemma lem274243 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem274286 (P : nat -> Prop) (y : nat) (h1 : term67 P y) : term67 P y.
Proof. exact (h1). Qed.
Lemma lem274298 (n : nat) (P : nat -> Prop) (m : nat) : (term66 n P m) = (term66 n P m).
Proof. exact (eq_refl (term66 n P m)). Qed.
Lemma lem274299 (n : nat) (P : nat -> Prop) : (term68 n P) = (term68 n P).
Proof. exact (fun_ext (fun m : nat => @lem274298 n P m)). Qed.
Lemma lem274300 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem274302 (n : nat) (P : nat -> Prop) : (term69 n P) = (term69 n P).
Proof. exact (MK_COMB (@lem274300) (@lem274299 n P)). Qed.
Lemma lem274303 (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term69 n P.
Proof. exact (EQ_MP (@lem274302 n P) (@lem274074 n P h1)). Qed.
Lemma lem274338 (_6378 : nat) (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term199 n P _6378.
Proof. exact (@lem274196 n P h1 _6378). Qed.
Lemma lem274339 (n : nat) (P : nat -> Prop) (_6378 : nat) : (term199 n P _6378) = (term66 n P _6378).
Proof. exact (eq_refl (term199 n P _6378)). Qed.
Lemma lem274341 (_6379 : nat) (h1 : term27) : term200 _6379.
Proof. exact (@lem274218 h1 _6379). Qed.
Lemma lem274342 (_6379 : nat) : (term200 _6379) = (term61 _6379).
Proof. exact (eq_refl (term200 _6379)). Qed.
Lemma lem274343 (_6379 : nat) (h1 : term27) : term61 _6379.
Proof. exact (EQ_MP (@lem274342 _6379) (@lem274341 _6379 h1)). Qed.
Lemma lem274344 (_6379 : nat) (_6380 : nat) (h1 : term27) : term201 _6379 _6380.
Proof. exact (@lem274343 _6379 h1 _6380). Qed.
Lemma lem274345 (_6379 : nat) (_6380 : nat) : (term201 _6379 _6380) = (term59 _6379 _6380).
Proof. exact (eq_refl (term201 _6379 _6380)). Qed.
Lemma lem274347 (_6381 : nat) (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : term199 y P _6381.
Proof. exact (@lem274239 P y n h1 _6381). Qed.
Lemma lem274348 (y : nat) (P : nat -> Prop) (_6381 : nat) : (term199 y P _6381) = (term66 y P _6381).
Proof. exact (eq_refl (term199 y P _6381)). Qed.
Lemma lem274359 (_6385 : nat) (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term199 n P _6385.
Proof. exact (@lem274303 n P h1 _6385). Qed.
Lemma lem274360 (n : nat) (P : nat -> Prop) (_6385 : nat) : (term199 n P _6385) = (term66 n P _6385).
Proof. exact (eq_refl (term199 n P _6385)). Qed.
Lemma lem274369 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem274375 (_6378 : nat) (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term66 n P _6378.
Proof. exact (EQ_MP (@lem274339 n P _6378) (@lem274338 _6378 n P h1)). Qed.
Lemma lem274385 (_6379 : nat) (_6380 : nat) (h1 : term27) : term59 _6379 _6380.
Proof. exact (EQ_MP (@lem274345 _6379 _6380) (@lem274344 _6379 _6380 h1)). Qed.
Lemma lem274395 (_6381 : nat) (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : term66 y P _6381.
Proof. exact (EQ_MP (@lem274348 y P _6381) (@lem274347 _6381 P y n h1)). Qed.
Lemma lem274397 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem274415 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term166 P m y n) : y = n.
Proof. exact (proj2 (@lem274169 P m y n h1)). Qed.
Lemma lem274417 (P : nat -> Prop) (y : nat) (h1 : term67 P y) : term67 P y.
Proof. exact (h1). Qed.
Lemma lem274437 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term166 P m y n) : y = n.
Proof. exact (proj2 (@lem274169 P m y n h1)). Qed.
Lemma lem274439 (y : nat) (P : nat -> Prop) (m : nat) (h1 : term73 y P m) : Peano.lt m y.
Proof. exact (proj1 (@lem274177 y P m h1)). Qed.
Lemma lem274469 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem274498 (P : nat -> Prop) : (term202 P) = (term202 P).
Proof. exact (eq_refl (term202 P)). Qed.
Lemma lem274499 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term166 P m y n) : (term203 P y) = (term203 P n).
Proof. exact (MK_COMB (@lem274498 P) (@lem274415 P m y n h1)). Qed.
Lemma lem274500 (P : nat -> Prop) (n : nat) : (term203 P n) = (term67 P n).
Proof. exact (eq_refl (term203 P n)). Qed.
Lemma lem274501 (P : nat -> Prop) (y : nat) : (term204 P y) = (term204 P y).
Proof. exact (eq_refl (term204 P y)). Qed.
Lemma lem274502 (y : nat) (P : nat -> Prop) (n : nat) : ((term203 P y) = (term203 P n)) = ((term203 P y) = (term67 P n)).
Proof. exact (MK_COMB (@lem274501 P y) (@lem274500 P n)). Qed.
Lemma lem274503 (P : nat -> Prop) (y : nat) : (term203 P y) = (term67 P y).
Proof. exact (eq_refl (term203 P y)). Qed.
Lemma lem274504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem274505 (P : nat -> Prop) (y : nat) : (term204 P y) = (term205 P y).
Proof. exact (MK_COMB (@lem274504) (@lem274503 P y)). Qed.
Lemma lem274506 (P : nat -> Prop) (n : nat) : (term67 P n) = (term67 P n).
Proof. exact (eq_refl (term67 P n)). Qed.
Lemma lem274507 (y : nat) (P : nat -> Prop) (n : nat) : ((term203 P y) = (term67 P n)) = ((term67 P y) = (term67 P n)).
Proof. exact (MK_COMB (@lem274505 P y) (@lem274506 P n)). Qed.
Lemma lem274508 (y : nat) (P : nat -> Prop) (n : nat) : ((term203 P y) = (term203 P n)) = ((term67 P y) = (term67 P n)).
Proof. exact (TRANS (@lem274502 y P n) (@lem274507 y P n)). Qed.
Lemma lem274509 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term166 P m y n) : (term67 P y) = (term67 P n).
Proof. exact (EQ_MP (@lem274508 y P n) (@lem274499 P m y n h1)). Qed.
Lemma lem274510 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : term166 P m y n) : term67 P n.
Proof. exact (EQ_MP (@lem274509 P m y n h2) (@lem274417 P y h1)). Qed.
Lemma lem274552 (_6385 : nat) (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term66 n P _6385.
Proof. exact (EQ_MP (@lem274360 n P _6385) (@lem274359 _6385 n P h1)). Qed.
Lemma lem274567 (m : nat) : (term206 m) = (term206 m).
Proof. exact (eq_refl (term206 m)). Qed.
Lemma lem274568 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term166 P m y n) : (term207 m y) = (term207 m n).
Proof. exact (MK_COMB (@lem274567 m) (@lem274437 P m y n h1)). Qed.
Lemma lem274569 (m : nat) (n : nat) : (term207 m n) = (Peano.lt m n).
Proof. exact (eq_refl (term207 m n)). Qed.
Lemma lem274570 (m : nat) (y : nat) : (term208 m y) = (term208 m y).
Proof. exact (eq_refl (term208 m y)). Qed.
Lemma lem274571 (y : nat) (m : nat) (n : nat) : ((term207 m y) = (term207 m n)) = ((term207 m y) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem274570 m y) (@lem274569 m n)). Qed.
Lemma lem274572 (m : nat) (y : nat) : (term207 m y) = (Peano.lt m y).
Proof. exact (eq_refl (term207 m y)). Qed.
Lemma lem274573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem274574 (m : nat) (y : nat) : (term208 m y) = (term209 m y).
Proof. exact (MK_COMB (@lem274573) (@lem274572 m y)). Qed.
Lemma lem274575 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem274576 (y : nat) (m : nat) (n : nat) : ((term207 m y) = (Peano.lt m n)) = ((Peano.lt m y) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem274574 m y) (@lem274575 m n)). Qed.
Lemma lem274577 (y : nat) (m : nat) (n : nat) : ((term207 m y) = (term207 m n)) = ((Peano.lt m y) = (Peano.lt m n)).
Proof. exact (TRANS (@lem274571 y m n) (@lem274576 y m n)). Qed.
Lemma lem274578 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term166 P m y n) : (Peano.lt m y) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem274577 y m n) (@lem274568 P m y n h1)). Qed.
Lemma lem274628 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : P y.
Proof. exact (proj1 (@lem274171 P y n h1)). Qed.
Lemma lem274629 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : term210 P y.
Proof. exact (fun h0 : term67 P y => @lem274628 P y n h1). Qed.
Lemma lem274631 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem274632 (P : nat -> Prop) (y : nat) : (term210 P y) = (P y).
Proof. exact (@lem274631 (P y)). Qed.
Lemma lem274633 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : P y.
Proof. exact (EQ_MP (@lem274632 P y) (@lem274629 P y n h1)). Qed.
Lemma lem274635 (b : Prop) (a : Prop) : (a \/ b) = (term212 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem274636 (P : nat -> Prop) (_6378 : nat) (n : nat) : (term66 n P _6378) = (term213 P _6378 n).
Proof. exact (@lem274635 (term67 P _6378) (term214 _6378 n)). Qed.
Lemma lem274638 (a : Prop) : (term215 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem274639 (P : nat -> Prop) (_6378 : nat) : (term70 P _6378) = (P _6378).
Proof. exact (@lem274638 (P _6378)). Qed.
Lemma lem274640 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem274641 (P : nat -> Prop) (_6378 : nat) : (term216 P _6378) = (term34 P _6378).
Proof. exact (MK_COMB (@lem274640) (@lem274639 P _6378)). Qed.
Lemma lem274642 (_6378 : nat) (n : nat) : (term214 _6378 n) = (term214 _6378 n).
Proof. exact (eq_refl (term214 _6378 n)). Qed.
Lemma lem274643 (P : nat -> Prop) (_6378 : nat) (n : nat) : (term213 P _6378 n) = (term217 P _6378 n).
Proof. exact (MK_COMB (@lem274641 P _6378) (@lem274642 _6378 n)). Qed.
Lemma lem274644 (P : nat -> Prop) (_6378 : nat) (n : nat) : (term66 n P _6378) = (term217 P _6378 n).
Proof. exact (TRANS (@lem274636 P _6378 n) (@lem274643 P _6378 n)). Qed.
Lemma lem274647 (_6378 : nat) (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term217 P _6378 n.
Proof. exact (EQ_MP (@lem274644 P _6378 n) (@lem274375 _6378 n P h1)). Qed.
Lemma lem274648 (y : nat) (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term217 P y n.
Proof. exact (@lem274647 y n P h1). Qed.
Lemma lem274651 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term11 n P) (h2 : term97 P y n) : term214 y n.
Proof. exact (@lem274648 y n P h1 (@lem274633 P y n h2)). Qed.
Lemma lem274652 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term11 n P) (h2 : term97 P y n) : term218 y n.
Proof. exact (fun h0 : Peano.lt y n => @lem274651 P y n h1 h2). Qed.
Lemma lem274654 (p : Prop) : (term219 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem274655 (y : nat) (n : nat) : (term218 y n) = (term214 y n).
Proof. exact (@lem274654 (Peano.lt y n)). Qed.
Lemma lem274656 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term11 n P) (h2 : term97 P y n) : term214 y n.
Proof. exact (EQ_MP (@lem274655 y n) (@lem274652 P y n h1 h2)). Qed.
Lemma lem274658 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : term89 y n.
Proof. exact (proj2 (@lem274168 P y n h1)). Qed.
Lemma lem274659 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : term220 y n.
Proof. exact (fun h0 : y = n => @lem274658 P y n h1). Qed.
Lemma lem274661 (p : Prop) : (term219 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem274662 (y : nat) (n : nat) : (term220 y n) = (term89 y n).
Proof. exact (@lem274661 (y = n)). Qed.
Lemma lem274663 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : term89 y n.
Proof. exact (EQ_MP (@lem274662 y n) (@lem274659 P y n h1)). Qed.
Lemma lem274686 (q : Prop) (p : Prop) (r : Prop) : (term221 p q r) = (term221 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem274687 (_6379 : nat) (_6380 : nat) : (term222 _6379 _6380) = (term59 _6379 _6380).
Proof. exact (@lem274686 (Peano.lt _6379 _6380) (Peano.lt _6380 _6379) (_6379 = _6380)). Qed.
Lemma lem274705 (_6379 : nat) (_6380 : nat) : (term223 _6379 _6380) = (term223 _6379 _6380).
Proof. exact (eq_refl (term223 _6379 _6380)). Qed.
Lemma lem274706 (_6379 : nat) (_6380 : nat) : ((term59 _6379 _6380) = (term222 _6379 _6380)) = ((term59 _6379 _6380) = (term59 _6379 _6380)).
Proof. exact (MK_COMB (@lem274705 _6379 _6380) (@lem274687 _6379 _6380)). Qed.
Lemma lem274708 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem274709 (x : Prop) : (x = x) = True.
Proof. exact (@lem274708 Prop x). Qed.
Lemma lem274710 (_6379 : nat) (_6380 : nat) : ((term59 _6379 _6380) = (term59 _6379 _6380)) = True.
Proof. exact (@lem274709 (term59 _6379 _6380)). Qed.
Lemma lem274711 (_6379 : nat) (_6380 : nat) : ((term59 _6379 _6380) = (term222 _6379 _6380)) = True.
Proof. exact (TRANS (@lem274706 _6379 _6380) (@lem274710 _6379 _6380)). Qed.
Lemma lem274712 (_6379 : nat) (_6380 : nat) : True = ((term59 _6379 _6380) = (term222 _6379 _6380)).
Proof. exact (SYM (@lem274711 _6379 _6380)). Qed.
Lemma lem274713 (_6379 : nat) (_6380 : nat) : (term59 _6379 _6380) = (term222 _6379 _6380).
Proof. exact (EQ_MP (@lem274712 _6379 _6380) (@lem0)). Qed.
Lemma lem274714 (_6379 : nat) (_6380 : nat) (h1 : term27) : term222 _6379 _6380.
Proof. exact (EQ_MP (@lem274713 _6379 _6380) (@lem274385 _6379 _6380 h1)). Qed.
Lemma lem274716 (b : Prop) (a : Prop) : (a \/ b) = (term212 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem274717 (_6380 : nat) (_6379 : nat) : (term222 _6379 _6380) = (term224 _6380 _6379).
Proof. exact (@lem274716 (term225 _6379 _6380) (Peano.lt _6380 _6379)). Qed.
Lemma lem274719 (a : Prop) (b : Prop) : (term226 a b) = (term227 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem274720 (_6379 : nat) (_6380 : nat) : (term228 _6379 _6380) = (term229 _6379 _6380).
Proof. exact (@lem274719 (Peano.lt _6379 _6380) (_6379 = _6380)). Qed.
Lemma lem274721 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem274722 (_6379 : nat) (_6380 : nat) : (term230 _6379 _6380) = (term231 _6379 _6380).
Proof. exact (MK_COMB (@lem274721) (@lem274720 _6379 _6380)). Qed.
Lemma lem274723 (_6380 : nat) (_6379 : nat) : (Peano.lt _6380 _6379) = (Peano.lt _6380 _6379).
Proof. exact (eq_refl (Peano.lt _6380 _6379)). Qed.
Lemma lem274724 (_6380 : nat) (_6379 : nat) : (term224 _6380 _6379) = (term232 _6380 _6379).
Proof. exact (MK_COMB (@lem274722 _6379 _6380) (@lem274723 _6380 _6379)). Qed.
Lemma lem274725 (_6380 : nat) (_6379 : nat) : (term222 _6379 _6380) = (term232 _6380 _6379).
Proof. exact (TRANS (@lem274717 _6380 _6379) (@lem274724 _6380 _6379)). Qed.
Lemma lem274727 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term11 n P) (h2 : term97 P y n) : term229 y n.
Proof. exact (conj (@lem274656 P y n h1 h2) (@lem274663 P y n h2)). Qed.
Lemma lem274729 (_6380 : nat) (_6379 : nat) (h1 : term27) : term232 _6380 _6379.
Proof. exact (EQ_MP (@lem274725 _6380 _6379) (@lem274714 _6379 _6380 h1)). Qed.
Lemma lem274730 (n : nat) (y : nat) (h1 : term27) : term232 n y.
Proof. exact (@lem274729 n y h1). Qed.
Lemma lem274733 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : term97 P y n) : Peano.lt n y.
Proof. exact (@lem274730 n y h1 (@lem274727 P y n h2 h3)). Qed.
Lemma lem274734 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : term97 P y n) : term233 n y.
Proof. exact (fun h0 : term214 n y => @lem274733 P y n h1 h2 h3). Qed.
Lemma lem274736 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem274737 (n : nat) (y : nat) : (term233 n y) = (Peano.lt n y).
Proof. exact (@lem274736 (Peano.lt n y)). Qed.
Lemma lem274738 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : term97 P y n) : Peano.lt n y.
Proof. exact (EQ_MP (@lem274737 n y) (@lem274734 P y n h1 h2 h3)). Qed.
Lemma lem274740 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem274741 (P : nat -> Prop) (n : nat) (h1 : P n) : term210 P n.
Proof. exact (fun h0 : term67 P n => @lem274740 P n h1). Qed.
Lemma lem274743 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem274744 (P : nat -> Prop) (n : nat) : (term210 P n) = (P n).
Proof. exact (@lem274743 (P n)). Qed.
Lemma lem274745 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (EQ_MP (@lem274744 P n) (@lem274741 P n h1)). Qed.
Lemma lem274747 (a : Prop) (b : Prop) : (term234 a b) = (term235 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem274748 (y : nat) (P : nat -> Prop) (_6381 : nat) : (term66 y P _6381) = (term236 y P _6381).
Proof. exact (@lem274747 (Peano.lt _6381 y) (P _6381)). Qed.
Lemma lem274750 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem274751 (y : nat) (P : nat -> Prop) (_6381 : nat) : (term236 y P _6381) = (term237 y P _6381).
Proof. exact (@lem274750 (term73 y P _6381)). Qed.
Lemma lem274752 (y : nat) (P : nat -> Prop) (_6381 : nat) : (term66 y P _6381) = (term237 y P _6381).
Proof. exact (TRANS (@lem274748 y P _6381) (@lem274751 y P _6381)). Qed.
Lemma lem274754 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term97 P y n) : term73 y P n.
Proof. exact (conj (@lem274738 P y n h1 h2 h4) (@lem274745 P n h3)). Qed.
Lemma lem274756 (_6381 : nat) (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : term237 y P _6381.
Proof. exact (EQ_MP (@lem274752 y P _6381) (@lem274395 _6381 P y n h1)). Qed.
Lemma lem274757 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term97 P y n) : term237 y P n.
Proof. exact (@lem274756 n P y n h1). Qed.
Lemma lem274760 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term97 P y n) : False.
Proof. exact (@lem274757 P y n h4 (@lem274754 P y n h1 h2 h3 h4)). Qed.
Lemma lem274761 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term97 P y n) : term238.
Proof. exact (fun h0 : ~ False => @lem274760 P y n h1 h2 h3 h4). Qed.
Lemma lem274763 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem274764 : term238 = False.
Proof. exact (@lem274763 False). Qed.
Lemma lem274765 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term97 P y n) : False.
Proof. exact (EQ_MP (@lem274764) (@lem274761 P y n h1 h2 h3 h4)). Qed.
Lemma lem274800 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (h1). Qed.
Lemma lem274801 (P : nat -> Prop) (n : nat) (h1 : P n) : term210 P n.
Proof. exact (fun h0 : term67 P n => @lem274800 P n h1). Qed.
Lemma lem274803 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem274804 (P : nat -> Prop) (n : nat) : (term210 P n) = (P n).
Proof. exact (@lem274803 (P n)). Qed.
Lemma lem274805 (P : nat -> Prop) (n : nat) (h1 : P n) : P n.
Proof. exact (EQ_MP (@lem274804 P n) (@lem274801 P n h1)). Qed.
Lemma lem274808 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem274810 (P : nat -> Prop) (n : nat) : (term67 P n) = (term239 P n).
Proof. exact (@lem274808 (P n)). Qed.
Lemma lem274813 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : term166 P m y n) : term239 P n.
Proof. exact (EQ_MP (@lem274810 P n) (@lem274510 P m y n h1 h2)). Qed.
Lemma lem274816 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : False.
Proof. exact (@lem274813 P m y n h1 h3 (@lem274805 P n h2)). Qed.
Lemma lem274817 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : term238.
Proof. exact (fun h0 : ~ False => @lem274816 P m y n h1 h2 h3). Qed.
Lemma lem274819 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem274820 : term238 = False.
Proof. exact (@lem274819 False). Qed.
Lemma lem274821 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : False.
Proof. exact (EQ_MP (@lem274820) (@lem274817 P m y n h1 h2 h3)). Qed.
Lemma lem274856 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term73 y P m) (h2 : term166 P m y n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem274578 P m y n h2) (@lem274439 y P m h1)). Qed.
Lemma lem274857 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term73 y P m) (h2 : term166 P m y n) : term233 m n.
Proof. exact (fun h0 : term214 m n => @lem274856 P m y n h1 h2). Qed.
Lemma lem274859 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem274860 (m : nat) (n : nat) : (term233 m n) = (Peano.lt m n).
Proof. exact (@lem274859 (Peano.lt m n)). Qed.
Lemma lem274861 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term73 y P m) (h2 : term166 P m y n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem274860 m n) (@lem274857 P m y n h1 h2)). Qed.
Lemma lem274863 (y : nat) (P : nat -> Prop) (m : nat) (h1 : term73 y P m) : P m.
Proof. exact (proj2 (@lem274177 y P m h1)). Qed.
Lemma lem274864 (y : nat) (P : nat -> Prop) (m : nat) (h1 : term73 y P m) : term210 P m.
Proof. exact (fun h0 : term67 P m => @lem274863 y P m h1). Qed.
Lemma lem274866 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem274867 (P : nat -> Prop) (m : nat) : (term210 P m) = (P m).
Proof. exact (@lem274866 (P m)). Qed.
Lemma lem274868 (y : nat) (P : nat -> Prop) (m : nat) (h1 : term73 y P m) : P m.
Proof. exact (EQ_MP (@lem274867 P m) (@lem274864 y P m h1)). Qed.
Lemma lem274870 (a : Prop) (b : Prop) : (term234 a b) = (term235 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem274871 (n : nat) (P : nat -> Prop) (_6385 : nat) : (term66 n P _6385) = (term236 n P _6385).
Proof. exact (@lem274870 (Peano.lt _6385 n) (P _6385)). Qed.
Lemma lem274873 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem274874 (n : nat) (P : nat -> Prop) (_6385 : nat) : (term236 n P _6385) = (term237 n P _6385).
Proof. exact (@lem274873 (term73 n P _6385)). Qed.
Lemma lem274875 (n : nat) (P : nat -> Prop) (_6385 : nat) : (term66 n P _6385) = (term237 n P _6385).
Proof. exact (TRANS (@lem274871 n P _6385) (@lem274874 n P _6385)). Qed.
Lemma lem274877 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term73 y P m) (h2 : term166 P m y n) : term73 n P m.
Proof. exact (conj (@lem274861 P m y n h1 h2) (@lem274868 y P m h1)). Qed.
Lemma lem274879 (_6385 : nat) (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term237 n P _6385.
Proof. exact (EQ_MP (@lem274875 n P _6385) (@lem274552 _6385 n P h1)). Qed.
Lemma lem274880 (m : nat) (n : nat) (P : nat -> Prop) (h1 : term11 n P) : term237 n P m.
Proof. exact (@lem274879 m n P h1). Qed.
Lemma lem274883 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term11 n P) (h2 : term73 y P m) (h3 : term166 P m y n) : False.
Proof. exact (@lem274880 m n P h1 (@lem274877 P m y n h2 h3)). Qed.
Lemma lem274884 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term11 n P) (h2 : term73 y P m) (h3 : term166 P m y n) : term238.
Proof. exact (fun h0 : ~ False => @lem274883 P m y n h1 h2 h3). Qed.
Lemma lem274886 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem274887 : term238 = False.
Proof. exact (@lem274886 False). Qed.
Lemma lem274889 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term11 n P) (h2 : term73 y P m) (h3 : term166 P m y n) : False.
Proof. exact (EQ_MP (@lem274887) (@lem274884 P m y n h1 h2 h3)). Qed.
Lemma lem274890 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem274821 P m y n h1 h2 h3) (fun h4 : False => @lem274469 P n h2)). Qed.
Lemma lem274892 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : False.
Proof. exact (EQ_MP (@lem274890 P m y n h1 h2 h3) (@lem274469 P n h2)). Qed.
Lemma lem274893 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : (term67 P y) = False.
Proof. exact (prop_ext (fun h4 : term67 P y => @lem274892 P m y n h1 h2 h3) (fun h4 : False => @lem274417 P y h1)). Qed.
Lemma lem274894 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : False.
Proof. exact (EQ_MP (@lem274893 P m y n h1 h2 h3) (@lem274417 P y h1)). Qed.
Lemma lem274895 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem274894 P m y n h1 h2 h3) (fun h4 : False => @lem274397 P n h2)). Qed.
Lemma lem274896 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : False.
Proof. exact (EQ_MP (@lem274895 P m y n h1 h2 h3) (@lem274397 P n h2)). Qed.
Lemma lem274897 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term97 P y n) : (P n) = False.
Proof. exact (prop_ext (fun h5 : P n => @lem274765 P y n h1 h2 h3 h4) (fun h5 : False => @lem274369 P n h3)). Qed.
Lemma lem274898 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term97 P y n) : False.
Proof. exact (EQ_MP (@lem274897 P y n h1 h2 h3 h4) (@lem274369 P n h3)). Qed.
Lemma lem274899 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : (term67 P y) = False.
Proof. exact (prop_ext (fun h4 : term67 P y => @lem274896 P m y n h1 h2 h3) (fun h4 : False => @lem274286 P y h1)). Qed.
Lemma lem274900 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : False.
Proof. exact (EQ_MP (@lem274899 P m y n h1 h2 h3) (@lem274286 P y h1)). Qed.
Lemma lem274901 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem274900 P m y n h1 h2 h3) (fun h4 : False => @lem274243 P n h2)). Qed.
Lemma lem274902 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : False.
Proof. exact (EQ_MP (@lem274901 P m y n h1 h2 h3) (@lem274243 P n h2)). Qed.
Lemma lem274903 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term97 P y n) : (P n) = False.
Proof. exact (prop_ext (fun h5 : P n => @lem274898 P y n h1 h2 h3 h4) (fun h5 : False => @lem274183 P n h3)). Qed.
Lemma lem274904 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term97 P y n) : False.
Proof. exact (EQ_MP (@lem274903 P y n h1 h2 h3 h4) (@lem274183 P n h3)). Qed.
Lemma lem274905 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : (term67 P y) = False.
Proof. exact (prop_ext (fun h4 : term67 P y => @lem274902 P m y n h1 h2 h3) (fun h4 : False => @lem274286 P y h1)). Qed.
Lemma lem274906 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : False.
Proof. exact (EQ_MP (@lem274905 P m y n h1 h2 h3) (@lem274286 P y h1)). Qed.
Lemma lem274907 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : (P n) = False.
Proof. exact (prop_ext (fun h4 : P n => @lem274906 P m y n h1 h2 h3) (fun h4 : False => @lem274243 P n h2)). Qed.
Lemma lem274908 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term67 P y) (h2 : P n) (h3 : term166 P m y n) : False.
Proof. exact (EQ_MP (@lem274907 P m y n h1 h2 h3) (@lem274243 P n h2)). Qed.
Lemma lem274909 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term97 P y n) : term27 = False.
Proof. exact (prop_ext (fun h5 : term27 => @lem274904 P y n h1 h2 h3 h4) (fun h5 : False => @lem274218 h1)). Qed.
Lemma lem274910 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term97 P y n) : False.
Proof. exact (EQ_MP (@lem274909 P y n h1 h2 h3 h4) (@lem274218 h1)). Qed.
Lemma lem274911 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term97 P y n) : (P n) = False.
Proof. exact (prop_ext (fun h5 : P n => @lem274910 P y n h1 h2 h3 h4) (fun h5 : False => @lem274183 P n h3)). Qed.
Lemma lem274912 (P : nat -> Prop) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term97 P y n) : False.
Proof. exact (EQ_MP (@lem274911 P y n h1 h2 h3 h4) (@lem274183 P n h3)). Qed.
Lemma lem274913 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term11 n P) (h2 : P n) (h3 : term166 P m y n) : False.
Proof. exact (or_elim (@lem274175 P m y n h3) (fun h0 : term67 P y => @lem274908 P m y n h0 h2 h3) (fun h0 : term73 y P m => @lem274889 P m y n h1 h0 h3)). Qed.
Lemma lem274914 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term193 P m y n) : False.
Proof. exact (or_elim (@lem274167 P m y n h4) (fun h0 : term97 P y n => @lem274912 P y n h1 h2 h3 h0) (fun h0 : term166 P m y n => @lem274913 P m y n h2 h3 h0)). Qed.
Lemma lem274915 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term193 P m y n) : (term193 P m y n) = False.
Proof. exact (prop_ext (fun h5 : term193 P m y n => @lem274914 P m y n h1 h2 h3 h4) (fun h5 : False => @lem274167 P m y n h4)). Qed.
Lemma lem274916 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term193 P m y n) : False.
Proof. exact (EQ_MP (@lem274915 P m y n h1 h2 h3 h4) (@lem274167 P m y n h4)). Qed.
Lemma lem274917 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term193 P m y n) : term27 = False.
Proof. exact (prop_ext (fun h5 : term27 => @lem274916 P m y n h1 h2 h3 h4) (fun h5 : False => @lem274102 h1)). Qed.
Lemma lem274918 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term193 P m y n) : False.
Proof. exact (EQ_MP (@lem274917 P m y n h1 h2 h3 h4) (@lem274102 h1)). Qed.
Lemma lem274919 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term193 P m y n) : (P n) = False.
Proof. exact (prop_ext (fun h5 : P n => @lem274918 P m y n h1 h2 h3 h4) (fun h5 : False => @lem274055 P n h3)). Qed.
Lemma lem274920 (P : nat -> Prop) (m : nat) (y : nat) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : P n) (h4 : term193 P m y n) : False.
Proof. exact (EQ_MP (@lem274919 P m y n h1 h2 h3 h4) (@lem274055 P n h3)). Qed.
Lemma lem274921 (y : nat) (P : nat -> Prop) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : term196 P y n) (h4 : P n) : False.
Proof. exact (ex_elim (@lem274050 P y n h3) (fun m : nat => fun h0 : term195 P y n m => @lem274920 P m y n h1 h2 h4 h0)). Qed.
Lemma lem274922 (P : nat -> Prop) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : term50 P n) (h4 : P n) : False.
Proof. exact (ex_elim (@lem273977 P n h3) (fun y : nat => fun h0 : term197 P n y => @lem274921 y P n h1 h2 h0 h4)). Qed.
Lemma lem274923 (P : nat -> Prop) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : term50 P n) (h4 : P n) : term27 = False.
Proof. exact (prop_ext (fun h5 : term27 => @lem274922 P n h1 h2 h3 h4) (fun h5 : False => @lem274049 h1)). Qed.
Lemma lem274924 (P : nat -> Prop) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : term50 P n) (h4 : P n) : False.
Proof. exact (EQ_MP (@lem274923 P n h1 h2 h3 h4) (@lem274049 h1)). Qed.
Lemma lem274925 (P : nat -> Prop) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : term50 P n) (h4 : P n) : (P n) = False.
Proof. exact (prop_ext (fun h5 : P n => @lem274924 P n h1 h2 h3 h4) (fun h5 : False => @lem273540 P n h4)). Qed.
Lemma lem274926 (P : nat -> Prop) (n : nat) (h1 : term27) (h2 : term11 n P) (h3 : term50 P n) (h4 : P n) : False.
Proof. exact (EQ_MP (@lem274925 P n h1 h2 h3 h4) (@lem273540 P n h4)). Qed.
Lemma lem274927 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : term50 P n) (h3 : P n) : term25.
Proof. exact (fun h0 : term27 => @lem274926 P n h0 h1 h2 h3). Qed.
Lemma lem274928 : term25 = term26.
Proof. exact (@lem69 term27). Qed.
Lemma lem274929 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : term50 P n) (h3 : P n) : term26.
Proof. exact (EQ_MP (@lem274928) (@lem274927 P n h1 h2 h3)). Qed.
Lemma lem274930 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : P n) : term52 P n.
Proof. exact (fun h0 : term50 P n => @lem274929 P n h1 h0 h2). Qed.
Lemma lem274931 (P : nat -> Prop) (n : nat) (h1 : P n) : term53 P n.
Proof. exact (fun h0 : term11 n P => @lem274930 P n h0 h1). Qed.
Lemma lem274932 (P : nat -> Prop) (n : nat) : term54 P n.
Proof. exact (fun h0 : P n => @lem274931 P n h0). Qed.
Lemma lem274937 (n : nat) : term56 n.
Proof. exact (fun P : nat -> Prop => @lem274932 P n). Qed.
Lemma lem274942 : term58.
Proof. exact (fun n : nat => @lem274937 n). Qed.
Lemma lem274943 : term42.
Proof. exact (EQ_MP (@lem273530) (@lem274942)). Qed.
Lemma lem274944 (n : nat) : term240 n.
Proof. exact (@lem274943 n). Qed.
Lemma lem274945 (n : nat) : (term240 n) = (term38 n).
Proof. exact (eq_refl (term240 n)). Qed.
Lemma lem274946 (n : nat) : term38 n.
Proof. exact (EQ_MP (@lem274945 n) (@lem274944 n)). Qed.
Lemma lem274947 (n : nat) (P : nat -> Prop) : term241 n P.
Proof. exact (@lem274946 n P). Qed.
Lemma lem274948 (P : nat -> Prop) (n : nat) : (term241 n P) = (term21 P n).
Proof. exact (eq_refl (term241 n P)). Qed.
Lemma lem274949 (P : nat -> Prop) (n : nat) : term21 P n.
Proof. exact (EQ_MP (@lem274948 P n) (@lem274947 n P)). Qed.
Lemma lem274951 (P : nat -> Prop) (n : nat) : term21 P n.
Proof. exact (@lem273258 P n (@lem274949 P n)). Qed.
Lemma lem274952 (P : nat -> Prop) (n : nat) (h1 : P n) : term32 P n.
Proof. exact (@lem274951 P n (@lem273215 P n h1)). Qed.
Lemma lem274953 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : P n) : term29 P n.
Proof. exact (@lem274952 P n h2 (@lem273214 n P h1)). Qed.
Lemma lem274954 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : term20 P n) (h3 : P n) : term25.
Proof. exact (@lem274953 P n h1 h3 (@lem273243 P n h2)). Qed.
Lemma lem274955 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : term20 P n) (h3 : P n) : False.
Proof. exact (@lem274954 P n h1 h2 h3 (@lem96657)). Qed.
Lemma lem274956 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : term20 P n) (h3 : P n) : (term20 P n) = False.
Proof. exact (prop_ext (fun h4 : term20 P n => @lem274955 P n h1 h2 h3) (fun h4 : False => @lem273243 P n h2)). Qed.
Lemma lem274957 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : term20 P n) (h3 : P n) : False.
Proof. exact (EQ_MP (@lem274956 P n h1 h2 h3) (@lem273243 P n h2)). Qed.
Lemma lem274958 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : P n) : term19 P n.
Proof. exact (fun h0 : term20 P n => @lem274957 P n h1 h0 h2). Qed.
Lemma lem274959 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : P n) : term18 P n.
Proof. exact (EQ_MP (@lem273242 P n) (@lem274958 P n h1 h2)). Qed.
Lemma lem274960 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : P n) : (term9 P) = n.
Proof. exact (@lem273238 P n (@lem274959 P n h1 h2)). Qed.
Lemma lem274961 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : P n) : (minimal P) = n.
Proof. exact (EQ_MP (@lem273234 P n) (@lem274960 P n h1 h2)). Qed.
Lemma lem274962 (n : nat) (P : nat -> Prop) (h1 : term10 n P) : term11 n P.
Proof. exact (proj2 (@lem273213 n P h1)). Qed.
Lemma lem274963 (n : nat) (P : nat -> Prop) (h1 : term10 n P) : P n.
Proof. exact (proj1 (@lem273213 n P h1)). Qed.
Lemma lem274964 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : P n) : (term11 n P) = ((minimal P) = n).
Proof. exact (prop_ext (fun h3 : term11 n P => @lem274961 P n h1 h2) (fun h3 : (minimal P) = n => @lem273214 n P h1)). Qed.
Lemma lem274965 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : P n) : (minimal P) = n.
Proof. exact (EQ_MP (@lem274964 P n h1 h2) (@lem273214 n P h1)). Qed.
Lemma lem274966 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : P n) : (P n) = ((minimal P) = n).
Proof. exact (prop_ext (fun h3 : P n => @lem274965 P n h1 h2) (fun h3 : (minimal P) = n => @lem273215 P n h2)). Qed.
Lemma lem274967 (P : nat -> Prop) (n : nat) (h1 : term11 n P) (h2 : P n) : (minimal P) = n.
Proof. exact (EQ_MP (@lem274966 P n h1 h2) (@lem273215 P n h2)). Qed.
Lemma lem274968 (n : nat) (P : nat -> Prop) (h1 : P n) (h2 : term10 n P) : (term11 n P) = ((minimal P) = n).
Proof. exact (prop_ext (fun h3 : term11 n P => @lem274967 P n h3 h1) (fun h3 : (minimal P) = n => @lem274962 n P h2)). Qed.
Lemma lem274969 (n : nat) (P : nat -> Prop) (h1 : P n) (h2 : term10 n P) : (minimal P) = n.
Proof. exact (EQ_MP (@lem274968 n P h1 h2) (@lem274962 n P h2)). Qed.
Lemma lem274970 (n : nat) (P : nat -> Prop) (h1 : term10 n P) : (P n) = ((minimal P) = n).
Proof. exact (prop_ext (fun h2 : P n => @lem274969 n P h2 h1) (fun h2 : (minimal P) = n => @lem274963 n P h1)). Qed.
Lemma lem274971 (n : nat) (P : nat -> Prop) (h1 : term10 n P) : (minimal P) = n.
Proof. exact (EQ_MP (@lem274970 n P h1) (@lem274963 n P h1)). Qed.
Lemma lem274972 (P : nat -> Prop) (n : nat) : term242 P n.
Proof. exact (fun h0 : term10 n P => @lem274971 n P h0). Qed.
Lemma lem274977 (P : nat -> Prop) : term243 P.
Proof. exact (fun n : nat => @lem274972 P n). Qed.
Lemma lem274982 : term244.
Proof. exact (fun P : nat -> Prop => @lem274977 P). Qed.
