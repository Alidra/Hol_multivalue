Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_RADD_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_SYM_spec.
Require Import LE_ADD_RCANCEL_spec.
Require Import NADD_ADD_spec.
Require Import nadd_le_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Lemma lem1281250 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1281251 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1281252 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1281251 m) (@lem1281250 m)). Qed.
Lemma lem1281253 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1281252 m n). Qed.
Lemma lem1281254 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1281256 (m : nat) : term3 m.
Proof. exact (@lem100973 m). Qed.
Lemma lem1281257 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1281258 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1281257 m) (@lem1281256 m)). Qed.
Lemma lem1281259 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem1281258 m n). Qed.
Lemma lem1281260 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem1281261 (m : nat) (n : nat) : term6 m n.
Proof. exact (EQ_MP (@lem1281260 m n) (@lem1281259 m n)). Qed.
Lemma lem1281262 (m : nat) (n : nat) (p : nat) : term7 m n p.
Proof. exact (@lem1281261 m n p). Qed.
Lemma lem1281263 (p : nat) (m : nat) (n : nat) : (term7 m n p) = ((term8 m n p) = (Peano.le m n)).
Proof. exact (eq_refl (term7 m n p)). Qed.
Lemma lem1281265 (m : nat) : term9 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1281266 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1281267 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem1281266 m) (@lem1281265 m)). Qed.
Lemma lem1281268 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem1281267 m n). Qed.
Lemma lem1281269 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem1281270 (m : nat) (n : nat) : term12 m n.
Proof. exact (EQ_MP (@lem1281269 m n) (@lem1281268 m n)). Qed.
Lemma lem1281271 (m : nat) (n : nat) (p : nat) : term13 m n p.
Proof. exact (@lem1281270 m n p). Qed.
Lemma lem1281272 (m : nat) (n : nat) (p : nat) : (term13 m n p) = ((term14 m n p) = (term15 m n p)).
Proof. exact (eq_refl (term13 m n p)). Qed.
Lemma lem1281274 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1281275 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1281276 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1281275 m) (@lem1281274 m)). Qed.
Lemma lem1281277 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1281276 m n). Qed.
Lemma lem1281278 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1281280 (x : nadd) : term16 x.
Proof. exact (@lem1274104 x). Qed.
Lemma lem1281281 (x : nadd) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1281282 (x : nadd) : term17 x.
Proof. exact (EQ_MP (@lem1281281 x) (@lem1281280 x)). Qed.
Lemma lem1281283 (x : nadd) (y : nadd) : term18 x y.
Proof. exact (@lem1281282 x y). Qed.
Lemma lem1281284 (x : nadd) (y : nadd) : (term18 x y) = ((term19 x y) = (term20 x y)).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1281286 (x : nadd) : term21 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1281287 (x : nadd) : (term21 x) = (term22 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1281288 (x : nadd) : term22 x.
Proof. exact (EQ_MP (@lem1281287 x) (@lem1281286 x)). Qed.
Lemma lem1281289 (x : nadd) (y : nadd) : term23 x y.
Proof. exact (@lem1281288 x y). Qed.
Lemma lem1281290 (x : nadd) (y : nadd) : (term23 x y) = ((nadd_le x y) = (term24 x y)).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1281295 (x : nadd) (y : nadd) : (nadd_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem1281290 x y) (@lem1281289 x y)). Qed.
Lemma lem1281296 (x : nadd) (y : nadd) (z : nadd) : (term25 x y z) = (term26 x y z).
Proof. exact (@lem1281295 (nadd_add x z) (nadd_add y z)). Qed.
Lemma lem1281306 (x : nadd) (y : nadd) : (term19 x y) = (term20 x y).
Proof. exact (EQ_MP (@lem1281284 x y) (@lem1281283 x y)). Qed.
Lemma lem1281307 (x : nadd) (z : nadd) : (term19 x z) = (term20 x z).
Proof. exact (@lem1281306 x z). Qed.
Lemma lem1281308 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1281309 (x : nadd) (z : nadd) (n : nat) : (term27 x z n) = (term28 x z n).
Proof. exact (MK_COMB (@lem1281307 x z) (@lem1281308 n)). Qed.
Lemma lem1281311 {A B : Type'} (f : A -> B) (y : A) : (term29 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1281312 (f : nat -> nat) (y : nat) : (term30 f y) = (f y).
Proof. exact (@lem1281311 nat nat f y). Qed.
Lemma lem1281313 (x : nadd) (z : nadd) (n : nat) : (term31 x z n) = (term28 x z n).
Proof. exact (@lem1281312 (term20 x z) n). Qed.
Lemma lem1281314 (x : nadd) (z : nadd) (n : nat) : (term28 x z n) = (term32 x z n).
Proof. exact (eq_refl (term28 x z n)). Qed.
Lemma lem1281315 (x : nadd) (z : nadd) : (term33 x z) = (term20 x z).
Proof. exact (fun_ext (fun n : nat => @lem1281314 x z n)). Qed.
Lemma lem1281316 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1281317 (x : nadd) (z : nadd) (n : nat) : (term31 x z n) = (term28 x z n).
Proof. exact (MK_COMB (@lem1281315 x z) (@lem1281316 n)). Qed.
Lemma lem1281318 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1281319 (x : nadd) (z : nadd) (n : nat) : (term34 x z n) = (term35 x z n).
Proof. exact (MK_COMB (@lem1281318) (@lem1281317 x z n)). Qed.
Lemma lem1281320 (x : nadd) (z : nadd) (n : nat) : (term28 x z n) = (term32 x z n).
Proof. exact (eq_refl (term28 x z n)). Qed.
Lemma lem1281321 (x : nadd) (z : nadd) (n : nat) : ((term31 x z n) = (term28 x z n)) = ((term28 x z n) = (term32 x z n)).
Proof. exact (MK_COMB (@lem1281319 x z n) (@lem1281320 x z n)). Qed.
Lemma lem1281322 (x : nadd) (z : nadd) (n : nat) : (term28 x z n) = (term32 x z n).
Proof. exact (EQ_MP (@lem1281321 x z n) (@lem1281313 x z n)). Qed.
Lemma lem1281323 (x : nadd) (z : nadd) (n : nat) : (term27 x z n) = (term32 x z n).
Proof. exact (TRANS (@lem1281309 x z n) (@lem1281322 x z n)). Qed.
Lemma lem1281324 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1281325 (x : nadd) (z : nadd) (n : nat) : (term36 x z n) = (term37 x z n).
Proof. exact (MK_COMB (@lem1281324) (@lem1281323 x z n)). Qed.
Lemma lem1281327 (x : nadd) (y : nadd) : (term19 x y) = (term20 x y).
Proof. exact (EQ_MP (@lem1281284 x y) (@lem1281283 x y)). Qed.
Lemma lem1281328 (y : nadd) (z : nadd) : (term19 y z) = (term20 y z).
Proof. exact (@lem1281327 y z). Qed.
Lemma lem1281329 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1281330 (y : nadd) (z : nadd) (n : nat) : (term27 y z n) = (term28 y z n).
Proof. exact (MK_COMB (@lem1281328 y z) (@lem1281329 n)). Qed.
Lemma lem1281332 {A B : Type'} (f : A -> B) (y : A) : (term29 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1281333 (f : nat -> nat) (y : nat) : (term30 f y) = (f y).
Proof. exact (@lem1281332 nat nat f y). Qed.
Lemma lem1281334 (y : nadd) (z : nadd) (n : nat) : (term31 y z n) = (term28 y z n).
Proof. exact (@lem1281333 (term20 y z) n). Qed.
Lemma lem1281335 (y : nadd) (z : nadd) (n : nat) : (term28 y z n) = (term32 y z n).
Proof. exact (eq_refl (term28 y z n)). Qed.
Lemma lem1281336 (y : nadd) (z : nadd) : (term33 y z) = (term20 y z).
Proof. exact (fun_ext (fun n : nat => @lem1281335 y z n)). Qed.
Lemma lem1281337 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1281338 (y : nadd) (z : nadd) (n : nat) : (term31 y z n) = (term28 y z n).
Proof. exact (MK_COMB (@lem1281336 y z) (@lem1281337 n)). Qed.
Lemma lem1281339 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1281340 (y : nadd) (z : nadd) (n : nat) : (term34 y z n) = (term35 y z n).
Proof. exact (MK_COMB (@lem1281339) (@lem1281338 y z n)). Qed.
Lemma lem1281341 (y : nadd) (z : nadd) (n : nat) : (term28 y z n) = (term32 y z n).
Proof. exact (eq_refl (term28 y z n)). Qed.
Lemma lem1281342 (y : nadd) (z : nadd) (n : nat) : ((term31 y z n) = (term28 y z n)) = ((term28 y z n) = (term32 y z n)).
Proof. exact (MK_COMB (@lem1281340 y z n) (@lem1281341 y z n)). Qed.
Lemma lem1281343 (y : nadd) (z : nadd) (n : nat) : (term28 y z n) = (term32 y z n).
Proof. exact (EQ_MP (@lem1281342 y z n) (@lem1281334 y z n)). Qed.
Lemma lem1281344 (y : nadd) (z : nadd) (n : nat) : (term27 y z n) = (term32 y z n).
Proof. exact (TRANS (@lem1281330 y z n) (@lem1281343 y z n)). Qed.
Lemma lem1281345 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1281346 (y : nadd) (z : nadd) (n : nat) : (term38 y z n) = (term39 y z n).
Proof. exact (MK_COMB (@lem1281345) (@lem1281344 y z n)). Qed.
Lemma lem1281347 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1281348 (y : nadd) (z : nadd) (n : nat) (B : nat) : (term40 y z n B) = (term41 y z n B).
Proof. exact (MK_COMB (@lem1281346 y z n) (@lem1281347 B)). Qed.
Lemma lem1281349 (x : nadd) (y : nadd) (z : nadd) (n : nat) (B : nat) : (term42 x y z n B) = (term43 x y z n B).
Proof. exact (MK_COMB (@lem1281325 x z n) (@lem1281348 y z n B)). Qed.
Lemma lem1281350 (x : nadd) (y : nadd) (z : nadd) (B : nat) : (term44 x y z B) = (term45 x y z B).
Proof. exact (fun_ext (fun n : nat => @lem1281349 x y z n B)). Qed.
Lemma lem1281351 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1281352 (x : nadd) (y : nadd) (z : nadd) (B : nat) : (term46 x y z B) = (term47 x y z B).
Proof. exact (MK_COMB (@lem1281351) (@lem1281350 x y z B)). Qed.
Lemma lem1281357 (x : nadd) (y : nadd) (z : nadd) : (term48 x y z) = (term49 x y z).
Proof. exact (fun_ext (fun B : nat => @lem1281352 x y z B)). Qed.
Lemma lem1281358 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1281359 (x : nadd) (y : nadd) (z : nadd) : (term26 x y z) = (term50 x y z).
Proof. exact (MK_COMB (@lem1281358) (@lem1281357 x y z)). Qed.
Lemma lem1281364 (x : nadd) (y : nadd) (z : nadd) : (term25 x y z) = (term50 x y z).
Proof. exact (TRANS (@lem1281296 x y z) (@lem1281359 x y z)). Qed.
Lemma lem1281365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1281366 (x : nadd) (y : nadd) (z : nadd) : (term51 x y z) = (term52 x y z).
Proof. exact (MK_COMB (@lem1281365) (@lem1281364 x y z)). Qed.
Lemma lem1281368 (x : nadd) (y : nadd) : (nadd_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem1281290 x y) (@lem1281289 x y)). Qed.
Lemma lem1281377 (z : nadd) (x : nadd) (y : nadd) : ((term25 x y z) = (nadd_le x y)) = ((term50 x y z) = (term24 x y)).
Proof. exact (MK_COMB (@lem1281366 x y z) (@lem1281368 x y)). Qed.
Lemma lem1281380 (z : nadd) (x : nadd) (y : nadd) : ((term50 x y z) = (term24 x y)) = ((term25 x y z) = (nadd_le x y)).
Proof. exact (SYM (@lem1281377 z x y)). Qed.
Lemma lem1281382 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1281278 n m) (@lem1281277 m n)). Qed.
Lemma lem1281383 (B : nat) (y : nadd) (z : nadd) (n : nat) : (term41 y z n B) = (term53 B y z n).
Proof. exact (@lem1281382 B (term32 y z n)). Qed.
Lemma lem1281384 (x : nadd) (z : nadd) (n : nat) : (term37 x z n) = (term37 x z n).
Proof. exact (eq_refl (term37 x z n)). Qed.
Lemma lem1281385 (x : nadd) (B : nat) (y : nadd) (z : nadd) (n : nat) : (term43 x y z n B) = (term54 x B y z n).
Proof. exact (MK_COMB (@lem1281384 x z n) (@lem1281383 B y z n)). Qed.
Lemma lem1281386 (x : nadd) (B : nat) (y : nadd) (z : nadd) : (term45 x y z B) = (term55 x B y z).
Proof. exact (fun_ext (fun n : nat => @lem1281385 x B y z n)). Qed.
Lemma lem1281387 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1281388 (x : nadd) (B : nat) (y : nadd) (z : nadd) : (term47 x y z B) = (term56 x B y z).
Proof. exact (MK_COMB (@lem1281387) (@lem1281386 x B y z)). Qed.
Lemma lem1281389 (x : nadd) (y : nadd) (z : nadd) : (term49 x y z) = (term57 x y z).
Proof. exact (fun_ext (fun B : nat => @lem1281388 x B y z)). Qed.
Lemma lem1281390 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1281391 (x : nadd) (y : nadd) (z : nadd) : (term50 x y z) = (term58 x y z).
Proof. exact (MK_COMB (@lem1281390) (@lem1281389 x y z)). Qed.
Lemma lem1281392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1281393 (x : nadd) (y : nadd) (z : nadd) : (term52 x y z) = (term59 x y z).
Proof. exact (MK_COMB (@lem1281392) (@lem1281391 x y z)). Qed.
Lemma lem1281394 (x : nadd) (y : nadd) : (term24 x y) = (term24 x y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1281395 (z : nadd) (x : nadd) (y : nadd) : ((term50 x y z) = (term24 x y)) = ((term58 x y z) = (term24 x y)).
Proof. exact (MK_COMB (@lem1281393 x y z) (@lem1281394 x y)). Qed.
Lemma lem1281396 (z : nadd) (x : nadd) (y : nadd) : ((term58 x y z) = (term24 x y)) = ((term50 x y z) = (term24 x y)).
Proof. exact (SYM (@lem1281395 z x y)). Qed.
Lemma lem1281410 (m : nat) (n : nat) (p : nat) : (term14 m n p) = (term15 m n p).
Proof. exact (EQ_MP (@lem1281272 m n p) (@lem1281271 m n p)). Qed.
Lemma lem1281411 (B : nat) (y : nadd) (z : nadd) (n : nat) : (term53 B y z n) = (term60 B y z n).
Proof. exact (@lem1281410 B (dest_nadd y n) (dest_nadd z n)). Qed.
Lemma lem1281412 (x : nadd) (z : nadd) (n : nat) : (term37 x z n) = (term37 x z n).
Proof. exact (eq_refl (term37 x z n)). Qed.
Lemma lem1281413 (x : nadd) (B : nat) (y : nadd) (z : nadd) (n : nat) : (term54 x B y z n) = (term61 x B y z n).
Proof. exact (MK_COMB (@lem1281412 x z n) (@lem1281411 B y z n)). Qed.
Lemma lem1281415 (p : nat) (m : nat) (n : nat) : (term8 m n p) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1281263 p m n) (@lem1281262 m n p)). Qed.
Lemma lem1281416 (z : nadd) (x : nadd) (B : nat) (y : nadd) (n : nat) : (term61 x B y z n) = (term62 x B y n).
Proof. exact (@lem1281415 (dest_nadd z n) (dest_nadd x n) (term63 B y n)). Qed.
Lemma lem1281417 (z : nadd) (x : nadd) (B : nat) (y : nadd) (n : nat) : (term54 x B y z n) = (term62 x B y n).
Proof. exact (TRANS (@lem1281413 x B y z n) (@lem1281416 z x B y n)). Qed.
Lemma lem1281418 (z : nadd) (x : nadd) (B : nat) (y : nadd) : (term55 x B y z) = (term64 x B y).
Proof. exact (fun_ext (fun n : nat => @lem1281417 z x B y n)). Qed.
Lemma lem1281419 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1281420 (z : nadd) (x : nadd) (B : nat) (y : nadd) : (term56 x B y z) = (term65 x B y).
Proof. exact (MK_COMB (@lem1281419) (@lem1281418 z x B y)). Qed.
Lemma lem1281425 (z : nadd) (x : nadd) (y : nadd) : (term57 x y z) = (term66 x y).
Proof. exact (fun_ext (fun B : nat => @lem1281420 z x B y)). Qed.
Lemma lem1281426 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1281427 (z : nadd) (x : nadd) (y : nadd) : (term58 x y z) = (term67 x y).
Proof. exact (MK_COMB (@lem1281426) (@lem1281425 z x y)). Qed.
Lemma lem1281432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1281433 (z : nadd) (x : nadd) (y : nadd) : (term59 x y z) = (term68 x y).
Proof. exact (MK_COMB (@lem1281432) (@lem1281427 z x y)). Qed.
Lemma lem1281442 (x : nadd) (y : nadd) : (term24 x y) = (term24 x y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1281443 (z : nadd) (x : nadd) (y : nadd) : ((term58 x y z) = (term24 x y)) = ((term67 x y) = (term24 x y)).
Proof. exact (MK_COMB (@lem1281433 z x y) (@lem1281442 x y)). Qed.
Lemma lem1281446 (z : nadd) (x : nadd) (y : nadd) : ((term67 x y) = (term24 x y)) = ((term58 x y z) = (term24 x y)).
Proof. exact (SYM (@lem1281443 z x y)). Qed.
Lemma lem1281448 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1281254 n m) (@lem1281253 m n)). Qed.
Lemma lem1281449 (y : nadd) (n : nat) (B : nat) : (term63 B y n) = (term69 y n B).
Proof. exact (@lem1281448 (dest_nadd y n) B). Qed.
Lemma lem1281450 (x : nadd) (n : nat) : (term70 x n) = (term70 x n).
Proof. exact (eq_refl (term70 x n)). Qed.
Lemma lem1281451 (x : nadd) (y : nadd) (n : nat) (B : nat) : (term62 x B y n) = (term71 x y n B).
Proof. exact (MK_COMB (@lem1281450 x n) (@lem1281449 y n B)). Qed.
Lemma lem1281452 (x : nadd) (y : nadd) (B : nat) : (term64 x B y) = (term72 x y B).
Proof. exact (fun_ext (fun n : nat => @lem1281451 x y n B)). Qed.
Lemma lem1281453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1281454 (x : nadd) (y : nadd) (B : nat) : (term65 x B y) = (term73 x y B).
Proof. exact (MK_COMB (@lem1281453) (@lem1281452 x y B)). Qed.
Lemma lem1281455 (x : nadd) (y : nadd) : (term66 x y) = (term74 x y).
Proof. exact (fun_ext (fun B : nat => @lem1281454 x y B)). Qed.
Lemma lem1281456 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1281457 (x : nadd) (y : nadd) : (term67 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem1281456) (@lem1281455 x y)). Qed.
Lemma lem1281458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1281459 (x : nadd) (y : nadd) : (term68 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1281458) (@lem1281457 x y)). Qed.
Lemma lem1281460 (x : nadd) (y : nadd) : (term24 x y) = (term24 x y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1281461 (x : nadd) (y : nadd) : ((term67 x y) = (term24 x y)) = ((term24 x y) = (term24 x y)).
Proof. exact (MK_COMB (@lem1281459 x y) (@lem1281460 x y)). Qed.
Lemma lem1281462 (x : nadd) (y : nadd) : ((term24 x y) = (term24 x y)) = ((term67 x y) = (term24 x y)).
Proof. exact (SYM (@lem1281461 x y)). Qed.
Lemma lem1281463 (x : nadd) (y : nadd) : (term24 x y) = (term24 x y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1281464 (x : nadd) (y : nadd) : (term67 x y) = (term24 x y).
Proof. exact (EQ_MP (@lem1281462 x y) (@lem1281463 x y)). Qed.
Lemma lem1281465 (z : nadd) (x : nadd) (y : nadd) : (term58 x y z) = (term24 x y).
Proof. exact (EQ_MP (@lem1281446 z x y) (@lem1281464 x y)). Qed.
Lemma lem1281466 (z : nadd) (x : nadd) (y : nadd) : (term50 x y z) = (term24 x y).
Proof. exact (EQ_MP (@lem1281396 z x y) (@lem1281465 z x y)). Qed.
Lemma lem1281467 (z : nadd) (x : nadd) (y : nadd) : (term25 x y z) = (nadd_le x y).
Proof. exact (EQ_MP (@lem1281380 z x y) (@lem1281466 z x y)). Qed.
Lemma lem1281472 (x : nadd) (y : nadd) : term76 x y.
Proof. exact (fun z : nadd => @lem1281467 z x y). Qed.
Lemma lem1281477 (x : nadd) : term77 x.
Proof. exact (fun y : nadd => @lem1281472 x y). Qed.
Lemma lem1281482 : term78.
Proof. exact (fun x : nadd => @lem1281477 x). Qed.
