Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_LINV_LEMMA4_term_abbrevs.
Require Import DIST_LMUL_spec.
Require Import DIST_SYM_spec.
Require Import DIST_TRIANGLES_LE_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import MULT_AC_spec.
Require Import NADD_MUL_LINV_LEMMA3_spec.
Require Import thm0_spec.
Require Import thm1157_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1302303 (n : nat) (m : nat) (p : nat) : term0 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem1302307 (a : Prop) (b : Prop) (h1 : term1 a b) : term1 a b.
Proof. exact (h1). Qed.
Lemma lem1302308 (a : Prop) (b : Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem1302309 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term1 a b) : a -> b.
Proof. exact (@lem1302307 a b h2 (@lem1302308 a b h1)). Qed.
Lemma lem1302310 (a : Prop) (b : Prop) (h1 : a = b) : term2 a b.
Proof. exact (fun h0 : term1 a b => @lem1302309 a b h1 h0). Qed.
Lemma lem1302311 (a : Prop) (b : Prop) (h1 : term1 a b) : term1 a b.
Proof. exact (h1). Qed.
Lemma lem1302312 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term1 a b) : a -> b.
Proof. exact (@lem1302310 a b h1 (@lem1302311 a b h2)). Qed.
Lemma lem1302313 (a : Prop) (b : Prop) (h1 : term1 a b) : term1 a b.
Proof. exact (fun h0 : a = b => @lem1302312 a b h0 h1). Qed.
Lemma lem1302314 (a : Prop) (b : Prop) : term3 a b.
Proof. exact (fun h0 : term1 a b => @lem1302313 a b h0). Qed.
Lemma lem1302316 (N : nat) (m : nat) (h1 : Peano.le N m) : Peano.le N m.
Proof. exact (h1). Qed.
Lemma lem1302317 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1302318 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1302319 (m : nat) (h1 : term4) : term5 m.
Proof. exact (@lem1302318 h1 m). Qed.
Lemma lem1302320 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem1302321 (m : nat) (h1 : term4) : term6 m.
Proof. exact (EQ_MP (@lem1302320 m) (@lem1302319 m h1)). Qed.
Lemma lem1302322 (m : nat) (n : nat) (h1 : term4) : term7 m n.
Proof. exact (@lem1302321 m h1 n). Qed.
Lemma lem1302323 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem1302324 (m : nat) (n : nat) (h1 : term4) : term8 m n.
Proof. exact (EQ_MP (@lem1302323 m n) (@lem1302322 m n h1)). Qed.
Lemma lem1302325 (m : nat) (n : nat) (p : nat) (h1 : term4) : term9 m n p.
Proof. exact (@lem1302324 m n h1 p). Qed.
Lemma lem1302326 (m : nat) (p : nat) (n : nat) : (term9 m n p) = (term10 m p n).
Proof. exact (eq_refl (term9 m n p)). Qed.
Lemma lem1302327 (m : nat) (p : nat) (n : nat) (h1 : term4) : term10 m p n.
Proof. exact (EQ_MP (@lem1302326 m p n) (@lem1302325 m n p h1)). Qed.
Lemma lem1302328 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term4) : term11 m p n q.
Proof. exact (@lem1302327 m p n h1 q). Qed.
Lemma lem1302329 (m : nat) (p : nat) (n : nat) (q : nat) : (term11 m p n q) = (term12 m p n q).
Proof. exact (eq_refl (term11 m p n q)). Qed.
Lemma lem1302330 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term4) : term12 m p n q.
Proof. exact (EQ_MP (@lem1302329 m p n q) (@lem1302328 m p n q h1)). Qed.
Lemma lem1302331 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (h1 : term4) : term13 m p n q r.
Proof. exact (@lem1302330 m p n q h1 r). Qed.
Lemma lem1302332 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) : (term13 m p n q r) = (term14 m p n q r).
Proof. exact (eq_refl (term13 m p n q r)). Qed.
Lemma lem1302333 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (h1 : term4) : term14 m p n q r.
Proof. exact (EQ_MP (@lem1302332 m p n q r) (@lem1302331 m p n q r h1)). Qed.
Lemma lem1302334 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (s : nat) (h1 : term4) : term15 m p n q r s.
Proof. exact (@lem1302333 m p n q r h1 s). Qed.
Lemma lem1302335 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (s : nat) : (term15 m p n q r s) = (term16 m p n q r s).
Proof. exact (eq_refl (term15 m p n q r s)). Qed.
Lemma lem1302336 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (s : nat) (h1 : term4) : term16 m p n q r s.
Proof. exact (EQ_MP (@lem1302335 m p n q r s) (@lem1302334 m p n q r s h1)). Qed.
Lemma lem1302337 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term17 m n r p q s) : term17 m n r p q s.
Proof. exact (h1). Qed.
Lemma lem1302338 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term4) (h2 : term17 m n r p q s) : term18 m p n q r s.
Proof. exact (@lem1302336 m p n q r s h1 (@lem1302337 m n r p q s h2)). Qed.
Lemma lem1302339 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term17 m n r p q s) : term19 m p n q r s.
Proof. exact (fun h0 : term4 => @lem1302338 m n r p q s h0 h1). Qed.
Lemma lem1302340 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1302341 (m : nat) (n : nat) (r : nat) (p : nat) (q : nat) (s : nat) (h1 : term4) (h2 : term17 m n r p q s) : term18 m p n q r s.
Proof. exact (@lem1302339 m n r p q s h2 (@lem1302340 h1)). Qed.
Lemma lem1302342 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (s : nat) (h1 : term4) : term16 m p n q r s.
Proof. exact (fun h0 : term17 m n r p q s => @lem1302341 m n r p q s h1 h0). Qed.
Lemma lem1302343 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (h1 : term4) : term14 m p n q r.
Proof. exact (fun s : nat => @lem1302342 m p n q r s h1). Qed.
Lemma lem1302344 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term4) : term12 m p n q.
Proof. exact (fun r : nat => @lem1302343 m p n q r h1). Qed.
Lemma lem1302345 (m : nat) (p : nat) (n : nat) (h1 : term4) : term10 m p n.
Proof. exact (fun q : nat => @lem1302344 m p n q h1). Qed.
Lemma lem1302346 (m : nat) (p : nat) (h1 : term4) : term20 m p.
Proof. exact (fun n : nat => @lem1302345 m p n h1). Qed.
Lemma lem1302347 (m : nat) (h1 : term4) : term21 m.
Proof. exact (fun p : nat => @lem1302346 m p h1). Qed.
Lemma lem1302348 (h1 : term4) : term22.
Proof. exact (fun m : nat => @lem1302347 m h1). Qed.
Lemma lem1302349 : term23.
Proof. exact (fun h0 : term4 => @lem1302348 h0). Qed.
Lemma lem1302350 : term22.
Proof. exact (@lem1302349 (@lem1260086)). Qed.
Lemma lem1302351 (m : nat) : term24 m.
Proof. exact (@lem1302350 m). Qed.
Lemma lem1302352 (m : nat) : (term24 m) = (term21 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1302353 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem1302352 m) (@lem1302351 m)). Qed.
Lemma lem1302354 (m : nat) (p : nat) : term25 m p.
Proof. exact (@lem1302353 m p). Qed.
Lemma lem1302355 (m : nat) (p : nat) : (term25 m p) = (term20 m p).
Proof. exact (eq_refl (term25 m p)). Qed.
Lemma lem1302356 (m : nat) (p : nat) : term20 m p.
Proof. exact (EQ_MP (@lem1302355 m p) (@lem1302354 m p)). Qed.
Lemma lem1302357 (m : nat) (p : nat) (n : nat) : term26 m p n.
Proof. exact (@lem1302356 m p n). Qed.
Lemma lem1302358 (m : nat) (p : nat) (n : nat) : (term26 m p n) = (term10 m p n).
Proof. exact (eq_refl (term26 m p n)). Qed.
Lemma lem1302359 (m : nat) (p : nat) (n : nat) : term10 m p n.
Proof. exact (EQ_MP (@lem1302358 m p n) (@lem1302357 m p n)). Qed.
Lemma lem1302360 (m : nat) (p : nat) (n : nat) (q : nat) : term11 m p n q.
Proof. exact (@lem1302359 m p n q). Qed.
Lemma lem1302361 (m : nat) (p : nat) (n : nat) (q : nat) : (term11 m p n q) = (term12 m p n q).
Proof. exact (eq_refl (term11 m p n q)). Qed.
Lemma lem1302362 (m : nat) (p : nat) (n : nat) (q : nat) : term12 m p n q.
Proof. exact (EQ_MP (@lem1302361 m p n q) (@lem1302360 m p n q)). Qed.
Lemma lem1302363 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) : term13 m p n q r.
Proof. exact (@lem1302362 m p n q r). Qed.
Lemma lem1302364 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) : (term13 m p n q r) = (term14 m p n q r).
Proof. exact (eq_refl (term13 m p n q r)). Qed.
Lemma lem1302365 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) : term14 m p n q r.
Proof. exact (EQ_MP (@lem1302364 m p n q r) (@lem1302363 m p n q r)). Qed.
Lemma lem1302366 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (s : nat) : term15 m p n q r s.
Proof. exact (@lem1302365 m p n q r s). Qed.
Lemma lem1302367 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (s : nat) : (term15 m p n q r s) = (term16 m p n q r s).
Proof. exact (eq_refl (term15 m p n q r s)). Qed.
Lemma lem1302369 (m : nat) : term27 m.
Proof. exact (@lem1244997 m). Qed.
Lemma lem1302370 (m : nat) : (term27 m) = (term28 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem1302371 (m : nat) : term28 m.
Proof. exact (EQ_MP (@lem1302370 m) (@lem1302369 m)). Qed.
Lemma lem1302372 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem1302371 m n). Qed.
Lemma lem1302373 (n : nat) (m : nat) : (term29 m n) = ((term30 m n) = (term30 n m)).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem1302375 (m : nat) : term31 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1302376 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1302377 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem1302376 m) (@lem1302375 m)). Qed.
Lemma lem1302378 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem1302377 m n). Qed.
Lemma lem1302379 (n : nat) (m : nat) : (term33 m n) = (term34 n m).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1302380 (n : nat) (m : nat) : term34 n m.
Proof. exact (EQ_MP (@lem1302379 n m) (@lem1302378 m n)). Qed.
Lemma lem1302381 (n : nat) (m : nat) (p : nat) : term35 n m p.
Proof. exact (@lem1302380 n m p). Qed.
Lemma lem1302382 (n : nat) (m : nat) (p : nat) : (term35 n m p) = ((term36 m n p) = (term37 n m p)).
Proof. exact (eq_refl (term35 n m p)). Qed.
Lemma lem1302384 (m : nat) : term38 m.
Proof. exact (@lem1245388 m). Qed.
Lemma lem1302385 (m : nat) : (term38 m) = (term39 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem1302386 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem1302385 m) (@lem1302384 m)). Qed.
Lemma lem1302387 (m : nat) (n : nat) : term40 m n.
Proof. exact (@lem1302386 m n). Qed.
Lemma lem1302388 (n : nat) (m : nat) : (term40 m n) = (term41 n m).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem1302389 (n : nat) (m : nat) : term41 n m.
Proof. exact (EQ_MP (@lem1302388 n m) (@lem1302387 m n)). Qed.
Lemma lem1302390 (n : nat) (m : nat) (p : nat) : term42 n m p.
Proof. exact (@lem1302389 n m p). Qed.
Lemma lem1302391 (n : nat) (m : nat) (p : nat) : (term42 n m p) = ((term43 m n p) = (term44 n m p)).
Proof. exact (eq_refl (term42 n m p)). Qed.
Lemma lem1302393 (x : nadd) : term45 x.
Proof. exact (@lem1302302 x). Qed.
Lemma lem1302394 (x : nadd) : (term45 x) = (term46 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1302396 (x : nadd) (h1 : term47 x) : term47 x.
Proof. exact (h1). Qed.
Lemma lem1302398 (x : nadd) : term46 x.
Proof. exact (EQ_MP (@lem1302394 x) (@lem1302393 x)). Qed.
Lemma lem1302399 (x : nadd) (h1 : term47 x) : term48 x.
Proof. exact (@lem1302398 x (@lem1302396 x h1)). Qed.
Lemma lem1302400 (x : nadd) (h1 : term48 x) : term48 x.
Proof. exact (h1). Qed.
Lemma lem1302401 (N : nat) (x : nadd) (h1 : term49 N x) : term49 N x.
Proof. exact (h1). Qed.
Lemma lem1302402 (m : nat) (N : nat) (n : nat) (h1 : term50 m N n) : term50 m N n.
Proof. exact (h1). Qed.
Lemma lem1302403 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1302404 (N : nat) (m : nat) (h1 : Peano.le N m) : Peano.le N m.
Proof. exact (h1). Qed.
Lemma lem1302406 (n : nat) (m : nat) (p : nat) : (term43 m n p) = (term44 n m p).
Proof. exact (EQ_MP (@lem1302391 n m p) (@lem1302390 n m p)). Qed.
Lemma lem1302407 (n : nat) (x : nadd) (m : nat) : (term51 n x m) = (term52 n x m).
Proof. exact (@lem1302406 (term53 m x n) (term54 m x n) (term53 n x m)). Qed.
Lemma lem1302408 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1302409 (n : nat) (x : nadd) (m : nat) : (term55 n x m) = (term56 n x m).
Proof. exact (MK_COMB (@lem1302408) (@lem1302407 n x m)). Qed.
Lemma lem1302411 (n : nat) (m : nat) (p : nat) : (term43 m n p) = (term44 n m p).
Proof. exact (EQ_MP (@lem1302391 n m p) (@lem1302390 n m p)). Qed.
Lemma lem1302412 (n : nat) (x : nadd) (m : nat) : (term57 n x m) = (term58 n x m).
Proof. exact (@lem1302411 (term59 m x n) (Nat.mul m n) (term59 n x m)). Qed.
Lemma lem1302413 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1302414 (n : nat) (x : nadd) (m : nat) : (term60 n x m) = (term61 n x m).
Proof. exact (MK_COMB (@lem1302413) (@lem1302412 n x m)). Qed.
Lemma lem1302416 (n : nat) (m : nat) (p : nat) : (term36 m n p) = (term37 n m p).
Proof. exact (EQ_MP (@lem1302382 n m p) (@lem1302381 n m p)). Qed.
Lemma lem1302417 (m : nat) (x : nadd) (n : nat) : (term62 x m n) = (term63 m x n).
Proof. exact (@lem1302416 m (term54 m x n) n). Qed.
Lemma lem1302418 (m : nat) (x : nadd) (n : nat) : (term64 x m n) = (term65 m x n).
Proof. exact (MK_COMB (@lem1302414 n x m) (@lem1302417 m x n)). Qed.
Lemma lem1302419 (m : nat) (x : nadd) (n : nat) : (term66 x m n) = (term67 m x n).
Proof. exact (MK_COMB (@lem1302409 n x m) (@lem1302418 m x n)). Qed.
Lemma lem1302420 (x : nadd) (m : nat) (n : nat) : (term67 m x n) = (term66 x m n).
Proof. exact (SYM (@lem1302419 m x n)). Qed.
Lemma lem1302422 (n : nat) (m : nat) : (term30 m n) = (term30 n m).
Proof. exact (EQ_MP (@lem1302373 n m) (@lem1302372 m n)). Qed.
Lemma lem1302423 (m : nat) (x : nadd) (n : nat) : (term58 n x m) = (term68 m x n).
Proof. exact (@lem1302422 (term69 n x m) (term70 m x n)). Qed.
Lemma lem1302424 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1302425 (m : nat) (x : nadd) (n : nat) : (term61 n x m) = (term71 m x n).
Proof. exact (MK_COMB (@lem1302424) (@lem1302423 m x n)). Qed.
Lemma lem1302426 (m : nat) (x : nadd) (n : nat) : (term63 m x n) = (term63 m x n).
Proof. exact (eq_refl (term63 m x n)). Qed.
Lemma lem1302427 (m : nat) (x : nadd) (n : nat) : (term65 m x n) = (term72 m x n).
Proof. exact (MK_COMB (@lem1302425 m x n) (@lem1302426 m x n)). Qed.
Lemma lem1302428 (n : nat) (x : nadd) (m : nat) : (term56 n x m) = (term56 n x m).
Proof. exact (eq_refl (term56 n x m)). Qed.
Lemma lem1302429 (m : nat) (x : nadd) (n : nat) : (term67 m x n) = (term73 m x n).
Proof. exact (MK_COMB (@lem1302428 n x m) (@lem1302427 m x n)). Qed.
Lemma lem1302430 (m : nat) (x : nadd) (n : nat) : (term73 m x n) = (term67 m x n).
Proof. exact (SYM (@lem1302429 m x n)). Qed.
Lemma lem1302432 (m : nat) (p : nat) (n : nat) (q : nat) (r : nat) (s : nat) : term16 m p n q r s.
Proof. exact (EQ_MP (@lem1302367 m p n q r s) (@lem1302366 m p n q r s)). Qed.
Lemma lem1302433 (m : nat) (x : nadd) (n : nat) : term74 m x n.
Proof. exact (@lem1302432 (term75 m x n) (term76 n x m) (term69 n x m) (term70 m x n) (term77 x n m) (term78 m x n)). Qed.
Lemma lem1302434 (N : nat) (x : nadd) (h1 : term49 N x) : term49 N x.
Proof. exact (h1). Qed.
Lemma lem1302435 (m : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term79 N x m.
Proof. exact (@lem1302434 N x h1 m). Qed.
Lemma lem1302436 (N : nat) (m : nat) (x : nadd) : (term79 N x m) = (term80 N m x).
Proof. exact (eq_refl (term79 N x m)). Qed.
Lemma lem1302437 (m : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term80 N m x.
Proof. exact (EQ_MP (@lem1302436 N m x) (@lem1302435 m N x h1)). Qed.
Lemma lem1302438 (m : nat) (n : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term81 N m x n.
Proof. exact (@lem1302437 m N x h1 n). Qed.
Lemma lem1302439 (N : nat) (m : nat) (x : nadd) (n : nat) : (term81 N m x n) = (term82 N m x n).
Proof. exact (eq_refl (term81 N m x n)). Qed.
Lemma lem1302440 (m : nat) (n : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term82 N m x n.
Proof. exact (EQ_MP (@lem1302439 N m x n) (@lem1302438 m n N x h1)). Qed.
Lemma lem1302441 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1302442 (m : nat) (x : nadd) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N n) : term83 m x n.
Proof. exact (@lem1302440 m n N x h1 (@lem1302441 N n h2)). Qed.
Lemma lem1302443 (x : nadd) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N n) : term84 x n.
Proof. exact (fun m : nat => @lem1302442 m x N n h1 h2). Qed.
Lemma lem1302444 (n : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term85 N x n.
Proof. exact (fun h0 : Peano.le N n => @lem1302443 x N n h1 h0). Qed.
Lemma lem1302445 (N : nat) (x : nadd) (h1 : term49 N x) : term86 N x.
Proof. exact (fun n : nat => @lem1302444 n N x h1). Qed.
Lemma lem1302446 (N : nat) (x : nadd) : term87 N x.
Proof. exact (fun h0 : term49 N x => @lem1302445 N x h0). Qed.
Lemma lem1302447 (N : nat) (x : nadd) (h1 : term49 N x) : term86 N x.
Proof. exact (@lem1302446 N x (@lem1302401 N x h1)). Qed.
Lemma lem1302448 (n : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term88 N x n.
Proof. exact (@lem1302447 N x h1 n). Qed.
Lemma lem1302449 (N : nat) (x : nadd) (n : nat) : (term88 N x n) = (term85 N x n).
Proof. exact (eq_refl (term88 N x n)). Qed.
Lemma lem1302452 (n : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term85 N x n.
Proof. exact (EQ_MP (@lem1302449 N x n) (@lem1302448 n N x h1)). Qed.
Lemma lem1302453 (x : nadd) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N n) : term84 x n.
Proof. exact (@lem1302452 n N x h1 (@lem1302317 N n h2)). Qed.
Lemma lem1302454 (m : nat) (x : nadd) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N n) : term89 x n m.
Proof. exact (@lem1302453 x N n h1 h2 m). Qed.
Lemma lem1302455 (m : nat) (x : nadd) (n : nat) : (term89 x n m) = (term83 m x n).
Proof. exact (eq_refl (term89 x n m)). Qed.
Lemma lem1302456 (m : nat) (x : nadd) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N n) : term83 m x n.
Proof. exact (EQ_MP (@lem1302455 m x n) (@lem1302454 m x N n h1 h2)). Qed.
Lemma lem1302457 (N : nat) (x : nadd) (h1 : term49 N x) : term49 N x.
Proof. exact (h1). Qed.
Lemma lem1302458 (m : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term79 N x m.
Proof. exact (@lem1302457 N x h1 m). Qed.
Lemma lem1302459 (N : nat) (m : nat) (x : nadd) : (term79 N x m) = (term80 N m x).
Proof. exact (eq_refl (term79 N x m)). Qed.
Lemma lem1302460 (m : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term80 N m x.
Proof. exact (EQ_MP (@lem1302459 N m x) (@lem1302458 m N x h1)). Qed.
Lemma lem1302461 (m : nat) (n : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term81 N m x n.
Proof. exact (@lem1302460 m N x h1 n). Qed.
Lemma lem1302462 (N : nat) (m : nat) (x : nadd) (n : nat) : (term81 N m x n) = (term82 N m x n).
Proof. exact (eq_refl (term81 N m x n)). Qed.
Lemma lem1302463 (m : nat) (n : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term82 N m x n.
Proof. exact (EQ_MP (@lem1302462 N m x n) (@lem1302461 m n N x h1)). Qed.
Lemma lem1302464 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1302465 (m : nat) (x : nadd) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N n) : term83 m x n.
Proof. exact (@lem1302463 m n N x h1 (@lem1302464 N n h2)). Qed.
Lemma lem1302466 (x : nadd) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N n) : term84 x n.
Proof. exact (fun m : nat => @lem1302465 m x N n h1 h2). Qed.
Lemma lem1302467 (n : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term85 N x n.
Proof. exact (fun h0 : Peano.le N n => @lem1302466 x N n h1 h0). Qed.
Lemma lem1302468 (N : nat) (x : nadd) (h1 : term49 N x) : term86 N x.
Proof. exact (fun n : nat => @lem1302467 n N x h1). Qed.
Lemma lem1302469 (N : nat) (x : nadd) : term87 N x.
Proof. exact (fun h0 : term49 N x => @lem1302468 N x h0). Qed.
Lemma lem1302470 (N : nat) (x : nadd) (h1 : term49 N x) : term86 N x.
Proof. exact (@lem1302469 N x (@lem1302401 N x h1)). Qed.
Lemma lem1302471 (n : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term88 N x n.
Proof. exact (@lem1302470 N x h1 n). Qed.
Lemma lem1302472 (N : nat) (x : nadd) (n : nat) : (term88 N x n) = (term85 N x n).
Proof. exact (eq_refl (term88 N x n)). Qed.
Lemma lem1302475 (n : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term85 N x n.
Proof. exact (EQ_MP (@lem1302472 N x n) (@lem1302471 n N x h1)). Qed.
Lemma lem1302476 (m : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term85 N x m.
Proof. exact (@lem1302475 m N x h1). Qed.
Lemma lem1302477 (x : nadd) (N : nat) (m : nat) (h1 : term49 N x) (h2 : Peano.le N m) : term84 x m.
Proof. exact (@lem1302476 m N x h1 (@lem1302316 N m h2)). Qed.
Lemma lem1302478 (n : nat) (x : nadd) (N : nat) (m : nat) (h1 : term49 N x) (h2 : Peano.le N m) : term89 x m n.
Proof. exact (@lem1302477 x N m h1 h2 n). Qed.
Lemma lem1302479 (n : nat) (x : nadd) (m : nat) : (term89 x m n) = (term83 n x m).
Proof. exact (eq_refl (term89 x m n)). Qed.
Lemma lem1302480 (n : nat) (x : nadd) (N : nat) (m : nat) (h1 : term49 N x) (h2 : Peano.le N m) : term83 n x m.
Proof. exact (EQ_MP (@lem1302479 n x m) (@lem1302478 n x N m h1 h2)). Qed.
Lemma lem1302482 (a : Prop) (b : Prop) : term1 a b.
Proof. exact (@lem1302314 a b (@lem1157 a b)). Qed.
Lemma lem1302483 (x : nadd) (n : nat) (m : nat) : term90 x n m.
Proof. exact (@lem1302482 (term83 m x n) (term91 x n m)). Qed.
Lemma lem1302485 (a : Prop) (b : Prop) : term1 a b.
Proof. exact (@lem1302314 a b (@lem1157 a b)). Qed.
Lemma lem1302486 (m : nat) (x : nadd) (n : nat) : term92 m x n.
Proof. exact (@lem1302485 (term83 n x m) (term93 m x n)). Qed.
Lemma lem1302511 (n : nat) (m : nat) (p : nat) : (term94 m n p) = (term94 n m p).
Proof. exact (proj2 (@lem1302303 n m p)). Qed.
Lemma lem1302512 (x : nadd) (m : nat) (n : nat) : (term95 x m n) = (term96 x m n).
Proof. exact (@lem1302511 n (dest_nadd x m) n). Qed.
Lemma lem1302520 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1302521 (n : nat) (x : nadd) (m : nat) : (term97 x m n) = (term59 n x m).
Proof. exact (@lem1302520 n (dest_nadd x m)). Qed.
Lemma lem1302525 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1302526 (n : nat) (x : nadd) (m : nat) : (term96 x m n) = (term98 n x m).
Proof. exact (MK_COMB (@lem1302525 n) (@lem1302521 n x m)). Qed.
Lemma lem1302533 (n : nat) (x : nadd) (m : nat) : (term95 x m n) = (term98 n x m).
Proof. exact (TRANS (@lem1302512 x m n) (@lem1302526 n x m)). Qed.
Lemma lem1302534 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1302535 (n : nat) (x : nadd) (m : nat) : (term99 x m n) = (term100 n x m).
Proof. exact (MK_COMB (@lem1302534 m) (@lem1302533 n x m)). Qed.
Lemma lem1302542 (m : nat) (x : nadd) (n : nat) : (term101 m x n) = (term101 m x n).
Proof. exact (eq_refl (term101 m x n)). Qed.
Lemma lem1302543 (n : nat) (x : nadd) (m : nat) : (term102 x m n) = (term103 n x m).
Proof. exact (MK_COMB (@lem1302542 m x n) (@lem1302535 n x m)). Qed.
Lemma lem1302544 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1302545 (n : nat) (x : nadd) (m : nat) : (term104 x m n) = (term105 n x m).
Proof. exact (MK_COMB (@lem1302544) (@lem1302543 n x m)). Qed.
Lemma lem1302546 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1302547 (n : nat) (x : nadd) (m : nat) : (term106 x m n) = (term107 n x m).
Proof. exact (MK_COMB (@lem1302546) (@lem1302545 n x m)). Qed.
Lemma lem1302557 (m : nat) (x : nadd) (n : nat) : (term108 m x n) = (term108 m x n).
Proof. exact (eq_refl (term108 m x n)). Qed.
Lemma lem1302558 (m : nat) (x : nadd) (n : nat) : (term83 m x n) = (term109 m x n).
Proof. exact (MK_COMB (@lem1302547 n x m) (@lem1302557 m x n)). Qed.
Lemma lem1302559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1302560 (m : nat) (x : nadd) (n : nat) : (term110 m x n) = (term111 m x n).
Proof. exact (MK_COMB (@lem1302559) (@lem1302558 m x n)). Qed.
Lemma lem1302562 (m : nat) (n : nat) (p : nat) : (term112 m n p) = (term94 m n p).
Proof. exact (proj1 (@lem1302303 n m p)). Qed.
Lemma lem1302563 (m : nat) (x : nadd) (n : nat) : (term75 m x n) = (term113 m x n).
Proof. exact (@lem1302562 (dest_nadd x m) (dest_nadd x n) (term53 m x n)). Qed.
Lemma lem1302571 (n : nat) (m : nat) (p : nat) : (term94 m n p) = (term94 n m p).
Proof. exact (proj2 (@lem1302303 n m p)). Qed.
Lemma lem1302572 (m : nat) (x : nadd) (n : nat) : (term114 m x n) = (term115 m x n).
Proof. exact (@lem1302571 m (dest_nadd x n) (nadd_rinv x n)). Qed.
Lemma lem1302582 (x : nadd) (m : nat) : (term116 x m) = (term116 x m).
Proof. exact (eq_refl (term116 x m)). Qed.
Lemma lem1302583 (m : nat) (x : nadd) (n : nat) : (term113 m x n) = (term117 m x n).
Proof. exact (MK_COMB (@lem1302582 x m) (@lem1302572 m x n)). Qed.
Lemma lem1302585 (n : nat) (m : nat) (p : nat) : (term94 m n p) = (term94 n m p).
Proof. exact (proj2 (@lem1302303 n m p)). Qed.
Lemma lem1302586 (m : nat) (x : nadd) (n : nat) : (term117 m x n) = (term118 m x n).
Proof. exact (@lem1302585 m (dest_nadd x m) (term119 x n)). Qed.
Lemma lem1302602 (m : nat) (x : nadd) (n : nat) : (term113 m x n) = (term118 m x n).
Proof. exact (TRANS (@lem1302583 m x n) (@lem1302586 m x n)). Qed.
Lemma lem1302603 (m : nat) (x : nadd) (n : nat) : (term75 m x n) = (term118 m x n).
Proof. exact (TRANS (@lem1302563 m x n) (@lem1302602 m x n)). Qed.
Lemma lem1302604 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1302605 (m : nat) (x : nadd) (n : nat) : (term120 m x n) = (term101 m x n).
Proof. exact (MK_COMB (@lem1302604) (@lem1302603 m x n)). Qed.
Lemma lem1302607 (m : nat) (n : nat) (p : nat) : (term112 m n p) = (term94 m n p).
Proof. exact (proj1 (@lem1302303 n m p)). Qed.
Lemma lem1302608 (n : nat) (x : nadd) (m : nat) : (term69 n x m) = (term100 n x m).
Proof. exact (@lem1302607 m n (term59 n x m)). Qed.
Lemma lem1302624 (n : nat) (x : nadd) (m : nat) : (term121 n x m) = (term103 n x m).
Proof. exact (MK_COMB (@lem1302605 m x n) (@lem1302608 n x m)). Qed.
Lemma lem1302625 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1302626 (n : nat) (x : nadd) (m : nat) : (term122 n x m) = (term105 n x m).
Proof. exact (MK_COMB (@lem1302625) (@lem1302624 n x m)). Qed.
Lemma lem1302627 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1302628 (n : nat) (x : nadd) (m : nat) : (term123 n x m) = (term107 n x m).
Proof. exact (MK_COMB (@lem1302627) (@lem1302626 n x m)). Qed.
Lemma lem1302630 (m : nat) (n : nat) (p : nat) : (term112 m n p) = (term94 m n p).
Proof. exact (proj1 (@lem1302303 n m p)). Qed.
Lemma lem1302631 (x : nadd) (n : nat) (m : nat) : (term77 x n m) = (term124 x n m).
Proof. exact (@lem1302630 (dest_nadd x m) (dest_nadd x n) m). Qed.
Lemma lem1302639 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1302640 (m : nat) (x : nadd) (n : nat) : (term97 x n m) = (term59 m x n).
Proof. exact (@lem1302639 m (dest_nadd x n)). Qed.
Lemma lem1302644 (x : nadd) (m : nat) : (term116 x m) = (term116 x m).
Proof. exact (eq_refl (term116 x m)). Qed.
Lemma lem1302645 (m : nat) (x : nadd) (n : nat) : (term124 x n m) = (term125 m x n).
Proof. exact (MK_COMB (@lem1302644 x m) (@lem1302640 m x n)). Qed.
Lemma lem1302647 (n : nat) (m : nat) (p : nat) : (term94 m n p) = (term94 n m p).
Proof. exact (proj2 (@lem1302303 n m p)). Qed.
Lemma lem1302648 (m : nat) (x : nadd) (n : nat) : (term125 m x n) = (term108 m x n).
Proof. exact (@lem1302647 m (dest_nadd x m) (dest_nadd x n)). Qed.
Lemma lem1302658 (m : nat) (x : nadd) (n : nat) : (term124 x n m) = (term108 m x n).
Proof. exact (TRANS (@lem1302645 m x n) (@lem1302648 m x n)). Qed.
Lemma lem1302659 (m : nat) (x : nadd) (n : nat) : (term77 x n m) = (term108 m x n).
Proof. exact (TRANS (@lem1302631 x n m) (@lem1302658 m x n)). Qed.
Lemma lem1302660 (m : nat) (x : nadd) (n : nat) : (term91 x n m) = (term109 m x n).
Proof. exact (MK_COMB (@lem1302628 n x m) (@lem1302659 m x n)). Qed.
Lemma lem1302661 (m : nat) (x : nadd) (n : nat) : ((term83 m x n) = (term91 x n m)) = ((term109 m x n) = (term109 m x n)).
Proof. exact (MK_COMB (@lem1302560 m x n) (@lem1302660 m x n)). Qed.
Lemma lem1302663 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1302664 (x : Prop) : (x = x) = True.
Proof. exact (@lem1302663 Prop x). Qed.
Lemma lem1302665 (m : nat) (x : nadd) (n : nat) : ((term109 m x n) = (term109 m x n)) = True.
Proof. exact (@lem1302664 (term109 m x n)). Qed.
Lemma lem1302666 (x : nadd) (n : nat) (m : nat) : ((term83 m x n) = (term91 x n m)) = True.
Proof. exact (TRANS (@lem1302661 m x n) (@lem1302665 m x n)). Qed.
Lemma lem1302667 (x : nadd) (n : nat) (m : nat) : True = ((term83 m x n) = (term91 x n m)).
Proof. exact (SYM (@lem1302666 x n m)). Qed.
Lemma lem1302668 (x : nadd) (n : nat) (m : nat) : (term83 m x n) = (term91 x n m).
Proof. exact (EQ_MP (@lem1302667 x n m) (@lem0)). Qed.
Lemma lem1302678 (n : nat) (m : nat) (p : nat) : (term94 m n p) = (term94 n m p).
Proof. exact (proj2 (@lem1302303 n m p)). Qed.
Lemma lem1302679 (n : nat) (x : nadd) (m : nat) : (term126 n x m) = (term127 n x m).
Proof. exact (@lem1302678 (dest_nadd x m) (dest_nadd x n) (nadd_rinv x m)). Qed.
Lemma lem1302689 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1302690 (n : nat) (x : nadd) (m : nat) : (term118 n x m) = (term128 n x m).
Proof. exact (MK_COMB (@lem1302689 n) (@lem1302679 n x m)). Qed.
Lemma lem1302697 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1302698 (n : nat) (x : nadd) (m : nat) : (term101 n x m) = (term129 n x m).
Proof. exact (MK_COMB (@lem1302697) (@lem1302690 n x m)). Qed.
Lemma lem1302706 (n : nat) (m : nat) (p : nat) : (term94 m n p) = (term94 n m p).
Proof. exact (proj2 (@lem1302303 n m p)). Qed.
Lemma lem1302707 (x : nadd) (n : nat) (m : nat) : (term95 x n m) = (term96 x n m).
Proof. exact (@lem1302706 m (dest_nadd x n) m). Qed.
Lemma lem1302715 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1302716 (m : nat) (x : nadd) (n : nat) : (term97 x n m) = (term59 m x n).
Proof. exact (@lem1302715 m (dest_nadd x n)). Qed.
Lemma lem1302720 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1302721 (m : nat) (x : nadd) (n : nat) : (term96 x n m) = (term98 m x n).
Proof. exact (MK_COMB (@lem1302720 m) (@lem1302716 m x n)). Qed.
Lemma lem1302728 (m : nat) (x : nadd) (n : nat) : (term95 x n m) = (term98 m x n).
Proof. exact (TRANS (@lem1302707 x n m) (@lem1302721 m x n)). Qed.
Lemma lem1302729 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1302730 (m : nat) (x : nadd) (n : nat) : (term99 x n m) = (term100 m x n).
Proof. exact (MK_COMB (@lem1302729 n) (@lem1302728 m x n)). Qed.
Lemma lem1302732 (n : nat) (m : nat) (p : nat) : (term94 m n p) = (term94 n m p).
Proof. exact (proj2 (@lem1302303 n m p)). Qed.
Lemma lem1302733 (m : nat) (x : nadd) (n : nat) : (term100 m x n) = (term130 m x n).
Proof. exact (@lem1302732 m n (term59 m x n)). Qed.
Lemma lem1302741 (n : nat) (m : nat) (p : nat) : (term94 m n p) = (term94 n m p).
Proof. exact (proj2 (@lem1302303 n m p)). Qed.
Lemma lem1302742 (m : nat) (x : nadd) (n : nat) : (term131 m x n) = (term132 m x n).
Proof. exact (@lem1302741 m n (dest_nadd x n)). Qed.
Lemma lem1302752 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1302753 (m : nat) (x : nadd) (n : nat) : (term130 m x n) = (term133 m x n).
Proof. exact (MK_COMB (@lem1302752 m) (@lem1302742 m x n)). Qed.
Lemma lem1302760 (m : nat) (x : nadd) (n : nat) : (term100 m x n) = (term133 m x n).
Proof. exact (TRANS (@lem1302733 m x n) (@lem1302753 m x n)). Qed.
Lemma lem1302761 (m : nat) (x : nadd) (n : nat) : (term99 x n m) = (term133 m x n).
Proof. exact (TRANS (@lem1302730 m x n) (@lem1302760 m x n)). Qed.
Lemma lem1302762 (m : nat) (x : nadd) (n : nat) : (term102 x n m) = (term134 m x n).
Proof. exact (MK_COMB (@lem1302698 n x m) (@lem1302761 m x n)). Qed.
Lemma lem1302763 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1302764 (m : nat) (x : nadd) (n : nat) : (term104 x n m) = (term135 m x n).
Proof. exact (MK_COMB (@lem1302763) (@lem1302762 m x n)). Qed.
Lemma lem1302765 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1302766 (m : nat) (x : nadd) (n : nat) : (term106 x n m) = (term136 m x n).
Proof. exact (MK_COMB (@lem1302765) (@lem1302764 m x n)). Qed.
Lemma lem1302774 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1302775 (m : nat) (x : nadd) (n : nat) : (term54 n x m) = (term54 m x n).
Proof. exact (@lem1302774 (dest_nadd x m) (dest_nadd x n)). Qed.
Lemma lem1302779 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1302780 (m : nat) (x : nadd) (n : nat) : (term108 n x m) = (term137 m x n).
Proof. exact (MK_COMB (@lem1302779 n) (@lem1302775 m x n)). Qed.
Lemma lem1302787 (m : nat) (x : nadd) (n : nat) : (term83 n x m) = (term138 m x n).
Proof. exact (MK_COMB (@lem1302766 m x n) (@lem1302780 m x n)). Qed.
Lemma lem1302788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1302789 (m : nat) (x : nadd) (n : nat) : (term110 n x m) = (term139 m x n).
Proof. exact (MK_COMB (@lem1302788) (@lem1302787 m x n)). Qed.
Lemma lem1302791 (m : nat) (n : nat) (p : nat) : (term112 m n p) = (term94 m n p).
Proof. exact (proj1 (@lem1302303 n m p)). Qed.
Lemma lem1302792 (n : nat) (x : nadd) (m : nat) : (term76 n x m) = (term140 n x m).
Proof. exact (@lem1302791 (dest_nadd x m) (dest_nadd x n) (term53 n x m)). Qed.
Lemma lem1302800 (n : nat) (m : nat) (p : nat) : (term94 m n p) = (term94 n m p).
Proof. exact (proj2 (@lem1302303 n m p)). Qed.
Lemma lem1302801 (n : nat) (x : nadd) (m : nat) : (term141 n x m) = (term142 n x m).
Proof. exact (@lem1302800 n (dest_nadd x n) (nadd_rinv x m)). Qed.
Lemma lem1302811 (x : nadd) (m : nat) : (term116 x m) = (term116 x m).
Proof. exact (eq_refl (term116 x m)). Qed.
Lemma lem1302812 (n : nat) (x : nadd) (m : nat) : (term140 n x m) = (term143 n x m).
Proof. exact (MK_COMB (@lem1302811 x m) (@lem1302801 n x m)). Qed.
Lemma lem1302814 (n : nat) (m : nat) (p : nat) : (term94 m n p) = (term94 n m p).
Proof. exact (proj2 (@lem1302303 n m p)). Qed.
Lemma lem1302815 (n : nat) (x : nadd) (m : nat) : (term143 n x m) = (term128 n x m).
Proof. exact (@lem1302814 n (dest_nadd x m) (term144 n x m)). Qed.
Lemma lem1302831 (n : nat) (x : nadd) (m : nat) : (term140 n x m) = (term128 n x m).
Proof. exact (TRANS (@lem1302812 n x m) (@lem1302815 n x m)). Qed.
Lemma lem1302832 (n : nat) (x : nadd) (m : nat) : (term76 n x m) = (term128 n x m).
Proof. exact (TRANS (@lem1302792 n x m) (@lem1302831 n x m)). Qed.
Lemma lem1302833 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1302834 (n : nat) (x : nadd) (m : nat) : (term145 n x m) = (term129 n x m).
Proof. exact (MK_COMB (@lem1302833) (@lem1302832 n x m)). Qed.
Lemma lem1302836 (m : nat) (n : nat) (p : nat) : (term112 m n p) = (term94 m n p).
Proof. exact (proj1 (@lem1302303 n m p)). Qed.
Lemma lem1302837 (m : nat) (x : nadd) (n : nat) : (term70 m x n) = (term130 m x n).
Proof. exact (@lem1302836 m n (term59 m x n)). Qed.
Lemma lem1302845 (n : nat) (m : nat) (p : nat) : (term94 m n p) = (term94 n m p).
Proof. exact (proj2 (@lem1302303 n m p)). Qed.
Lemma lem1302846 (m : nat) (x : nadd) (n : nat) : (term131 m x n) = (term132 m x n).
Proof. exact (@lem1302845 m n (dest_nadd x n)). Qed.
Lemma lem1302856 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1302857 (m : nat) (x : nadd) (n : nat) : (term130 m x n) = (term133 m x n).
Proof. exact (MK_COMB (@lem1302856 m) (@lem1302846 m x n)). Qed.
Lemma lem1302864 (m : nat) (x : nadd) (n : nat) : (term70 m x n) = (term133 m x n).
Proof. exact (TRANS (@lem1302837 m x n) (@lem1302857 m x n)). Qed.
Lemma lem1302865 (m : nat) (x : nadd) (n : nat) : (term146 m x n) = (term134 m x n).
Proof. exact (MK_COMB (@lem1302834 n x m) (@lem1302864 m x n)). Qed.
Lemma lem1302866 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1302867 (m : nat) (x : nadd) (n : nat) : (term147 m x n) = (term135 m x n).
Proof. exact (MK_COMB (@lem1302866) (@lem1302865 m x n)). Qed.
Lemma lem1302868 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1302869 (m : nat) (x : nadd) (n : nat) : (term148 m x n) = (term136 m x n).
Proof. exact (MK_COMB (@lem1302868) (@lem1302867 m x n)). Qed.
Lemma lem1302871 (m : nat) (n : nat) (p : nat) : (term112 m n p) = (term94 m n p).
Proof. exact (proj1 (@lem1302303 n m p)). Qed.
Lemma lem1302872 (m : nat) (x : nadd) (n : nat) : (term78 m x n) = (term149 m x n).
Proof. exact (@lem1302871 (dest_nadd x m) (dest_nadd x n) n). Qed.
Lemma lem1302880 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem1302881 (x : nadd) (n : nat) : (term150 x n) = (term151 x n).
Proof. exact (@lem1302880 n (dest_nadd x n)). Qed.
Lemma lem1302885 (x : nadd) (m : nat) : (term116 x m) = (term116 x m).
Proof. exact (eq_refl (term116 x m)). Qed.
Lemma lem1302886 (m : nat) (x : nadd) (n : nat) : (term149 m x n) = (term152 m x n).
Proof. exact (MK_COMB (@lem1302885 x m) (@lem1302881 x n)). Qed.
Lemma lem1302888 (n : nat) (m : nat) (p : nat) : (term94 m n p) = (term94 n m p).
Proof. exact (proj2 (@lem1302303 n m p)). Qed.
Lemma lem1302889 (m : nat) (x : nadd) (n : nat) : (term152 m x n) = (term137 m x n).
Proof. exact (@lem1302888 n (dest_nadd x m) (dest_nadd x n)). Qed.
Lemma lem1302899 (m : nat) (x : nadd) (n : nat) : (term149 m x n) = (term137 m x n).
Proof. exact (TRANS (@lem1302886 m x n) (@lem1302889 m x n)). Qed.
Lemma lem1302900 (m : nat) (x : nadd) (n : nat) : (term78 m x n) = (term137 m x n).
Proof. exact (TRANS (@lem1302872 m x n) (@lem1302899 m x n)). Qed.
Lemma lem1302901 (m : nat) (x : nadd) (n : nat) : (term93 m x n) = (term138 m x n).
Proof. exact (MK_COMB (@lem1302869 m x n) (@lem1302900 m x n)). Qed.
Lemma lem1302902 (m : nat) (x : nadd) (n : nat) : ((term83 n x m) = (term93 m x n)) = ((term138 m x n) = (term138 m x n)).
Proof. exact (MK_COMB (@lem1302789 m x n) (@lem1302901 m x n)). Qed.
Lemma lem1302904 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1302905 (x : Prop) : (x = x) = True.
Proof. exact (@lem1302904 Prop x). Qed.
Lemma lem1302906 (m : nat) (x : nadd) (n : nat) : ((term138 m x n) = (term138 m x n)) = True.
Proof. exact (@lem1302905 (term138 m x n)). Qed.
Lemma lem1302907 (m : nat) (x : nadd) (n : nat) : ((term83 n x m) = (term93 m x n)) = True.
Proof. exact (TRANS (@lem1302902 m x n) (@lem1302906 m x n)). Qed.
Lemma lem1302908 (m : nat) (x : nadd) (n : nat) : True = ((term83 n x m) = (term93 m x n)).
Proof. exact (SYM (@lem1302907 m x n)). Qed.
Lemma lem1302909 (m : nat) (x : nadd) (n : nat) : (term83 n x m) = (term93 m x n).
Proof. exact (EQ_MP (@lem1302908 m x n) (@lem0)). Qed.
Lemma lem1302910 (m : nat) (x : nadd) (n : nat) : term153 m x n.
Proof. exact (@lem1302486 m x n (@lem1302909 m x n)). Qed.
Lemma lem1302911 (x : nadd) (n : nat) (m : nat) : term154 x n m.
Proof. exact (@lem1302483 x n m (@lem1302668 x n m)). Qed.
Lemma lem1302912 (n : nat) (x : nadd) (N : nat) (m : nat) (h1 : term49 N x) (h2 : Peano.le N m) : term93 m x n.
Proof. exact (@lem1302910 m x n (@lem1302480 n x N m h1 h2)). Qed.
Lemma lem1302913 (m : nat) (x : nadd) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N n) : term91 x n m.
Proof. exact (@lem1302911 x n m (@lem1302456 m x N n h1 h2)). Qed.
Lemma lem1302914 (x : nadd) (m : nat) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N m) (h3 : Peano.le N n) : term155 m x n.
Proof. exact (conj (@lem1302913 m x N n h1 h3) (@lem1302912 n x N m h1 h2)). Qed.
Lemma lem1302915 (x : nadd) (m : nat) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N m) (h3 : Peano.le N n) : term73 m x n.
Proof. exact (@lem1302433 m x n (@lem1302914 x m N n h1 h2 h3)). Qed.
Lemma lem1302916 (x : nadd) (m : nat) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N m) (h3 : Peano.le N n) : term67 m x n.
Proof. exact (EQ_MP (@lem1302430 m x n) (@lem1302915 x m N n h1 h2 h3)). Qed.
Lemma lem1302917 (x : nadd) (m : nat) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N m) (h3 : Peano.le N n) : term66 x m n.
Proof. exact (EQ_MP (@lem1302420 x m n) (@lem1302916 x m N n h1 h2 h3)). Qed.
Lemma lem1302918 (m : nat) (N : nat) (n : nat) (h1 : term50 m N n) : Peano.le N n.
Proof. exact (proj2 (@lem1302402 m N n h1)). Qed.
Lemma lem1302919 (m : nat) (N : nat) (n : nat) (h1 : term50 m N n) : Peano.le N m.
Proof. exact (proj1 (@lem1302402 m N n h1)). Qed.
Lemma lem1302920 (x : nadd) (m : nat) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N m) (h3 : Peano.le N n) : (Peano.le N n) = (term66 x m n).
Proof. exact (prop_ext (fun h4 : Peano.le N n => @lem1302917 x m N n h1 h2 h3) (fun h4 : term66 x m n => @lem1302403 N n h3)). Qed.
Lemma lem1302921 (x : nadd) (m : nat) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N m) (h3 : Peano.le N n) : term66 x m n.
Proof. exact (EQ_MP (@lem1302920 x m N n h1 h2 h3) (@lem1302403 N n h3)). Qed.
Lemma lem1302922 (x : nadd) (m : nat) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N m) (h3 : Peano.le N n) : (Peano.le N m) = (term66 x m n).
Proof. exact (prop_ext (fun h4 : Peano.le N m => @lem1302921 x m N n h1 h2 h3) (fun h4 : term66 x m n => @lem1302404 N m h2)). Qed.
Lemma lem1302923 (x : nadd) (m : nat) (N : nat) (n : nat) (h1 : term49 N x) (h2 : Peano.le N m) (h3 : Peano.le N n) : term66 x m n.
Proof. exact (EQ_MP (@lem1302922 x m N n h1 h2 h3) (@lem1302404 N m h2)). Qed.
Lemma lem1302924 (x : nadd) (n : nat) (N : nat) (m : nat) (h1 : term49 N x) (h2 : term50 m N n) (h3 : Peano.le N m) : (Peano.le N n) = (term66 x m n).
Proof. exact (prop_ext (fun h4 : Peano.le N n => @lem1302923 x m N n h1 h3 h4) (fun h4 : term66 x m n => @lem1302918 m N n h2)). Qed.
Lemma lem1302925 (x : nadd) (n : nat) (N : nat) (m : nat) (h1 : term49 N x) (h2 : term50 m N n) (h3 : Peano.le N m) : term66 x m n.
Proof. exact (EQ_MP (@lem1302924 x n N m h1 h2 h3) (@lem1302918 m N n h2)). Qed.
Lemma lem1302926 (x : nadd) (m : nat) (N : nat) (n : nat) (h1 : term49 N x) (h2 : term50 m N n) : (Peano.le N m) = (term66 x m n).
Proof. exact (prop_ext (fun h3 : Peano.le N m => @lem1302925 x n N m h1 h2 h3) (fun h3 : term66 x m n => @lem1302919 m N n h2)). Qed.
Lemma lem1302927 (x : nadd) (m : nat) (N : nat) (n : nat) (h1 : term49 N x) (h2 : term50 m N n) : term66 x m n.
Proof. exact (EQ_MP (@lem1302926 x m N n h1 h2) (@lem1302919 m N n h2)). Qed.
Lemma lem1302928 (m : nat) (n : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term156 N x m n.
Proof. exact (fun h0 : term50 m N n => @lem1302927 x m N n h1 h0). Qed.
Lemma lem1302933 (m : nat) (N : nat) (x : nadd) (h1 : term49 N x) : term157 N x m.
Proof. exact (fun n : nat => @lem1302928 m n N x h1). Qed.
Lemma lem1302938 (N : nat) (x : nadd) (h1 : term49 N x) : term158 N x.
Proof. exact (fun m : nat => @lem1302933 m N x h1). Qed.
Lemma lem1302939 (N : nat) (x : nadd) (h1 : term49 N x) : term159 x.
Proof. exact (ex_intro (term160 x) N (@lem1302938 N x h1)). Qed.
Lemma lem1302940 (x : nadd) (h1 : term48 x) : term159 x.
Proof. exact (ex_elim (@lem1302400 x h1) (fun N : nat => fun h0 : term161 x N => @lem1302939 N x h0)). Qed.
Lemma lem1302941 (x : nadd) : term162 x.
Proof. exact (fun h0 : term48 x => @lem1302940 x h0). Qed.
Lemma lem1302942 (x : nadd) (h1 : term47 x) : term159 x.
Proof. exact (@lem1302941 x (@lem1302399 x h1)). Qed.
Lemma lem1302943 (x : nadd) : term163 x.
Proof. exact (fun h0 : term47 x => @lem1302942 x h0). Qed.
Lemma lem1302948 : term164.
Proof. exact (fun x : nadd => @lem1302943 x). Qed.
