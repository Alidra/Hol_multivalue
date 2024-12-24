Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1254597_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1254209 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1254210 (m : nat) (d' : nat) (q : nat) : (term0 m d' q) = (term1 m d' q).
Proof. exact (@lem1254209 m d' q). Qed.
Lemma lem1254212 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254213 (d' : nat) (m : nat) (q : nat) : (term1 m d' q) = (term1 d' m q).
Proof. exact (@lem1254212 d' m q). Qed.
Lemma lem1254220 (d' : nat) (m : nat) (q : nat) : (term0 m d' q) = (term1 d' m q).
Proof. exact (TRANS (@lem1254210 m d' q) (@lem1254213 d' m q)). Qed.
Lemma lem1254224 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1254225 (d' : nat) (m : nat) (q : nat) : (term2 m d' q) = (term3 d' m q).
Proof. exact (MK_COMB (@lem1254224) (@lem1254220 d' m q)). Qed.
Lemma lem1254227 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254228 (m : nat) (q : nat) (d' : nat) : (term1 q m d') = (term1 m q d').
Proof. exact (@lem1254227 m q d'). Qed.
Lemma lem1254236 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1254237 (d' : nat) (q : nat) : (Nat.add q d') = (Nat.add d' q).
Proof. exact (@lem1254236 d' q). Qed.
Lemma lem1254241 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1254242 (m : nat) (d' : nat) (q : nat) : (term1 m q d') = (term1 m d' q).
Proof. exact (MK_COMB (@lem1254241 m) (@lem1254237 d' q)). Qed.
Lemma lem1254244 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254245 (d' : nat) (m : nat) (q : nat) : (term1 m d' q) = (term1 d' m q).
Proof. exact (@lem1254244 d' m q). Qed.
Lemma lem1254255 (d' : nat) (m : nat) (q : nat) : (term1 m q d') = (term1 d' m q).
Proof. exact (TRANS (@lem1254242 m d' q) (@lem1254245 d' m q)). Qed.
Lemma lem1254256 (d' : nat) (m : nat) (q : nat) : (term1 q m d') = (term1 d' m q).
Proof. exact (TRANS (@lem1254228 m q d') (@lem1254255 d' m q)). Qed.
Lemma lem1254257 (d' : nat) (m : nat) (q : nat) : ((term0 m d' q) = (term1 q m d')) = ((term1 d' m q) = (term1 d' m q)).
Proof. exact (MK_COMB (@lem1254225 d' m q) (@lem1254256 d' m q)). Qed.
Lemma lem1254259 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1254260 (x : nat) : (x = x) = True.
Proof. exact (@lem1254259 nat x). Qed.
Lemma lem1254261 (d' : nat) (m : nat) (q : nat) : ((term1 d' m q) = (term1 d' m q)) = True.
Proof. exact (@lem1254260 (term1 d' m q)). Qed.
Lemma lem1254262 (q : nat) (m : nat) (d' : nat) : ((term0 m d' q) = (term1 q m d')) = True.
Proof. exact (TRANS (@lem1254257 d' m q) (@lem1254261 d' m q)). Qed.
Lemma lem1254263 (q : nat) (m : nat) (d' : nat) : True = ((term0 m d' q) = (term1 q m d')).
Proof. exact (SYM (@lem1254262 q m d')). Qed.
Lemma lem1254264 (q : nat) (m : nat) (d' : nat) : (term0 m d' q) = (term1 q m d').
Proof. exact (EQ_MP (@lem1254263 q m d') (@lem0)). Qed.
Lemma lem1254268 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1254269 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term4 m q d' d'' d''') = (term5 m q d' d'' d''').
Proof. exact (@lem1254268 m (Nat.add q d'') (term6 d' d'' d''')). Qed.
Lemma lem1254277 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1254278 (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term7 q d' d'' d''') = (term8 q d' d'' d''').
Proof. exact (@lem1254277 q d'' (term6 d' d'' d''')). Qed.
Lemma lem1254280 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254281 (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term8 q d' d'' d''') = (term9 q d' d'' d''').
Proof. exact (@lem1254280 d'' q (term6 d' d'' d''')). Qed.
Lemma lem1254288 (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term7 q d' d'' d''') = (term9 q d' d'' d''').
Proof. exact (TRANS (@lem1254278 q d' d'' d''') (@lem1254281 q d' d'' d''')). Qed.
Lemma lem1254296 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1254297 (d' : nat) (d'' : nat) (d''' : nat) : (term6 d' d'' d''') = (term10 d' d'' d''').
Proof. exact (@lem1254296 d' d'' (S d''')). Qed.
Lemma lem1254307 (q : nat) : (Nat.add q) = (Nat.add q).
Proof. exact (eq_refl (Nat.add q)). Qed.
Lemma lem1254308 (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term11 q d' d'' d''') = (term12 q d' d'' d''').
Proof. exact (MK_COMB (@lem1254307 q) (@lem1254297 d' d'' d''')). Qed.
Lemma lem1254310 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254311 (d' : nat) (q : nat) (d'' : nat) (d''' : nat) : (term12 q d' d'' d''') = (term12 d' q d'' d''').
Proof. exact (@lem1254310 d' q (term13 d'' d''')). Qed.
Lemma lem1254319 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254320 (d'' : nat) (q : nat) (d''' : nat) : (term10 q d'' d''') = (term10 d'' q d''').
Proof. exact (@lem1254319 d'' q (S d''')). Qed.
Lemma lem1254330 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254331 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term12 d' q d'' d''') = (term12 d' d'' q d''').
Proof. exact (MK_COMB (@lem1254330 d') (@lem1254320 d'' q d''')). Qed.
Lemma lem1254338 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term12 q d' d'' d''') = (term12 d' d'' q d''').
Proof. exact (TRANS (@lem1254311 d' q d'' d''') (@lem1254331 d' d'' q d''')). Qed.
Lemma lem1254339 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term11 q d' d'' d''') = (term12 d' d'' q d''').
Proof. exact (TRANS (@lem1254308 q d' d'' d''') (@lem1254338 d' d'' q d''')). Qed.
Lemma lem1254340 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1254341 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term9 q d' d'' d''') = (term14 d' d'' q d''').
Proof. exact (MK_COMB (@lem1254340 d'') (@lem1254339 d' d'' q d''')). Qed.
Lemma lem1254343 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254344 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term14 d' d'' q d''') = (term15 d' d'' q d''').
Proof. exact (@lem1254343 d' d'' (term10 d'' q d''')). Qed.
Lemma lem1254366 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term9 q d' d'' d''') = (term15 d' d'' q d''').
Proof. exact (TRANS (@lem1254341 d' d'' q d''') (@lem1254344 d' d'' q d''')). Qed.
Lemma lem1254367 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term7 q d' d'' d''') = (term15 d' d'' q d''').
Proof. exact (TRANS (@lem1254288 q d' d'' d''') (@lem1254366 d' d'' q d''')). Qed.
Lemma lem1254368 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1254369 (m : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term5 m q d' d'' d''') = (term16 m d' d'' q d''').
Proof. exact (MK_COMB (@lem1254368 m) (@lem1254367 d' d'' q d''')). Qed.
Lemma lem1254371 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254372 (d' : nat) (m : nat) (d'' : nat) (q : nat) (d''' : nat) : (term16 m d' d'' q d''') = (term16 d' m d'' q d''').
Proof. exact (@lem1254371 d' m (term17 d'' q d''')). Qed.
Lemma lem1254380 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254381 (m : nat) (d'' : nat) (q : nat) (d''' : nat) : (term15 m d'' q d''') = (term14 m d'' q d''').
Proof. exact (@lem1254380 d'' m (term10 d'' q d''')). Qed.
Lemma lem1254389 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254390 (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term12 m d'' q d''') = (term12 d'' m q d''').
Proof. exact (@lem1254389 d'' m (term13 q d''')). Qed.
Lemma lem1254406 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1254407 (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term14 m d'' q d''') = (term18 d'' m q d''').
Proof. exact (MK_COMB (@lem1254406 d'') (@lem1254390 d'' m q d''')). Qed.
Lemma lem1254414 (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term15 m d'' q d''') = (term18 d'' m q d''').
Proof. exact (TRANS (@lem1254381 m d'' q d''') (@lem1254407 d'' m q d''')). Qed.
Lemma lem1254415 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254416 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term16 d' m d'' q d''') = (term19 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1254415 d') (@lem1254414 d'' m q d''')). Qed.
Lemma lem1254423 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term16 m d' d'' q d''') = (term19 d' d'' m q d''').
Proof. exact (TRANS (@lem1254372 d' m d'' q d''') (@lem1254416 d' d'' m q d''')). Qed.
Lemma lem1254424 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term5 m q d' d'' d''') = (term19 d' d'' m q d''').
Proof. exact (TRANS (@lem1254369 m d' d'' q d''') (@lem1254423 d' d'' m q d''')). Qed.
Lemma lem1254425 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term4 m q d' d'' d''') = (term19 d' d'' m q d''').
Proof. exact (TRANS (@lem1254269 m q d' d'' d''') (@lem1254424 d' d'' m q d''')). Qed.
Lemma lem1254426 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1254427 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term20 m q d' d'' d''') = (term21 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1254426) (@lem1254425 d' d'' m q d''')). Qed.
Lemma lem1254429 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254430 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term22 q m d' d'' d''') = (term22 m q d' d'' d''').
Proof. exact (@lem1254429 m q (term23 d' d'' d''')). Qed.
Lemma lem1254438 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254439 (d' : nat) (q : nat) (d'' : nat) (d''' : nat) : (term24 q d' d'' d''') = (term24 d' q d'' d''').
Proof. exact (@lem1254438 d' q (term25 d'' d''')). Qed.
Lemma lem1254447 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254448 (q : nat) (d'' : nat) (d''' : nat) : (term23 q d'' d''') = (term26 q d'' d''').
Proof. exact (@lem1254447 d'' q (term13 d'' d''')). Qed.
Lemma lem1254456 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254457 (d'' : nat) (q : nat) (d''' : nat) : (term10 q d'' d''') = (term10 d'' q d''').
Proof. exact (@lem1254456 d'' q (S d''')). Qed.
Lemma lem1254467 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1254468 (d'' : nat) (q : nat) (d''' : nat) : (term26 q d'' d''') = (term17 d'' q d''').
Proof. exact (MK_COMB (@lem1254467 d'') (@lem1254457 d'' q d''')). Qed.
Lemma lem1254475 (d'' : nat) (q : nat) (d''' : nat) : (term23 q d'' d''') = (term17 d'' q d''').
Proof. exact (TRANS (@lem1254448 q d'' d''') (@lem1254468 d'' q d''')). Qed.
Lemma lem1254476 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254477 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term24 d' q d'' d''') = (term15 d' d'' q d''').
Proof. exact (MK_COMB (@lem1254476 d') (@lem1254475 d'' q d''')). Qed.
Lemma lem1254484 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term24 q d' d'' d''') = (term15 d' d'' q d''').
Proof. exact (TRANS (@lem1254439 d' q d'' d''') (@lem1254477 d' d'' q d''')). Qed.
Lemma lem1254485 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1254486 (m : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term22 m q d' d'' d''') = (term16 m d' d'' q d''').
Proof. exact (MK_COMB (@lem1254485 m) (@lem1254484 d' d'' q d''')). Qed.
Lemma lem1254488 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254489 (d' : nat) (m : nat) (d'' : nat) (q : nat) (d''' : nat) : (term16 m d' d'' q d''') = (term16 d' m d'' q d''').
Proof. exact (@lem1254488 d' m (term17 d'' q d''')). Qed.
Lemma lem1254497 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254498 (m : nat) (d'' : nat) (q : nat) (d''' : nat) : (term15 m d'' q d''') = (term14 m d'' q d''').
Proof. exact (@lem1254497 d'' m (term10 d'' q d''')). Qed.
Lemma lem1254506 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254507 (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term12 m d'' q d''') = (term12 d'' m q d''').
Proof. exact (@lem1254506 d'' m (term13 q d''')). Qed.
Lemma lem1254523 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1254524 (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term14 m d'' q d''') = (term18 d'' m q d''').
Proof. exact (MK_COMB (@lem1254523 d'') (@lem1254507 d'' m q d''')). Qed.
Lemma lem1254531 (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term15 m d'' q d''') = (term18 d'' m q d''').
Proof. exact (TRANS (@lem1254498 m d'' q d''') (@lem1254524 d'' m q d''')). Qed.
Lemma lem1254532 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254533 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term16 d' m d'' q d''') = (term19 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1254532 d') (@lem1254531 d'' m q d''')). Qed.
Lemma lem1254540 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term16 m d' d'' q d''') = (term19 d' d'' m q d''').
Proof. exact (TRANS (@lem1254489 d' m d'' q d''') (@lem1254533 d' d'' m q d''')). Qed.
Lemma lem1254541 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term22 m q d' d'' d''') = (term19 d' d'' m q d''').
Proof. exact (TRANS (@lem1254486 m d' d'' q d''') (@lem1254540 d' d'' m q d''')). Qed.
Lemma lem1254542 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term22 q m d' d'' d''') = (term19 d' d'' m q d''').
Proof. exact (TRANS (@lem1254430 m q d' d'' d''') (@lem1254541 d' d'' m q d''')). Qed.
Lemma lem1254543 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : ((term4 m q d' d'' d''') = (term22 q m d' d'' d''')) = ((term19 d' d'' m q d''') = (term19 d' d'' m q d''')).
Proof. exact (MK_COMB (@lem1254427 d' d'' m q d''') (@lem1254542 d' d'' m q d''')). Qed.
Lemma lem1254545 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1254546 (x : nat) : (x = x) = True.
Proof. exact (@lem1254545 nat x). Qed.
Lemma lem1254547 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : ((term19 d' d'' m q d''') = (term19 d' d'' m q d''')) = True.
Proof. exact (@lem1254546 (term19 d' d'' m q d''')). Qed.
Lemma lem1254548 (q : nat) (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term4 m q d' d'' d''') = (term22 q m d' d'' d''')) = True.
Proof. exact (TRANS (@lem1254543 d' d'' m q d''') (@lem1254547 d' d'' m q d''')). Qed.
Lemma lem1254549 (q : nat) (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : True = ((term4 m q d' d'' d''') = (term22 q m d' d'' d''')).
Proof. exact (SYM (@lem1254548 q m d' d'' d''')). Qed.
Lemma lem1254550 (q : nat) (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term4 m q d' d'' d''') = (term22 q m d' d'' d''').
Proof. exact (EQ_MP (@lem1254549 q m d' d'' d''') (@lem0)). Qed.
Lemma lem1254551 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1254552 (q : nat) (m : nat) (d' : nat) : (term2 m d' q) = (term3 q m d').
Proof. exact (MK_COMB (@lem1254551) (@lem1254264 q m d')). Qed.
Lemma lem1254553 (q : nat) (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term0 m d' q) = (term4 m q d' d'' d''')) = ((term1 q m d') = (term22 q m d' d'' d''')).
Proof. exact (MK_COMB (@lem1254552 q m d') (@lem1254550 q m d' d'' d''')). Qed.
Lemma lem1254554 (m : nat) : term27 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1254555 (m : nat) : (term27 m) = (term28 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem1254556 (m : nat) : term28 m.
Proof. exact (EQ_MP (@lem1254555 m) (@lem1254554 m)). Qed.
Lemma lem1254557 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem1254556 m n). Qed.
Lemma lem1254558 (m : nat) (n : nat) : (term29 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem1254566 (m : nat) : term30 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1254567 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem1254568 (m : nat) : term31 m.
Proof. exact (EQ_MP (@lem1254567 m) (@lem1254566 m)). Qed.
Lemma lem1254569 (m : nat) (n : nat) : term32 m n.
Proof. exact (@lem1254568 m n). Qed.
Lemma lem1254570 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1254571 (m : nat) (n : nat) : term33 m n.
Proof. exact (EQ_MP (@lem1254570 m n) (@lem1254569 m n)). Qed.
Lemma lem1254572 (m : nat) (n : nat) (p : nat) : term34 m n p.
Proof. exact (@lem1254571 m n p). Qed.
Lemma lem1254573 (m : nat) (n : nat) (p : nat) : (term34 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term34 m n p)). Qed.
Lemma lem1254576 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1254573 m n p) (@lem1254572 m n p)). Qed.
Lemma lem1254577 (q : nat) (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term1 q m d') = (term22 q m d' d'' d''')) = ((Nat.add m d') = (term24 m d' d'' d''')).
Proof. exact (@lem1254576 q (Nat.add m d') (term24 m d' d'' d''')). Qed.
Lemma lem1254579 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1254573 m n p) (@lem1254572 m n p)). Qed.
Lemma lem1254580 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((Nat.add m d') = (term24 m d' d'' d''')) = (d' = (term23 d' d'' d''')).
Proof. exact (@lem1254579 m d' (term23 d' d'' d''')). Qed.
Lemma lem1254582 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1254558 m n) (@lem1254557 m n)). Qed.
Lemma lem1254587 (d' : nat) (d'' : nat) (d''' : nat) : (d' = (term23 d' d'' d''')) = ((term25 d'' d''') = (NUMERAL 0)).
Proof. exact (@lem1254582 d' (term25 d'' d''')). Qed.
Lemma lem1254588 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((Nat.add m d') = (term24 m d' d'' d''')) = ((term25 d'' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1254580 m d' d'' d''') (@lem1254587 d' d'' d''')). Qed.
Lemma lem1254589 (q : nat) (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term1 q m d') = (term22 q m d' d'' d''')) = ((term25 d'' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1254577 q m d' d'' d''') (@lem1254588 m d' d'' d''')). Qed.
Lemma lem1254590 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term35 m q d' d'' d''') = (term35 m q d' d'' d''').
Proof. exact (eq_refl (term35 m q d' d'' d''')). Qed.
Lemma lem1254591 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (((term0 m d' q) = (term4 m q d' d'' d''')) = ((term1 q m d') = (term22 q m d' d'' d'''))) = (((term0 m d' q) = (term4 m q d' d'' d''')) = ((term25 d'' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1254590 m q d' d'' d''') (@lem1254589 q m d' d'' d''')). Qed.
Lemma lem1254592 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term0 m d' q) = (term4 m q d' d'' d''')) = ((term25 d'' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1254591 m q d' d'' d''') (@lem1254553 q m d' d'' d''')). Qed.
Lemma lem1254593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1254594 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term36 m q d' d'' d''') = (term37 d'' d''').
Proof. exact (MK_COMB (@lem1254593) (@lem1254592 m q d' d'' d''')). Qed.
Lemma lem1254595 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1254596 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term38 m q d' d'' d''') = (term39 d'' d''').
Proof. exact (MK_COMB (@lem1254594 m q d' d'' d''') (@lem1254595)). Qed.
Lemma lem1254597 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term39 d'' d''') = (term38 m q d' d'' d''').
Proof. exact (SYM (@lem1254596 m q d' d'' d''')). Qed.
