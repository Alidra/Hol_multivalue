Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7926528_term_abbrevs.
Require Import thm7925100_spec.
Require Import thm7925101_spec.
Require Import thm7925131_spec.
Require Import thm7925135_spec.
Require Import thm7926442_spec.
Lemma lem7926443 {A : Type'} (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term0 A _103783')) : term1 A _103783' tybit0' P.
Proof. exact (@lem7925101 A tybit0' _103783' h1 (term2 A tybit0' P)). Qed.
Lemma lem7926444 {A : Type'} (_103783' : type45 A) (tybit0' : type1331 A) (P : type1345 A) : (term1 A _103783' tybit0' P) = (term3 A _103783' tybit0' P).
Proof. exact (eq_refl (term1 A _103783' tybit0' P)). Qed.
Lemma lem7926445 {A : Type'} (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term0 A _103783')) : term3 A _103783' tybit0' P.
Proof. exact (EQ_MP (@lem7926444 A _103783' tybit0' P) (@lem7926443 A P tybit0' _103783' h1)). Qed.
Lemma lem7926447 {A : Type'} (tybit0' : type1331 A) (P : type1345 A) (_103783' : type45 A) (a : finite_sum A A) : (term4 A tybit0' P _103783' a) = (term5 A tybit0' P _103783' a).
Proof. exact (eq_refl (term4 A tybit0' P _103783' a)). Qed.
Lemma lem7926448 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term0 A _103783')) : term6 A tybit0' _103783' a.
Proof. exact (@lem7925100 A tybit0' _103783' h1 a). Qed.
Lemma lem7926449 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (a : finite_sum A A) : (term6 A tybit0' _103783' a) = (term7 A tybit0' _103783' a).
Proof. exact (eq_refl (term6 A tybit0' _103783' a)). Qed.
Lemma lem7926452 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term0 A _103783')) : term7 A tybit0' _103783' a.
Proof. exact (EQ_MP (@lem7926449 A tybit0' _103783' a) (@lem7926448 A a tybit0' _103783' h1)). Qed.
Lemma lem7926453 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term0 A _103783')) : term7 A tybit0' _103783' a.
Proof. exact (@lem7926452 A a tybit0' _103783' h1). Qed.
Lemma lem7926455 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) : (term9 A _103783' a) = (@_103783 A a).
Proof. exact (SYM (@lem7926442 A a _103783' h1)). Qed.
Lemma lem7926456 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) : (term9 A _103783' a) = (@_103783 A a).
Proof. exact (@lem7926455 A a _103783' h1). Qed.
Lemma lem7926457 {A : Type'} (P : type1345 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7926458 {A : Type'} (P : type1345 A) (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) : (term10 A P _103783' a) = (term11 A P a).
Proof. exact (MK_COMB (@lem7926457 A P) (@lem7926456 A a _103783' h1)). Qed.
Lemma lem7926459 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (a : finite_sum A A) : (term12 A tybit0' _103783' a) = (term12 A tybit0' _103783' a).
Proof. exact (eq_refl (term12 A tybit0' _103783' a)). Qed.
Lemma lem7926460 {A : Type'} (tybit0' : type1331 A) (P : type1345 A) (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) : (term5 A tybit0' P _103783' a) = (term13 A tybit0' _103783' P a).
Proof. exact (MK_COMB (@lem7926459 A tybit0' _103783' a) (@lem7926458 A P a _103783' h1)). Qed.
Lemma lem7926461 {A : Type'} (tybit0' : type1331 A) (P : type1345 A) (_103783' : type45 A) (a : finite_sum A A) : (term14 A tybit0' P _103783' a) = (term14 A tybit0' P _103783' a).
Proof. exact (eq_refl (term14 A tybit0' P _103783' a)). Qed.
Lemma lem7926462 {A : Type'} (tybit0' : type1331 A) (P : type1345 A) (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) : ((term4 A tybit0' P _103783' a) = (term5 A tybit0' P _103783' a)) = ((term4 A tybit0' P _103783' a) = (term13 A tybit0' _103783' P a)).
Proof. exact (MK_COMB (@lem7926461 A tybit0' P _103783' a) (@lem7926460 A tybit0' P a _103783' h1)). Qed.
Lemma lem7926463 {A : Type'} (tybit0' : type1331 A) (P : type1345 A) (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) : (term4 A tybit0' P _103783' a) = (term13 A tybit0' _103783' P a).
Proof. exact (EQ_MP (@lem7926462 A tybit0' P a _103783' h1) (@lem7926447 A tybit0' P _103783' a)). Qed.
Lemma lem7926464 {A : Type'} (P : type1345 A) (h1 : term15 A P) : term15 A P.
Proof. exact (h1). Qed.
Lemma lem7926465 {A : Type'} (a : finite_sum A A) (P : type1345 A) (h1 : term15 A P) : term16 A P a.
Proof. exact (@lem7926464 A P h1 a). Qed.
Lemma lem7926466 {A : Type'} (P : type1345 A) (a : finite_sum A A) : (term16 A P a) = (term11 A P a).
Proof. exact (eq_refl (term16 A P a)). Qed.
Lemma lem7926467 {A : Type'} (a : finite_sum A A) (P : type1345 A) (h1 : term15 A P) : term11 A P a.
Proof. exact (EQ_MP (@lem7926466 A P a) (@lem7926465 A a P h1)). Qed.
Lemma lem7926468 {A : Type'} (a : finite_sum A A) (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : tybit0' = (term0 A _103783')) : term13 A tybit0' _103783' P a.
Proof. exact (conj (@lem7926453 A a tybit0' _103783' h2) (@lem7926467 A a P h1)). Qed.
Lemma lem7926469 {A : Type'} (tybit0' : type1331 A) (P : type1345 A) (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) : (term13 A tybit0' _103783' P a) = (term4 A tybit0' P _103783' a).
Proof. exact (SYM (@lem7926463 A tybit0' P a _103783' h1)). Qed.
Lemma lem7926470 {A : Type'} (a : finite_sum A A) (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : term4 A tybit0' P _103783' a.
Proof. exact (EQ_MP (@lem7926469 A tybit0' P a _103783' h2) (@lem7926468 A a P tybit0' _103783' h1 h3)). Qed.
Lemma lem7926471 {A : Type'} (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : term17 A tybit0' P _103783'.
Proof. exact (fun a : finite_sum A A => @lem7926470 A a P tybit0' _103783' h1 h2 h3). Qed.
Lemma lem7926472 {A : Type'} (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) (h2 : tybit0' = (term0 A _103783')) : term18 A tybit0' P _103783'.
Proof. exact (fun h0 : term15 A P => @lem7926471 A P tybit0' _103783' h0 h1 h2). Qed.
Lemma lem7926473 {A : Type'} (P : type1345 A) (h1 : term15 A P) : term15 A P.
Proof. exact (h1). Qed.
Lemma lem7926474 {A : Type'} (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : term17 A tybit0' P _103783'.
Proof. exact (@lem7926472 A P tybit0' _103783' h2 h3 (@lem7926473 A P h1)). Qed.
Lemma lem7926475 {A : Type'} (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : term19 A tybit0' P.
Proof. exact (@lem7926445 A P tybit0' _103783' h3 (@lem7926474 A P tybit0' _103783' h1 h2 h3)). Qed.
Lemma lem7926476 {A : Type'} (x : tybit0 A) (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : term20 A tybit0' P x.
Proof. exact (@lem7926475 A P tybit0' _103783' h1 h2 h3 (@_dest_tybit0 A x)). Qed.
Lemma lem7926477 {A : Type'} (tybit0' : type1331 A) (P : type1345 A) (x : tybit0 A) : (term20 A tybit0' P x) = (term21 A tybit0' P x).
Proof. exact (eq_refl (term20 A tybit0' P x)). Qed.
Lemma lem7926478 {A : Type'} (x : tybit0 A) (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : term21 A tybit0' P x.
Proof. exact (EQ_MP (@lem7926477 A tybit0' P x) (@lem7926476 A x P tybit0' _103783' h1 h2 h3)). Qed.
Lemma lem7926480 {A : Type'} (r : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) (h2 : tybit0' = (term0 A _103783')) : (tybit0' r) = ((term22 A r) = r).
Proof. exact (TRANS (@lem7925135 A r tybit0' _103783' h1 h2) (@lem7925131 A r)). Qed.
Lemma lem7926481 {A : Type'} (r : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) (h2 : tybit0' = (term0 A _103783')) : (tybit0' r) = ((term22 A r) = r).
Proof. exact (@lem7926480 A r tybit0' _103783' h1 h2). Qed.
Lemma lem7926482 {A : Type'} (x : tybit0 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) (h2 : tybit0' = (term0 A _103783')) : (term23 A tybit0' x) = ((term24 A x) = (@_dest_tybit0 A x)).
Proof. exact (@lem7926481 A (@_dest_tybit0 A x) tybit0' _103783' h1 h2). Qed.
Lemma lem7926483 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7926484 {A : Type'} (x : tybit0 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) (h2 : tybit0' = (term0 A _103783')) : (term25 A tybit0' x) = (term26 A x).
Proof. exact (MK_COMB (@lem7926483) (@lem7926482 A x tybit0' _103783' h1 h2)). Qed.
Lemma lem7926485 {A : Type'} (tybit0' : type1331 A) (P : type1345 A) (x : tybit0 A) : (term27 A tybit0' P x) = (term27 A tybit0' P x).
Proof. exact (eq_refl (term27 A tybit0' P x)). Qed.
Lemma lem7926486 {A : Type'} (P : type1345 A) (x : tybit0 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) (h2 : tybit0' = (term0 A _103783')) : (term21 A tybit0' P x) = (term28 A tybit0' P x).
Proof. exact (MK_COMB (@lem7926484 A x tybit0' _103783' h1 h2) (@lem7926485 A tybit0' P x)). Qed.
Lemma lem7926487 {A : Type'} (x : tybit0 A) (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : term28 A tybit0' P x.
Proof. exact (EQ_MP (@lem7926486 A P x tybit0' _103783' h2 h3) (@lem7926478 A x P tybit0' _103783' h1 h2 h3)). Qed.
Lemma lem7926489 {A : Type'} (a : tybit0 A) : (term29 A a) = a.
Proof. exact (@axiom_37 A a). Qed.
Lemma lem7926490 {A : Type'} (a : tybit0 A) : (term29 A a) = a.
Proof. exact (@lem7926489 A a). Qed.
Lemma lem7926491 {A : Type'} (x : tybit0 A) : (term29 A x) = x.
Proof. exact (@lem7926490 A x). Qed.
Lemma lem7926492 {A : Type'} : (@_dest_tybit0 A) = (@_dest_tybit0 A).
Proof. exact (eq_refl (@_dest_tybit0 A)). Qed.
Lemma lem7926493 {A : Type'} (x : tybit0 A) : (term24 A x) = (@_dest_tybit0 A x).
Proof. exact (MK_COMB (@lem7926492 A) (@lem7926491 A x)). Qed.
Lemma lem7926494 {A : Type'} : (@eq (recspace (finite_sum A A))) = (@eq (recspace (finite_sum A A))).
Proof. exact (eq_refl (@eq (recspace (finite_sum A A)))). Qed.
Lemma lem7926495 {A : Type'} (x : tybit0 A) : (term30 A x) = (term31 A x).
Proof. exact (MK_COMB (@lem7926494 A) (@lem7926493 A x)). Qed.
Lemma lem7926496 {A : Type'} (x : tybit0 A) : (@_dest_tybit0 A x) = (@_dest_tybit0 A x).
Proof. exact (eq_refl (@_dest_tybit0 A x)). Qed.
Lemma lem7926497 {A : Type'} (x : tybit0 A) : ((term24 A x) = (@_dest_tybit0 A x)) = ((@_dest_tybit0 A x) = (@_dest_tybit0 A x)).
Proof. exact (MK_COMB (@lem7926495 A x) (@lem7926496 A x)). Qed.
Lemma lem7926498 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7926499 {A : Type'} (x : tybit0 A) : (term26 A x) = (term32 A x).
Proof. exact (MK_COMB (@lem7926498) (@lem7926497 A x)). Qed.
Lemma lem7926500 {A : Type'} (tybit0' : type1331 A) (P : type1345 A) (x : tybit0 A) : (term27 A tybit0' P x) = (term27 A tybit0' P x).
Proof. exact (eq_refl (term27 A tybit0' P x)). Qed.
Lemma lem7926501 {A : Type'} (tybit0' : type1331 A) (P : type1345 A) (x : tybit0 A) : (term28 A tybit0' P x) = (term33 A tybit0' P x).
Proof. exact (MK_COMB (@lem7926499 A x) (@lem7926500 A tybit0' P x)). Qed.
Lemma lem7926502 {A : Type'} (x : tybit0 A) (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : term33 A tybit0' P x.
Proof. exact (EQ_MP (@lem7926501 A tybit0' P x) (@lem7926487 A x P tybit0' _103783' h1 h2 h3)). Qed.
Lemma lem7926503 {A : Type'} (x : tybit0 A) : (@_dest_tybit0 A x) = (@_dest_tybit0 A x).
Proof. exact (eq_refl (@_dest_tybit0 A x)). Qed.
Lemma lem7926504 {A : Type'} (x : tybit0 A) (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : term27 A tybit0' P x.
Proof. exact (@lem7926502 A x P tybit0' _103783' h1 h2 h3 (@lem7926503 A x)). Qed.
Lemma lem7926505 {A : Type'} (tybit0' : type1331 A) (P : type1345 A) (x : tybit0 A) : (term27 A tybit0' P x) = (term34 A tybit0' P x).
Proof. exact (eq_refl (term27 A tybit0' P x)). Qed.
Lemma lem7926506 {A : Type'} (x : tybit0 A) (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : term34 A tybit0' P x.
Proof. exact (EQ_MP (@lem7926505 A tybit0' P x) (@lem7926504 A x P tybit0' _103783' h1 h2 h3)). Qed.
Lemma lem7926507 {A : Type'} (x : tybit0 A) (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : term35 A P x.
Proof. exact (proj2 (@lem7926506 A x P tybit0' _103783' h1 h2 h3)). Qed.
Lemma lem7926509 {A : Type'} (a : tybit0 A) : (term29 A a) = a.
Proof. exact (@axiom_37 A a). Qed.
Lemma lem7926510 {A : Type'} (a : tybit0 A) : (term29 A a) = a.
Proof. exact (@lem7926509 A a). Qed.
Lemma lem7926511 {A : Type'} (x : tybit0 A) : (term29 A x) = x.
Proof. exact (@lem7926510 A x). Qed.
Lemma lem7926512 {A : Type'} (P : type1345 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7926513 {A : Type'} (P : type1345 A) (x : tybit0 A) : (term35 A P x) = (P x).
Proof. exact (MK_COMB (@lem7926512 A P) (@lem7926511 A x)). Qed.
Lemma lem7926514 {A : Type'} (x : tybit0 A) (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : P x.
Proof. exact (EQ_MP (@lem7926513 A P x) (@lem7926507 A x P tybit0' _103783' h1 h2 h3)). Qed.
Lemma lem7926515 {A : Type'} (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : term15 A P) (h2 : _103783' = (term8 A)) (h3 : tybit0' = (term0 A _103783')) : term36 A P.
Proof. exact (fun x : tybit0 A => @lem7926514 A x P tybit0' _103783' h1 h2 h3). Qed.
Lemma lem7926516 {A : Type'} (P : type1345 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) (h2 : tybit0' = (term0 A _103783')) : term37 A P.
Proof. exact (fun h0 : term15 A P => @lem7926515 A P tybit0' _103783' h0 h1 h2). Qed.
Lemma lem7926517 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) (h2 : tybit0' = (term0 A _103783')) : term38 A.
Proof. exact (fun P : type1345 A => @lem7926516 A P tybit0' _103783' h1 h2). Qed.
Lemma lem7926518 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term8 A)) : term39 A tybit0' _103783'.
Proof. exact (fun h0 : tybit0' = (term0 A _103783') => @lem7926517 A tybit0' _103783' h1 h0). Qed.
Lemma lem7926519 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (eq_refl (term8 A)). Qed.
Lemma lem7926520 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) : term40 A tybit0' _103783'.
Proof. exact (fun h0 : _103783' = (term8 A) => @lem7926518 A tybit0' _103783' h0). Qed.
Lemma lem7926521 {A : Type'} (tybit0' : type1331 A) : term41 A tybit0'.
Proof. exact (@lem7926520 A tybit0' (term8 A)). Qed.
Lemma lem7926522 {A : Type'} (tybit0' : type1331 A) : term42 A tybit0'.
Proof. exact (@lem7926521 A tybit0' (@lem7926519 A)). Qed.
Lemma lem7926523 {A : Type'} (tybit0' : type1331 A) (h1 : tybit0' = (term43 A)) : tybit0' = (term43 A).
Proof. exact (h1). Qed.
Lemma lem7926524 {A : Type'} (tybit0' : type1331 A) (h1 : tybit0' = (term43 A)) : term38 A.
Proof. exact (@lem7926522 A tybit0' (@lem7926523 A tybit0' h1)). Qed.
Lemma lem7926525 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (eq_refl (term43 A)). Qed.
Lemma lem7926526 {A : Type'} (tybit0' : type1331 A) : term42 A tybit0'.
Proof. exact (fun h0 : tybit0' = (term43 A) => @lem7926524 A tybit0' h0). Qed.
Lemma lem7926527 {A : Type'} : term44 A.
Proof. exact (@lem7926526 A (term43 A)). Qed.
Lemma lem7926528 {A : Type'} : term38 A.
Proof. exact (@lem7926527 A (@lem7926525 A)). Qed.
