Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIR_SURJECTIVE_term_abbrevs.
Require Import COMMA_DEF_spec.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm44425_spec.
Require Import thm44434_spec.
Lemma lem47439 {A B : Type'} : term0 A B.
Proof. exact (fun a : prod A B => @lem44425 A B a). Qed.
Lemma lem47440 {A B : Type'} (a : prod A B) : term1 A B a.
Proof. exact (@lem47439 A B a). Qed.
Lemma lem47441 {A B : Type'} (a : prod A B) : (term1 A B a) = ((term2 A B a) = a).
Proof. exact (eq_refl (term1 A B a)). Qed.
Lemma lem47443 {A B : Type'} : (@ABS_prod A B) = (@ABS_prod A B).
Proof. exact (eq_refl (@ABS_prod A B)). Qed.
Lemma lem47444 {A B : Type'} : term0 A B.
Proof. exact (fun a : prod A B => @lem44425 A B a). Qed.
Lemma lem47445 {A B : Type'} (a : prod A B) : term1 A B a.
Proof. exact (@lem47444 A B a). Qed.
Lemma lem47446 {A B : Type'} (a : prod A B) : (term1 A B a) = ((term2 A B a) = a).
Proof. exact (eq_refl (term1 A B a)). Qed.
Lemma lem47448 {A B : Type'} : term3 A B.
Proof. exact (fun r : type1413 A B => @lem44434 A B r). Qed.
Lemma lem47449 {A B : Type'} (p : prod A B) : term4 A B p.
Proof. exact (@lem47448 A B (@REP_prod A B p)). Qed.
Lemma lem47450 {A B : Type'} (p : prod A B) : (term4 A B p) = ((term5 A B p) = ((term6 A B p) = (@REP_prod A B p))).
Proof. exact (eq_refl (term4 A B p)). Qed.
Lemma lem47451 {A B : Type'} (p : prod A B) : (term5 A B p) = ((term6 A B p) = (@REP_prod A B p)).
Proof. exact (EQ_MP (@lem47450 A B p) (@lem47449 A B p)). Qed.
Lemma lem47452 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (@lem45466 A B x). Qed.
Lemma lem47453 {A B : Type'} (x : A) : (term7 A B x) = (term8 A B x).
Proof. exact (eq_refl (term7 A B x)). Qed.
Lemma lem47454 {A B : Type'} (x : A) : term8 A B x.
Proof. exact (EQ_MP (@lem47453 A B x) (@lem47452 A B x)). Qed.
Lemma lem47455 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (@lem47454 A B x y). Qed.
Lemma lem47456 {A B : Type'} (x : A) (y : B) : (term9 A B x y) = ((@pair A B x y) = (term10 A B x y)).
Proof. exact (eq_refl (term9 A B x y)). Qed.
Lemma lem47469 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (term10 A B x y).
Proof. exact (EQ_MP (@lem47456 A B x y) (@lem47455 A B x y)). Qed.
Lemma lem47470 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (term10 A B x y).
Proof. exact (@lem47469 A B x y). Qed.
Lemma lem47471 {A B : Type'} (p : prod A B) : (@eq (prod A B) p) = (@eq (prod A B) p).
Proof. exact (eq_refl (@eq (prod A B) p)). Qed.
Lemma lem47472 {A B : Type'} (p : prod A B) (x : A) (y : B) : (p = (@pair A B x y)) = (p = (term10 A B x y)).
Proof. exact (MK_COMB (@lem47471 A B p) (@lem47470 A B x y)). Qed.
Lemma lem47475 {A B : Type'} (p : prod A B) (x : A) : (term11 A B p x) = (term12 A B p x).
Proof. exact (fun_ext (fun y : B => @lem47472 A B p x y)). Qed.
Lemma lem47476 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem47477 {A B : Type'} (p : prod A B) (x : A) : (term13 A B p x) = (term14 A B p x).
Proof. exact (MK_COMB (@lem47476 B) (@lem47475 A B p x)). Qed.
Lemma lem47482 {A B : Type'} (p : prod A B) : (term15 A B p) = (term16 A B p).
Proof. exact (fun_ext (fun x : A => @lem47477 A B p x)). Qed.
Lemma lem47483 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem47484 {A B : Type'} (p : prod A B) : (term17 A B p) = (term18 A B p).
Proof. exact (MK_COMB (@lem47483 A) (@lem47482 A B p)). Qed.
Lemma lem47489 {A B : Type'} (p : prod A B) : (term18 A B p) = (term17 A B p).
Proof. exact (SYM (@lem47484 A B p)). Qed.
Lemma lem47509 {A B : Type'} (a : prod A B) : (term2 A B a) = a.
Proof. exact (EQ_MP (@lem47446 A B a) (@lem47445 A B a)). Qed.
Lemma lem47510 {A B : Type'} (a : prod A B) : (term2 A B a) = a.
Proof. exact (@lem47509 A B a). Qed.
Lemma lem47511 {A B : Type'} (p : prod A B) : (term2 A B p) = p.
Proof. exact (@lem47510 A B p). Qed.
Lemma lem47512 {A B : Type'} : (@REP_prod A B) = (@REP_prod A B).
Proof. exact (eq_refl (@REP_prod A B)). Qed.
Lemma lem47513 {A B : Type'} (p : prod A B) : (term6 A B p) = (@REP_prod A B p).
Proof. exact (MK_COMB (@lem47512 A B) (@lem47511 A B p)). Qed.
Lemma lem47514 {A B : Type'} : (@eq (A -> B -> Prop)) = (@eq (A -> B -> Prop)).
Proof. exact (eq_refl (@eq (A -> B -> Prop))). Qed.
Lemma lem47515 {A B : Type'} (p : prod A B) : (term19 A B p) = (term20 A B p).
Proof. exact (MK_COMB (@lem47514 A B) (@lem47513 A B p)). Qed.
Lemma lem47516 {A B : Type'} (p : prod A B) : (@REP_prod A B p) = (@REP_prod A B p).
Proof. exact (eq_refl (@REP_prod A B p)). Qed.
Lemma lem47517 {A B : Type'} (p : prod A B) : ((term6 A B p) = (@REP_prod A B p)) = ((@REP_prod A B p) = (@REP_prod A B p)).
Proof. exact (MK_COMB (@lem47515 A B p) (@lem47516 A B p)). Qed.
Lemma lem47519 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem47520 {A B : Type'} (x : type1413 A B) : (x = x) = True.
Proof. exact (@lem47519 (type1413 A B) x). Qed.
Lemma lem47521 {A B : Type'} (p : prod A B) : ((@REP_prod A B p) = (@REP_prod A B p)) = True.
Proof. exact (@lem47520 A B (@REP_prod A B p)). Qed.
Lemma lem47522 {A B : Type'} (p : prod A B) : ((term6 A B p) = (@REP_prod A B p)) = True.
Proof. exact (TRANS (@lem47517 A B p) (@lem47521 A B p)). Qed.
Lemma lem47523 {A B : Type'} (p : prod A B) : (term21 A B p) = (term21 A B p).
Proof. exact (eq_refl (term21 A B p)). Qed.
Lemma lem47524 {A B : Type'} (p : prod A B) : ((term5 A B p) = ((term6 A B p) = (@REP_prod A B p))) = ((term5 A B p) = True).
Proof. exact (MK_COMB (@lem47523 A B p) (@lem47522 A B p)). Qed.
Lemma lem47526 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem47527 {A B : Type'} (p : prod A B) : ((term5 A B p) = True) = (term5 A B p).
Proof. exact (@lem47526 (term5 A B p)). Qed.
Lemma lem47538 {A B : Type'} (p : prod A B) : ((term5 A B p) = ((term6 A B p) = (@REP_prod A B p))) = (term5 A B p).
Proof. exact (TRANS (@lem47524 A B p) (@lem47527 A B p)). Qed.
Lemma lem47539 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem47540 {A B : Type'} (p : prod A B) : (term22 A B p) = (term23 A B p).
Proof. exact (MK_COMB (@lem47539) (@lem47538 A B p)). Qed.
Lemma lem47551 {A B : Type'} (p : prod A B) : (term18 A B p) = (term18 A B p).
Proof. exact (eq_refl (term18 A B p)). Qed.
Lemma lem47552 {A B : Type'} (p : prod A B) : (term24 A B p) = (term25 A B p).
Proof. exact (MK_COMB (@lem47540 A B p) (@lem47551 A B p)). Qed.
Lemma lem47555 {A B : Type'} (p : prod A B) : (term25 A B p) = (term24 A B p).
Proof. exact (SYM (@lem47552 A B p)). Qed.
Lemma lem47556 {A B : Type'} (p : prod A B) (h1 : term5 A B p) : term5 A B p.
Proof. exact (h1). Qed.
Lemma lem47557 {A B : Type'} (p : prod A B) (a : A) (h1 : term26 A B p a) : term26 A B p a.
Proof. exact (h1). Qed.
Lemma lem47558 {A B : Type'} (p : prod A B) (a : A) (b : B) (h1 : (@REP_prod A B p) = (@mk_pair A B a b)) : (@REP_prod A B p) = (@mk_pair A B a b).
Proof. exact (h1). Qed.
Lemma lem47559 {A B : Type'} (p : prod A B) (a : A) (b : B) (h1 : (@REP_prod A B p) = (@mk_pair A B a b)) : (@REP_prod A B p) = (@mk_pair A B a b).
Proof. exact (h1). Qed.
Lemma lem47560 {A B : Type'} (p : prod A B) (a : A) (b : B) (h1 : (@REP_prod A B p) = (@mk_pair A B a b)) : (term2 A B p) = (term10 A B a b).
Proof. exact (MK_COMB (@lem47443 A B) (@lem47559 A B p a b h1)). Qed.
Lemma lem47568 {A B : Type'} (a : prod A B) : (term2 A B a) = a.
Proof. exact (EQ_MP (@lem47441 A B a) (@lem47440 A B a)). Qed.
Lemma lem47569 {A B : Type'} (a : prod A B) : (term2 A B a) = a.
Proof. exact (@lem47568 A B a). Qed.
Lemma lem47570 {A B : Type'} (p : prod A B) : (term2 A B p) = p.
Proof. exact (@lem47569 A B p). Qed.
Lemma lem47571 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem47572 {A B : Type'} (p : prod A B) : (term27 A B p) = (@eq (prod A B) p).
Proof. exact (MK_COMB (@lem47571 A B) (@lem47570 A B p)). Qed.
Lemma lem47573 {A B : Type'} (a : A) (b : B) : (term10 A B a b) = (term10 A B a b).
Proof. exact (eq_refl (term10 A B a b)). Qed.
Lemma lem47574 {A B : Type'} (p : prod A B) (a : A) (b : B) : ((term2 A B p) = (term10 A B a b)) = (p = (term10 A B a b)).
Proof. exact (MK_COMB (@lem47572 A B p) (@lem47573 A B a b)). Qed.
Lemma lem47577 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem47578 {A B : Type'} (p : prod A B) (a : A) (b : B) : (term28 A B p a b) = (term29 A B p a b).
Proof. exact (MK_COMB (@lem47577) (@lem47574 A B p a b)). Qed.
Lemma lem47589 {A B : Type'} (p : prod A B) : (term18 A B p) = (term18 A B p).
Proof. exact (eq_refl (term18 A B p)). Qed.
Lemma lem47590 {A B : Type'} (a : A) (b : B) (p : prod A B) : (term30 A B a b p) = (term31 A B a b p).
Proof. exact (MK_COMB (@lem47578 A B p a b) (@lem47589 A B p)). Qed.
Lemma lem47595 {A B : Type'} (a : A) (b : B) (p : prod A B) : (term31 A B a b p) = (term30 A B a b p).
Proof. exact (SYM (@lem47590 A B a b p)). Qed.
Lemma lem47596 {A B : Type'} (p : prod A B) (a : A) (b : B) (h1 : p = (term10 A B a b)) : p = (term10 A B a b).
Proof. exact (h1). Qed.
Lemma lem47597 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (eq_refl (term32 A B)). Qed.
Lemma lem47598 {A B : Type'} (p : prod A B) (a : A) (b : B) (h1 : p = (term10 A B a b)) : (term33 A B p) = (term34 A B a b).
Proof. exact (MK_COMB (@lem47597 A B) (@lem47596 A B p a b h1)). Qed.
Lemma lem47599 {A B : Type'} (a : A) (b : B) : (term34 A B a b) = (term35 A B a b).
Proof. exact (eq_refl (term34 A B a b)). Qed.
Lemma lem47600 {A B : Type'} (p : prod A B) : (term36 A B p) = (term36 A B p).
Proof. exact (eq_refl (term36 A B p)). Qed.
Lemma lem47601 {A B : Type'} (p : prod A B) (a : A) (b : B) : ((term33 A B p) = (term34 A B a b)) = ((term33 A B p) = (term35 A B a b)).
Proof. exact (MK_COMB (@lem47600 A B p) (@lem47599 A B a b)). Qed.
Lemma lem47602 {A B : Type'} (p : prod A B) : (term33 A B p) = (term18 A B p).
Proof. exact (eq_refl (term33 A B p)). Qed.
Lemma lem47603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem47604 {A B : Type'} (p : prod A B) : (term36 A B p) = (term37 A B p).
Proof. exact (MK_COMB (@lem47603) (@lem47602 A B p)). Qed.
Lemma lem47605 {A B : Type'} (a : A) (b : B) : (term35 A B a b) = (term35 A B a b).
Proof. exact (eq_refl (term35 A B a b)). Qed.
Lemma lem47606 {A B : Type'} (p : prod A B) (a : A) (b : B) : ((term33 A B p) = (term35 A B a b)) = ((term18 A B p) = (term35 A B a b)).
Proof. exact (MK_COMB (@lem47604 A B p) (@lem47605 A B a b)). Qed.
Lemma lem47607 {A B : Type'} (p : prod A B) (a : A) (b : B) : ((term33 A B p) = (term34 A B a b)) = ((term18 A B p) = (term35 A B a b)).
Proof. exact (TRANS (@lem47601 A B p a b) (@lem47606 A B p a b)). Qed.
Lemma lem47608 {A B : Type'} (p : prod A B) (a : A) (b : B) (h1 : p = (term10 A B a b)) : (term18 A B p) = (term35 A B a b).
Proof. exact (EQ_MP (@lem47607 A B p a b) (@lem47598 A B p a b h1)). Qed.
Lemma lem47609 {A B : Type'} (p : prod A B) (a : A) (b : B) (h1 : p = (term10 A B a b)) : (term35 A B a b) = (term18 A B p).
Proof. exact (SYM (@lem47608 A B p a b h1)). Qed.
Lemma lem47610 {A B : Type'} (a : A) (b : B) : (term10 A B a b) = (term10 A B a b).
Proof. exact (eq_refl (term10 A B a b)). Qed.
Lemma lem47611 {A B : Type'} (b : B) (a : A) : term38 A B b a.
Proof. exact (ex_intro (term39 A B b a) b (@lem47610 A B a b)). Qed.
Lemma lem47612 {A B : Type'} (a : A) (b : B) : term35 A B a b.
Proof. exact (ex_intro (term40 A B a b) a (@lem47611 A B b a)). Qed.
Lemma lem47613 {A B : Type'} (p : prod A B) (a : A) (b : B) (h1 : p = (term10 A B a b)) : term18 A B p.
Proof. exact (EQ_MP (@lem47609 A B p a b h1) (@lem47612 A B a b)). Qed.
Lemma lem47614 {A B : Type'} (a : A) (b : B) (p : prod A B) : term31 A B a b p.
Proof. exact (fun h0 : p = (term10 A B a b) => @lem47613 A B p a b h0). Qed.
Lemma lem47615 {A B : Type'} (a : A) (b : B) (p : prod A B) : term30 A B a b p.
Proof. exact (EQ_MP (@lem47595 A B a b p) (@lem47614 A B a b p)). Qed.
Lemma lem47616 {A B : Type'} (p : prod A B) (a : A) (b : B) (h1 : (@REP_prod A B p) = (@mk_pair A B a b)) : term18 A B p.
Proof. exact (@lem47615 A B a b p (@lem47560 A B p a b h1)). Qed.
Lemma lem47617 {A B : Type'} (a : A) (b : B) (p : prod A B) : term41 A B a b p.
Proof. exact (fun h0 : (@REP_prod A B p) = (@mk_pair A B a b) => @lem47616 A B p a b h0). Qed.
Lemma lem47618 {A B : Type'} (p : prod A B) (a : A) (b : B) (h1 : (@REP_prod A B p) = (@mk_pair A B a b)) : term18 A B p.
Proof. exact (@lem47617 A B a b p (@lem47558 A B p a b h1)). Qed.
Lemma lem47619 {A B : Type'} (p : prod A B) (a : A) (h1 : term26 A B p a) : term18 A B p.
Proof. exact (ex_elim (@lem47557 A B p a h1) (fun b : B => fun h0 : term42 A B p a b => @lem47618 A B p a b h0)). Qed.
Lemma lem47620 {A B : Type'} (p : prod A B) (h1 : term5 A B p) : term18 A B p.
Proof. exact (ex_elim (@lem47556 A B p h1) (fun a : A => fun h0 : term43 A B p a => @lem47619 A B p a h0)). Qed.
Lemma lem47621 {A B : Type'} (p : prod A B) : term25 A B p.
Proof. exact (fun h0 : term5 A B p => @lem47620 A B p h0). Qed.
Lemma lem47622 {A B : Type'} (p : prod A B) : term24 A B p.
Proof. exact (EQ_MP (@lem47555 A B p) (@lem47621 A B p)). Qed.
Lemma lem47623 {A B : Type'} (p : prod A B) : term18 A B p.
Proof. exact (@lem47622 A B p (@lem47451 A B p)). Qed.
Lemma lem47624 {A B : Type'} (p : prod A B) : term17 A B p.
Proof. exact (EQ_MP (@lem47489 A B p) (@lem47623 A B p)). Qed.
Lemma lem47629 {A B : Type'} : term44 A B.
Proof. exact (fun p : prod A B => @lem47624 A B p). Qed.
