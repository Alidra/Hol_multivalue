Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm155635_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import thm155311_spec.
Require Import thm155534_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem155535 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem155536 : term1.
Proof. exact (EQ_MP (@lem155535) (@lem155311)). Qed.
Lemma lem155537 : term2.
Proof. exact (@lem155536 term3). Qed.
Lemma lem155538 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem155539 : term4.
Proof. exact (EQ_MP (@lem155538) (@lem155537)). Qed.
Lemma lem155540 (h1 : Nat.div = term5) : Nat.div = term5.
Proof. exact (h1). Qed.
Lemma lem155541 (h1 : Nat.div = term5) : term5 = Nat.div.
Proof. exact (SYM (@lem155540 h1)). Qed.
Lemma lem155542 (h1 : term5 = Nat.div) : term5 = Nat.div.
Proof. exact (h1). Qed.
Lemma lem155543 (h1 : term5 = Nat.div) : Nat.div = term5.
Proof. exact (SYM (@lem155542 h1)). Qed.
Lemma lem155544 : (Nat.div = term5) = (term5 = Nat.div).
Proof. exact (prop_ext (fun h1 : Nat.div = term5 => @lem155541 h1) (fun h1 : term5 = Nat.div => @lem155543 h1)). Qed.
Lemma lem155547 : term5 = Nat.div.
Proof. exact (EQ_MP (@lem155544) (@lem155534)). Qed.
Lemma lem155548 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem155549 (m : nat) : (term6 m) = (Nat.div m).
Proof. exact (MK_COMB (@lem155547) (@lem155548 m)). Qed.
Lemma lem155550 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem155551 (m : nat) (n : nat) : (term7 m n) = (Nat.div m n).
Proof. exact (MK_COMB (@lem155549 m) (@lem155550 n)). Qed.
Lemma lem155552 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem155553 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem155552) (@lem155551 m n)). Qed.
Lemma lem155554 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem155555 (m : nat) (n : nat) : ((term7 m n) = (NUMERAL 0)) = ((Nat.div m n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem155553 m n) (@lem155554)). Qed.
Lemma lem155556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem155557 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem155556) (@lem155555 m n)). Qed.
Lemma lem155558 (r : type1606) (n : nat) (m : nat) : ((r m n) = m) = ((r m n) = m).
Proof. exact (eq_refl ((r m n) = m)). Qed.
Lemma lem155559 (r : type1606) (n : nat) (m : nat) : (term12 r n m) = (term13 r n m).
Proof. exact (MK_COMB (@lem155557 m n) (@lem155558 r n m)). Qed.
Lemma lem155560 (n : nat) : (term14 n) = (term14 n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem155561 (r : type1606) (n : nat) (m : nat) : (term15 r n m) = (term16 r n m).
Proof. exact (MK_COMB (@lem155560 n) (@lem155559 r n m)). Qed.
Lemma lem155563 : term5 = Nat.div.
Proof. exact (EQ_MP (@lem155544) (@lem155534)). Qed.
Lemma lem155564 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem155565 (m : nat) : (term6 m) = (Nat.div m).
Proof. exact (MK_COMB (@lem155563) (@lem155564 m)). Qed.
Lemma lem155566 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem155567 (m : nat) (n : nat) : (term7 m n) = (Nat.div m n).
Proof. exact (MK_COMB (@lem155565 m) (@lem155566 n)). Qed.
Lemma lem155568 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem155569 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem155568) (@lem155567 m n)). Qed.
Lemma lem155570 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem155571 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem155569 m n) (@lem155570 n)). Qed.
Lemma lem155572 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem155573 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem155572) (@lem155571 m n)). Qed.
Lemma lem155574 (r : type1606) (m : nat) (n : nat) : (r m n) = (r m n).
Proof. exact (eq_refl (r m n)). Qed.
Lemma lem155575 (r : type1606) (m : nat) (n : nat) : (term23 r m n) = (term24 r m n).
Proof. exact (MK_COMB (@lem155573 m n) (@lem155574 r m n)). Qed.
Lemma lem155576 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem155577 (r : type1606) (m : nat) (n : nat) : (m = (term23 r m n)) = (m = (term24 r m n)).
Proof. exact (MK_COMB (@lem155576 m) (@lem155575 r m n)). Qed.
Lemma lem155578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem155579 (r : type1606) (m : nat) (n : nat) : (term25 r m n) = (term26 r m n).
Proof. exact (MK_COMB (@lem155578) (@lem155577 r m n)). Qed.
Lemma lem155580 (r : type1606) (m : nat) (n : nat) : (term27 r m n) = (term27 r m n).
Proof. exact (eq_refl (term27 r m n)). Qed.
Lemma lem155581 (r : type1606) (m : nat) (n : nat) : (term28 r m n) = (term29 r m n).
Proof. exact (MK_COMB (@lem155579 r m n) (@lem155580 r m n)). Qed.
Lemma lem155582 (r : type1606) (m : nat) (n : nat) : (term30 r m n) = (term31 r m n).
Proof. exact (MK_COMB (@lem155561 r n m) (@lem155581 r m n)). Qed.
Lemma lem155583 (r : type1606) (m : nat) : (term32 r m) = (term33 r m).
Proof. exact (fun_ext (fun n : nat => @lem155582 r m n)). Qed.
Lemma lem155584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155585 (r : type1606) (m : nat) : (term34 r m) = (term35 r m).
Proof. exact (MK_COMB (@lem155584) (@lem155583 r m)). Qed.
Lemma lem155586 (r : type1606) : (term36 r) = (term37 r).
Proof. exact (fun_ext (fun m : nat => @lem155585 r m)). Qed.
Lemma lem155587 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155588 (r : type1606) : (term38 r) = (term39 r).
Proof. exact (MK_COMB (@lem155587) (@lem155586 r)). Qed.
Lemma lem155589 : term40 = term41.
Proof. exact (fun_ext (fun r : type1606 => @lem155588 r)). Qed.
Lemma lem155590 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem155591 : term4 = term42.
Proof. exact (MK_COMB (@lem155590) (@lem155589)). Qed.
Lemma lem155592 : term42.
Proof. exact (EQ_MP (@lem155591) (@lem155539)). Qed.
Lemma lem155593 : term43.
Proof. exact (fun _3087 : type1674 => @lem155592). Qed.
Lemma lem155594 {A B : Type'} (P : type1413 A B) : term44 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem155595 {A B : Type'} (P : type1413 A B) : (term44 A B P) = ((term45 A B P) = (term46 A B P)).
Proof. exact (eq_refl (term44 A B P)). Qed.
Lemma lem155598 {A B : Type'} (P : type1413 A B) : (term45 A B P) = (term46 A B P).
Proof. exact (EQ_MP (@lem155595 A B P) (@lem155594 A B P)). Qed.
Lemma lem155599 (P : type1300) : (term47 P) = (term48 P).
Proof. exact (@lem155598 type1674 type1606 P). Qed.
Lemma lem155600 : term49 = term50.
Proof. exact (@lem155599 term51). Qed.
Lemma lem155601 (_3087 : type1674) : (term52 _3087) = term41.
Proof. exact (eq_refl (term52 _3087)). Qed.
Lemma lem155602 (r : type1606) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem155603 (_3087 : type1674) (r : type1606) : (term53 _3087 r) = (term54 r).
Proof. exact (MK_COMB (@lem155601 _3087) (@lem155602 r)). Qed.
Lemma lem155604 (r : type1606) : (term54 r) = (term39 r).
Proof. exact (eq_refl (term54 r)). Qed.
Lemma lem155605 (_3087 : type1674) (r : type1606) : (term53 _3087 r) = (term39 r).
Proof. exact (TRANS (@lem155603 _3087 r) (@lem155604 r)). Qed.
Lemma lem155606 (_3087 : type1674) : (term55 _3087) = term41.
Proof. exact (fun_ext (fun r : type1606 => @lem155605 _3087 r)). Qed.
Lemma lem155607 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem155608 (_3087 : type1674) : (term56 _3087) = term42.
Proof. exact (MK_COMB (@lem155607) (@lem155606 _3087)). Qed.
Lemma lem155609 : term57 = term58.
Proof. exact (fun_ext (fun _3087 : type1674 => @lem155608 _3087)). Qed.
Lemma lem155610 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem155611 : term49 = term43.
Proof. exact (MK_COMB (@lem155610) (@lem155609)). Qed.
Lemma lem155612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem155613 : term59 = term60.
Proof. exact (MK_COMB (@lem155612) (@lem155611)). Qed.
Lemma lem155614 (_3087 : type1674) : (term52 _3087) = term41.
Proof. exact (eq_refl (term52 _3087)). Qed.
Lemma lem155615 (r : type1306) (_3087 : type1674) : (r _3087) = (r _3087).
Proof. exact (eq_refl (r _3087)). Qed.
Lemma lem155616 (r : type1306) (_3087 : type1674) : (term61 r _3087) = (term62 r _3087).
Proof. exact (MK_COMB (@lem155614 _3087) (@lem155615 r _3087)). Qed.
Lemma lem155617 (r : type1306) (_3087 : type1674) : (term62 r _3087) = (term63 r _3087).
Proof. exact (eq_refl (term62 r _3087)). Qed.
Lemma lem155618 (r : type1306) (_3087 : type1674) : (term61 r _3087) = (term63 r _3087).
Proof. exact (TRANS (@lem155616 r _3087) (@lem155617 r _3087)). Qed.
Lemma lem155619 (r : type1306) : (term64 r) = (term65 r).
Proof. exact (fun_ext (fun _3087 : type1674 => @lem155618 r _3087)). Qed.
Lemma lem155620 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem155621 (r : type1306) : (term66 r) = (term67 r).
Proof. exact (MK_COMB (@lem155620) (@lem155619 r)). Qed.
Lemma lem155622 : term68 = term69.
Proof. exact (fun_ext (fun r : type1306 => @lem155621 r)). Qed.
Lemma lem155623 : (@ex ((prod nat (prod nat nat)) -> nat -> nat -> nat)) = (@ex ((prod nat (prod nat nat)) -> nat -> nat -> nat)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat nat)) -> nat -> nat -> nat))). Qed.
Lemma lem155624 : term50 = term70.
Proof. exact (MK_COMB (@lem155623) (@lem155622)). Qed.
Lemma lem155625 : (term49 = term50) = (term43 = term70).
Proof. exact (MK_COMB (@lem155613) (@lem155624)). Qed.
Lemma lem155626 : term43 = term70.
Proof. exact (EQ_MP (@lem155625) (@lem155600)). Qed.
Lemma lem155627 : term70.
Proof. exact (EQ_MP (@lem155626) (@lem155593)). Qed.
Lemma lem155629 {A : Type'} : (@ex A) = (term71 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem155630 : (@ex ((prod nat (prod nat nat)) -> nat -> nat -> nat)) = term72.
Proof. exact (@lem155629 type1306). Qed.
Lemma lem155631 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem155632 : term70 = term73.
Proof. exact (MK_COMB (@lem155630) (@lem155631)). Qed.
Lemma lem155633 : term73 = term74.
Proof. exact (eq_refl term73). Qed.
Lemma lem155634 : term70 = term74.
Proof. exact (TRANS (@lem155632) (@lem155633)). Qed.
Lemma lem155635 : term74.
Proof. exact (EQ_MP (@lem155634) (@lem155627)). Qed.
