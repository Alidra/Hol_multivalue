Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1251719_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_LCANCEL_0_spec.
Require Import thm0_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1251507 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1251508 (d' : nat) (d'' : nat) (d''' : nat) : (term2 d' d'' d''') = (term3 d' d'' d''').
Proof. exact (@lem1251507 d' d'' (S d''')). Qed.
Lemma lem1251518 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1251519 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term4 m d' d'' d''') = (term5 m d' d'' d''').
Proof. exact (MK_COMB (@lem1251518 m) (@lem1251508 d' d'' d''')). Qed.
Lemma lem1251521 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251522 (d' : nat) (m : nat) (d'' : nat) (d''' : nat) : (term5 m d' d'' d''') = (term5 d' m d'' d''').
Proof. exact (@lem1251521 d' m (term6 d'' d''')). Qed.
Lemma lem1251530 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251531 (d'' : nat) (m : nat) (d''' : nat) : (term3 m d'' d''') = (term3 d'' m d''').
Proof. exact (@lem1251530 d'' m (S d''')). Qed.
Lemma lem1251541 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251542 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term5 d' m d'' d''') = (term5 d' d'' m d''').
Proof. exact (MK_COMB (@lem1251541 d') (@lem1251531 d'' m d''')). Qed.
Lemma lem1251549 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term5 m d' d'' d''') = (term5 d' d'' m d''').
Proof. exact (TRANS (@lem1251522 d' m d'' d''') (@lem1251542 d' d'' m d''')). Qed.
Lemma lem1251550 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term4 m d' d'' d''') = (term5 d' d'' m d''').
Proof. exact (TRANS (@lem1251519 m d' d'' d''') (@lem1251549 d' d'' m d''')). Qed.
Lemma lem1251551 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1251552 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term7 m d' d'' d''') = (term8 d' d'' m d''').
Proof. exact (MK_COMB (@lem1251551) (@lem1251550 d' d'' m d''')). Qed.
Lemma lem1251554 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251555 (d'' : nat) (m : nat) (d' : nat) (d''' : nat) : (term5 m d'' d' d''') = (term5 d'' m d' d''').
Proof. exact (@lem1251554 d'' m (term6 d' d''')). Qed.
Lemma lem1251563 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251564 (d' : nat) (m : nat) (d''' : nat) : (term3 m d' d''') = (term3 d' m d''').
Proof. exact (@lem1251563 d' m (S d''')). Qed.
Lemma lem1251574 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1251575 (d'' : nat) (d' : nat) (m : nat) (d''' : nat) : (term5 d'' m d' d''') = (term5 d'' d' m d''').
Proof. exact (MK_COMB (@lem1251574 d'') (@lem1251564 d' m d''')). Qed.
Lemma lem1251577 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251578 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term5 d'' d' m d''') = (term5 d' d'' m d''').
Proof. exact (@lem1251577 d' d'' (term6 m d''')). Qed.
Lemma lem1251594 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term5 d'' m d' d''') = (term5 d' d'' m d''').
Proof. exact (TRANS (@lem1251575 d'' d' m d''') (@lem1251578 d' d'' m d''')). Qed.
Lemma lem1251595 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : (term5 m d'' d' d''') = (term5 d' d'' m d''').
Proof. exact (TRANS (@lem1251555 d'' m d' d''') (@lem1251594 d' d'' m d''')). Qed.
Lemma lem1251596 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : ((term4 m d' d'' d''') = (term5 m d'' d' d''')) = ((term5 d' d'' m d''') = (term5 d' d'' m d''')).
Proof. exact (MK_COMB (@lem1251552 d' d'' m d''') (@lem1251595 d' d'' m d''')). Qed.
Lemma lem1251598 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1251599 (x : nat) : (x = x) = True.
Proof. exact (@lem1251598 nat x). Qed.
Lemma lem1251600 (d' : nat) (d'' : nat) (m : nat) (d''' : nat) : ((term5 d' d'' m d''') = (term5 d' d'' m d''')) = True.
Proof. exact (@lem1251599 (term5 d' d'' m d''')). Qed.
Lemma lem1251601 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term4 m d' d'' d''') = (term5 m d'' d' d''')) = True.
Proof. exact (TRANS (@lem1251596 d' d'' m d''') (@lem1251600 d' d'' m d''')). Qed.
Lemma lem1251602 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term4 m d' d'' d''') = (term5 m d'' d' d''')).
Proof. exact (SYM (@lem1251601 m d'' d' d''')). Qed.
Lemma lem1251603 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term4 m d' d'' d''') = (term5 m d'' d' d''').
Proof. exact (EQ_MP (@lem1251602 m d'' d' d''') (@lem0)). Qed.
Lemma lem1251607 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1251608 (m : nat) (d' : nat) (d'' : nat) : (term0 m d' d'') = (term1 m d' d'').
Proof. exact (@lem1251607 m d' d''). Qed.
Lemma lem1251610 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251611 (d' : nat) (m : nat) (d'' : nat) : (term1 m d' d'') = (term1 d' m d'').
Proof. exact (@lem1251610 d' m d''). Qed.
Lemma lem1251618 (d' : nat) (m : nat) (d'' : nat) : (term0 m d' d'') = (term1 d' m d'').
Proof. exact (TRANS (@lem1251608 m d' d'') (@lem1251611 d' m d'')). Qed.
Lemma lem1251620 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1251621 (d'' : nat) (m : nat) : (Nat.add m d'') = (Nat.add d'' m).
Proof. exact (@lem1251620 d'' m). Qed.
Lemma lem1251625 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251626 (d' : nat) (d'' : nat) (m : nat) : (term1 d' m d'') = (term1 d' d'' m).
Proof. exact (MK_COMB (@lem1251625 d') (@lem1251621 d'' m)). Qed.
Lemma lem1251633 (d' : nat) (d'' : nat) (m : nat) : (term0 m d' d'') = (term1 d' d'' m).
Proof. exact (TRANS (@lem1251618 d' m d'') (@lem1251626 d' d'' m)). Qed.
Lemma lem1251634 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1251635 (d' : nat) (d'' : nat) (m : nat) : (term9 m d' d'') = (term10 d' d'' m).
Proof. exact (MK_COMB (@lem1251634) (@lem1251633 d' d'' m)). Qed.
Lemma lem1251637 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251638 (d'' : nat) (m : nat) (d' : nat) : (term1 m d'' d') = (term1 d'' m d').
Proof. exact (@lem1251637 d'' m d'). Qed.
Lemma lem1251646 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1251647 (d' : nat) (m : nat) : (Nat.add m d') = (Nat.add d' m).
Proof. exact (@lem1251646 d' m). Qed.
Lemma lem1251651 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1251652 (d'' : nat) (d' : nat) (m : nat) : (term1 d'' m d') = (term1 d'' d' m).
Proof. exact (MK_COMB (@lem1251651 d'') (@lem1251647 d' m)). Qed.
Lemma lem1251654 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251655 (d' : nat) (d'' : nat) (m : nat) : (term1 d'' d' m) = (term1 d' d'' m).
Proof. exact (@lem1251654 d' d'' m). Qed.
Lemma lem1251665 (d' : nat) (d'' : nat) (m : nat) : (term1 d'' m d') = (term1 d' d'' m).
Proof. exact (TRANS (@lem1251652 d'' d' m) (@lem1251655 d' d'' m)). Qed.
Lemma lem1251666 (d' : nat) (d'' : nat) (m : nat) : (term1 m d'' d') = (term1 d' d'' m).
Proof. exact (TRANS (@lem1251638 d'' m d') (@lem1251665 d' d'' m)). Qed.
Lemma lem1251667 (d' : nat) (d'' : nat) (m : nat) : ((term0 m d' d'') = (term1 m d'' d')) = ((term1 d' d'' m) = (term1 d' d'' m)).
Proof. exact (MK_COMB (@lem1251635 d' d'' m) (@lem1251666 d' d'' m)). Qed.
Lemma lem1251669 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1251670 (x : nat) : (x = x) = True.
Proof. exact (@lem1251669 nat x). Qed.
Lemma lem1251671 (d' : nat) (d'' : nat) (m : nat) : ((term1 d' d'' m) = (term1 d' d'' m)) = True.
Proof. exact (@lem1251670 (term1 d' d'' m)). Qed.
Lemma lem1251672 (m : nat) (d'' : nat) (d' : nat) : ((term0 m d' d'') = (term1 m d'' d')) = True.
Proof. exact (TRANS (@lem1251667 d' d'' m) (@lem1251671 d' d'' m)). Qed.
Lemma lem1251673 (m : nat) (d'' : nat) (d' : nat) : True = ((term0 m d' d'') = (term1 m d'' d')).
Proof. exact (SYM (@lem1251672 m d'' d')). Qed.
Lemma lem1251674 (m : nat) (d'' : nat) (d' : nat) : (term0 m d' d'') = (term1 m d'' d').
Proof. exact (EQ_MP (@lem1251673 m d'' d') (@lem0)). Qed.
Lemma lem1251675 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1251676 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term7 m d' d'' d''') = (term8 m d'' d' d''').
Proof. exact (MK_COMB (@lem1251675) (@lem1251603 m d'' d' d''')). Qed.
Lemma lem1251677 (d''' : nat) (m : nat) (d'' : nat) (d' : nat) : ((term4 m d' d'' d''') = (term0 m d' d'')) = ((term5 m d'' d' d''') = (term1 m d'' d')).
Proof. exact (MK_COMB (@lem1251676 m d'' d' d''') (@lem1251674 m d'' d')). Qed.
Lemma lem1251684 (m : nat) : term11 m.
Proof. exact (@lem79890 m). Qed.
Lemma lem1251685 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem1251686 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1251685 m) (@lem1251684 m)). Qed.
Lemma lem1251687 (m : nat) (n : nat) : term13 m n.
Proof. exact (@lem1251686 m n). Qed.
Lemma lem1251688 (m : nat) (n : nat) : (term13 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem1251690 (m : nat) : term14 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1251691 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1251692 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1251691 m) (@lem1251690 m)). Qed.
Lemma lem1251693 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1251692 m n). Qed.
Lemma lem1251694 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1251695 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem1251694 m n) (@lem1251693 m n)). Qed.
Lemma lem1251696 (m : nat) (n : nat) (p : nat) : term18 m n p.
Proof. exact (@lem1251695 m n p). Qed.
Lemma lem1251697 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem1251700 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1251697 m n p) (@lem1251696 m n p)). Qed.
Lemma lem1251701 (m : nat) (d''' : nat) (d'' : nat) (d' : nat) : ((term5 m d'' d' d''') = (term1 m d'' d')) = ((term3 d'' d' d''') = (Nat.add d'' d')).
Proof. exact (@lem1251700 m (term3 d'' d' d''') (Nat.add d'' d')). Qed.
Lemma lem1251703 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1251697 m n p) (@lem1251696 m n p)). Qed.
Lemma lem1251704 (d'' : nat) (d''' : nat) (d' : nat) : ((term3 d'' d' d''') = (Nat.add d'' d')) = ((term6 d' d''') = d').
Proof. exact (@lem1251703 d'' (term6 d' d''') d'). Qed.
Lemma lem1251706 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1251688 m n) (@lem1251687 m n)). Qed.
Lemma lem1251709 (d' : nat) (d''' : nat) : ((term6 d' d''') = d') = ((S d''') = (NUMERAL 0)).
Proof. exact (@lem1251706 d' (S d''')). Qed.
Lemma lem1251710 (d'' : nat) (d' : nat) (d''' : nat) : ((term3 d'' d' d''') = (Nat.add d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1251704 d'' d''' d') (@lem1251709 d' d''')). Qed.
Lemma lem1251711 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term5 m d'' d' d''') = (term1 m d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1251701 m d''' d'' d') (@lem1251710 d'' d' d''')). Qed.
Lemma lem1251712 (d''' : nat) (m : nat) (d' : nat) (d'' : nat) : (term19 d''' m d' d'') = (term19 d''' m d' d'').
Proof. exact (eq_refl (term19 d''' m d' d'')). Qed.
Lemma lem1251713 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : (((term4 m d' d'' d''') = (term0 m d' d'')) = ((term5 m d'' d' d''') = (term1 m d'' d'))) = (((term4 m d' d'' d''') = (term0 m d' d'')) = ((S d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1251712 d''' m d' d'') (@lem1251711 m d'' d' d''')). Qed.
Lemma lem1251714 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term4 m d' d'' d''') = (term0 m d' d'')) = ((S d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1251713 m d' d'' d''') (@lem1251677 d''' m d'' d')). Qed.
Lemma lem1251715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1251716 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term20 d''' m d' d'') = (term21 d''').
Proof. exact (MK_COMB (@lem1251715) (@lem1251714 m d' d'' d''')). Qed.
Lemma lem1251717 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1251718 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term22 d''' m d' d'') = (term23 d''').
Proof. exact (MK_COMB (@lem1251716 m d' d'' d''') (@lem1251717)). Qed.
Lemma lem1251719 (d''' : nat) (m : nat) (d' : nat) (d'' : nat) : (term23 d''') = (term22 d''' m d' d'').
Proof. exact (SYM (@lem1251718 m d' d'' d''')). Qed.
