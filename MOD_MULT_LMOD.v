Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_MULT_LMOD_term_abbrevs.
Require Import MOD_MULT_RMOD_spec.
Require Import MULT_SYM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem205655 (m : nat) : term0 m.
Proof. exact (@lem205654 m). Qed.
Lemma lem205656 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem205657 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem205656 m) (@lem205655 m)). Qed.
Lemma lem205658 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem205657 m n). Qed.
Lemma lem205659 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem205660 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem205659 m n) (@lem205658 m n)). Qed.
Lemma lem205661 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem205660 m n p). Qed.
Lemma lem205662 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 m p n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem205664 (m : nat) : term7 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem205665 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem205666 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem205665 m) (@lem205664 m)). Qed.
Lemma lem205667 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem205666 m n). Qed.
Lemma lem205668 (n : nat) (m : nat) : (term9 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem205685 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem205668 n m) (@lem205667 m n)). Qed.
Lemma lem205686 (p : nat) (m : nat) (n : nat) : (term10 m n p) = (term11 p m n).
Proof. exact (@lem205685 p (Nat.modulo m n)). Qed.
Lemma lem205687 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem205688 (p : nat) (m : nat) (n : nat) : (term12 m n p) = (term13 p m n).
Proof. exact (MK_COMB (@lem205687) (@lem205686 p m n)). Qed.
Lemma lem205689 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem205690 (p : nat) (m : nat) (n : nat) : (term14 m p n) = (term5 p m n).
Proof. exact (MK_COMB (@lem205688 p m n) (@lem205689 n)). Qed.
Lemma lem205691 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem205692 (p : nat) (m : nat) (n : nat) : (term15 m p n) = (term16 p m n).
Proof. exact (MK_COMB (@lem205691) (@lem205690 p m n)). Qed.
Lemma lem205694 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem205668 n m) (@lem205667 m n)). Qed.
Lemma lem205695 (p : nat) (m : nat) : (Nat.mul m p) = (Nat.mul p m).
Proof. exact (@lem205694 p m). Qed.
Lemma lem205696 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem205697 (p : nat) (m : nat) : (term17 m p) = (term17 p m).
Proof. exact (MK_COMB (@lem205696) (@lem205695 p m)). Qed.
Lemma lem205698 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem205699 (p : nat) (m : nat) (n : nat) : (term6 m p n) = (term6 p m n).
Proof. exact (MK_COMB (@lem205697 p m) (@lem205698 n)). Qed.
Lemma lem205700 (p : nat) (m : nat) (n : nat) : ((term14 m p n) = (term6 m p n)) = ((term5 p m n) = (term6 p m n)).
Proof. exact (MK_COMB (@lem205692 p m n) (@lem205699 p m n)). Qed.
Lemma lem205701 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (fun_ext (fun p : nat => @lem205700 p m n)). Qed.
Lemma lem205702 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205703 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem205702) (@lem205701 m n)). Qed.
Lemma lem205704 (m : nat) : (term22 m) = (term23 m).
Proof. exact (fun_ext (fun n : nat => @lem205703 m n)). Qed.
Lemma lem205705 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205706 (m : nat) : (term24 m) = (term25 m).
Proof. exact (MK_COMB (@lem205705) (@lem205704 m)). Qed.
Lemma lem205707 : term26 = term27.
Proof. exact (fun_ext (fun m : nat => @lem205706 m)). Qed.
Lemma lem205708 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205709 : term28 = term29.
Proof. exact (MK_COMB (@lem205708) (@lem205707)). Qed.
Lemma lem205710 : term29 = term28.
Proof. exact (SYM (@lem205709)). Qed.
Lemma lem205726 (m : nat) (p : nat) (n : nat) : (term5 m p n) = (term6 m p n).
Proof. exact (EQ_MP (@lem205662 m p n) (@lem205661 m n p)). Qed.
Lemma lem205727 (p : nat) (m : nat) (n : nat) : (term5 p m n) = (term6 p m n).
Proof. exact (@lem205726 p m n). Qed.
Lemma lem205728 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem205729 (p : nat) (m : nat) (n : nat) : (term16 p m n) = (term30 p m n).
Proof. exact (MK_COMB (@lem205728) (@lem205727 p m n)). Qed.
Lemma lem205730 (p : nat) (m : nat) (n : nat) : (term6 p m n) = (term6 p m n).
Proof. exact (eq_refl (term6 p m n)). Qed.
Lemma lem205731 (p : nat) (m : nat) (n : nat) : ((term5 p m n) = (term6 p m n)) = ((term6 p m n) = (term6 p m n)).
Proof. exact (MK_COMB (@lem205729 p m n) (@lem205730 p m n)). Qed.
Lemma lem205733 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem205734 (x : nat) : (x = x) = True.
Proof. exact (@lem205733 nat x). Qed.
Lemma lem205735 (p : nat) (m : nat) (n : nat) : ((term6 p m n) = (term6 p m n)) = True.
Proof. exact (@lem205734 (term6 p m n)). Qed.
Lemma lem205736 (p : nat) (m : nat) (n : nat) : ((term5 p m n) = (term6 p m n)) = True.
Proof. exact (TRANS (@lem205731 p m n) (@lem205735 p m n)). Qed.
Lemma lem205737 (m : nat) (n : nat) : (term19 m n) = term31.
Proof. exact (fun_ext (fun p : nat => @lem205736 p m n)). Qed.
Lemma lem205738 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205739 (m : nat) (n : nat) : (term21 m n) = term32.
Proof. exact (MK_COMB (@lem205738) (@lem205737 m n)). Qed.
Lemma lem205741 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem205742 (t : Prop) : (term34 t) = t.
Proof. exact (@lem205741 nat t). Qed.
Lemma lem205743 : term32 = True.
Proof. exact (@lem205742 True). Qed.
Lemma lem205744 (m : nat) (n : nat) : (term21 m n) = True.
Proof. exact (TRANS (@lem205739 m n) (@lem205743)). Qed.
Lemma lem205745 (m : nat) : (term23 m) = term31.
Proof. exact (fun_ext (fun n : nat => @lem205744 m n)). Qed.
Lemma lem205746 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205747 (m : nat) : (term25 m) = term32.
Proof. exact (MK_COMB (@lem205746) (@lem205745 m)). Qed.
Lemma lem205749 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem205750 (t : Prop) : (term34 t) = t.
Proof. exact (@lem205749 nat t). Qed.
Lemma lem205751 : term32 = True.
Proof. exact (@lem205750 True). Qed.
Lemma lem205752 (m : nat) : (term25 m) = True.
Proof. exact (TRANS (@lem205747 m) (@lem205751)). Qed.
Lemma lem205753 : term27 = term31.
Proof. exact (fun_ext (fun m : nat => @lem205752 m)). Qed.
Lemma lem205754 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205755 : term29 = term32.
Proof. exact (MK_COMB (@lem205754) (@lem205753)). Qed.
Lemma lem205757 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem205758 (t : Prop) : (term34 t) = t.
Proof. exact (@lem205757 nat t). Qed.
Lemma lem205759 : term32 = True.
Proof. exact (@lem205758 True). Qed.
Lemma lem205760 : term29 = True.
Proof. exact (TRANS (@lem205755) (@lem205759)). Qed.
Lemma lem205761 : True = term29.
Proof. exact (SYM (@lem205760)). Qed.
Lemma lem205762 : term29.
Proof. exact (EQ_MP (@lem205761) (@lem0)). Qed.
Lemma lem205763 : term28.
Proof. exact (EQ_MP (@lem205710) (@lem205762)). Qed.
