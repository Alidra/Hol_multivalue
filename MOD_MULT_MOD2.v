Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_MULT_MOD2_term_abbrevs.
Require Import MOD_MULT_LMOD_spec.
Require Import MOD_MULT_RMOD_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem205764 (m : nat) : term0 m.
Proof. exact (@lem205763 m). Qed.
Lemma lem205765 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem205766 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem205765 m) (@lem205764 m)). Qed.
Lemma lem205767 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem205766 m n). Qed.
Lemma lem205768 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem205769 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem205768 m n) (@lem205767 m n)). Qed.
Lemma lem205770 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem205769 m n p). Qed.
Lemma lem205771 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 m p n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem205773 (m : nat) : term7 m.
Proof. exact (@lem205654 m). Qed.
Lemma lem205774 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem205775 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem205774 m) (@lem205773 m)). Qed.
Lemma lem205776 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem205775 m n). Qed.
Lemma lem205777 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem205778 (m : nat) (n : nat) : term10 m n.
Proof. exact (EQ_MP (@lem205777 m n) (@lem205776 m n)). Qed.
Lemma lem205779 (m : nat) (n : nat) (p : nat) : term11 m n p.
Proof. exact (@lem205778 m n p). Qed.
Lemma lem205780 (m : nat) (p : nat) (n : nat) : (term11 m n p) = ((term12 m p n) = (term6 m p n)).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem205797 (m : nat) (p : nat) (n : nat) : (term5 m p n) = (term6 m p n).
Proof. exact (EQ_MP (@lem205771 m p n) (@lem205770 m n p)). Qed.
Lemma lem205798 (m : nat) (p : nat) (n : nat) : (term13 m p n) = (term12 m p n).
Proof. exact (@lem205797 m (Nat.modulo p n) n). Qed.
Lemma lem205800 (m : nat) (p : nat) (n : nat) : (term12 m p n) = (term6 m p n).
Proof. exact (EQ_MP (@lem205780 m p n) (@lem205779 m n p)). Qed.
Lemma lem205801 (m : nat) (p : nat) (n : nat) : (term13 m p n) = (term6 m p n).
Proof. exact (TRANS (@lem205798 m p n) (@lem205800 m p n)). Qed.
Lemma lem205802 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem205803 (m : nat) (p : nat) (n : nat) : (term14 m p n) = (term15 m p n).
Proof. exact (MK_COMB (@lem205802) (@lem205801 m p n)). Qed.
Lemma lem205804 (m : nat) (p : nat) (n : nat) : (term6 m p n) = (term6 m p n).
Proof. exact (eq_refl (term6 m p n)). Qed.
Lemma lem205805 (m : nat) (p : nat) (n : nat) : ((term13 m p n) = (term6 m p n)) = ((term6 m p n) = (term6 m p n)).
Proof. exact (MK_COMB (@lem205803 m p n) (@lem205804 m p n)). Qed.
Lemma lem205807 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem205808 (x : nat) : (x = x) = True.
Proof. exact (@lem205807 nat x). Qed.
Lemma lem205809 (m : nat) (p : nat) (n : nat) : ((term6 m p n) = (term6 m p n)) = True.
Proof. exact (@lem205808 (term6 m p n)). Qed.
Lemma lem205810 (m : nat) (p : nat) (n : nat) : ((term13 m p n) = (term6 m p n)) = True.
Proof. exact (TRANS (@lem205805 m p n) (@lem205809 m p n)). Qed.
Lemma lem205811 (m : nat) (n : nat) : (term16 m n) = term17.
Proof. exact (fun_ext (fun p : nat => @lem205810 m p n)). Qed.
Lemma lem205812 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205813 (m : nat) (n : nat) : (term18 m n) = term19.
Proof. exact (MK_COMB (@lem205812) (@lem205811 m n)). Qed.
Lemma lem205815 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem205816 (t : Prop) : (term21 t) = t.
Proof. exact (@lem205815 nat t). Qed.
Lemma lem205817 : term19 = True.
Proof. exact (@lem205816 True). Qed.
Lemma lem205818 (m : nat) (n : nat) : (term18 m n) = True.
Proof. exact (TRANS (@lem205813 m n) (@lem205817)). Qed.
Lemma lem205819 (m : nat) : (term22 m) = term17.
Proof. exact (fun_ext (fun n : nat => @lem205818 m n)). Qed.
Lemma lem205820 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205821 (m : nat) : (term23 m) = term19.
Proof. exact (MK_COMB (@lem205820) (@lem205819 m)). Qed.
Lemma lem205823 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem205824 (t : Prop) : (term21 t) = t.
Proof. exact (@lem205823 nat t). Qed.
Lemma lem205825 : term19 = True.
Proof. exact (@lem205824 True). Qed.
Lemma lem205826 (m : nat) : (term23 m) = True.
Proof. exact (TRANS (@lem205821 m) (@lem205825)). Qed.
Lemma lem205827 : term24 = term17.
Proof. exact (fun_ext (fun m : nat => @lem205826 m)). Qed.
Lemma lem205828 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem205829 : term25 = term19.
Proof. exact (MK_COMB (@lem205828) (@lem205827)). Qed.
Lemma lem205831 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem205832 (t : Prop) : (term21 t) = t.
Proof. exact (@lem205831 nat t). Qed.
Lemma lem205833 : term19 = True.
Proof. exact (@lem205832 True). Qed.
Lemma lem205834 : term25 = True.
Proof. exact (TRANS (@lem205829) (@lem205833)). Qed.
Lemma lem205835 : True = term25.
Proof. exact (SYM (@lem205834)). Qed.
Lemma lem205836 : term25.
Proof. exact (EQ_MP (@lem205835) (@lem0)). Qed.
