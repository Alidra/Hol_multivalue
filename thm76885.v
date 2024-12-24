Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm76885_term_abbrevs.
Require Import thm76680_spec.
Require Import thm76851_spec.
Lemma lem76852 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem76853 : term1.
Proof. exact (EQ_MP (@lem76852) (@lem76680)). Qed.
Lemma lem76854 : term2.
Proof. exact (@lem76853 term3). Qed.
Lemma lem76855 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem76856 : term4.
Proof. exact (EQ_MP (@lem76855) (@lem76854)). Qed.
Lemma lem76857 (h1 : Nat.pred = term5) : Nat.pred = term5.
Proof. exact (h1). Qed.
Lemma lem76858 (h1 : Nat.pred = term5) : term5 = Nat.pred.
Proof. exact (SYM (@lem76857 h1)). Qed.
Lemma lem76859 (h1 : term5 = Nat.pred) : term5 = Nat.pred.
Proof. exact (h1). Qed.
Lemma lem76860 (h1 : term5 = Nat.pred) : Nat.pred = term5.
Proof. exact (SYM (@lem76859 h1)). Qed.
Lemma lem76861 : (Nat.pred = term5) = (term5 = Nat.pred).
Proof. exact (prop_ext (fun h1 : Nat.pred = term5 => @lem76858 h1) (fun h1 : term5 = Nat.pred => @lem76860 h1)). Qed.
Lemma lem76864 : term5 = Nat.pred.
Proof. exact (EQ_MP (@lem76861) (@lem76851)). Qed.
Lemma lem76865 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem76866 : term6 = term7.
Proof. exact (MK_COMB (@lem76864) (@lem76865)). Qed.
Lemma lem76867 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem76868 : term8 = term9.
Proof. exact (MK_COMB (@lem76867) (@lem76866)). Qed.
Lemma lem76869 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem76870 : (term6 = (NUMERAL 0)) = (term7 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem76868) (@lem76869)). Qed.
Lemma lem76871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem76872 : term10 = term11.
Proof. exact (MK_COMB (@lem76871) (@lem76870)). Qed.
Lemma lem76874 : term5 = Nat.pred.
Proof. exact (EQ_MP (@lem76861) (@lem76851)). Qed.
Lemma lem76875 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem76876 (n : nat) : (term12 n) = (term13 n).
Proof. exact (MK_COMB (@lem76874) (@lem76875 n)). Qed.
Lemma lem76877 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem76878 (n : nat) : (term14 n) = (term15 n).
Proof. exact (MK_COMB (@lem76877) (@lem76876 n)). Qed.
Lemma lem76879 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem76880 (n : nat) : ((term12 n) = n) = ((term13 n) = n).
Proof. exact (MK_COMB (@lem76878 n) (@lem76879 n)). Qed.
Lemma lem76881 : term16 = term17.
Proof. exact (fun_ext (fun n : nat => @lem76880 n)). Qed.
Lemma lem76882 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem76883 : term18 = term19.
Proof. exact (MK_COMB (@lem76882) (@lem76881)). Qed.
Lemma lem76884 : term4 = term20.
Proof. exact (MK_COMB (@lem76872) (@lem76883)). Qed.
Lemma lem76885 : term20.
Proof. exact (EQ_MP (@lem76884) (@lem76856)). Qed.
