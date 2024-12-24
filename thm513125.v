Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm513125_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem513093 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem513094 : (NUMERAL 0) = 0.
Proof. exact (@lem513093 0). Qed.
Lemma lem513095 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem513096 : term0 = (Nat.add 0).
Proof. exact (MK_COMB (@lem513095) (@lem513094)). Qed.
Lemma lem513097 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem513098 (n : nat) : (term1 n) = (Nat.add 0 n).
Proof. exact (MK_COMB (@lem513096) (@lem513097 n)). Qed.
Lemma lem513099 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513100 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem513099) (@lem513098 n)). Qed.
Lemma lem513101 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem513102 (n : nat) : ((term1 n) = n) = ((Nat.add 0 n) = n).
Proof. exact (MK_COMB (@lem513100 n) (@lem513101 n)). Qed.
Lemma lem513103 : term4 = term5.
Proof. exact (fun_ext (fun n : nat => @lem513102 n)). Qed.
Lemma lem513104 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513105 : term6 = term7.
Proof. exact (MK_COMB (@lem513104) (@lem513103)). Qed.
Lemma lem513106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513107 : term8 = term9.
Proof. exact (MK_COMB (@lem513106) (@lem513105)). Qed.
Lemma lem513109 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem513110 : (NUMERAL 0) = 0.
Proof. exact (@lem513109 0). Qed.
Lemma lem513111 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem513112 (m : nat) : (term10 m) = (Nat.add m 0).
Proof. exact (MK_COMB (@lem513111 m) (@lem513110)). Qed.
Lemma lem513113 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem513114 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem513113) (@lem513112 m)). Qed.
Lemma lem513115 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem513116 (m : nat) : ((term10 m) = m) = ((Nat.add m 0) = m).
Proof. exact (MK_COMB (@lem513114 m) (@lem513115 m)). Qed.
Lemma lem513117 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem513116 m)). Qed.
Lemma lem513118 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513119 : term15 = term16.
Proof. exact (MK_COMB (@lem513118) (@lem513117)). Qed.
Lemma lem513120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513121 : term17 = term18.
Proof. exact (MK_COMB (@lem513120) (@lem513119)). Qed.
Lemma lem513122 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem513123 : term20 = term21.
Proof. exact (MK_COMB (@lem513121) (@lem513122)). Qed.
Lemma lem513124 : term22 = term23.
Proof. exact (MK_COMB (@lem513107) (@lem513123)). Qed.
Lemma lem513125 : term23.
Proof. exact (EQ_MP (@lem513124) (@lem77629)). Qed.
