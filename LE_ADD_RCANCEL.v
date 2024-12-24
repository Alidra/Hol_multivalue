Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_ADD_RCANCEL_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import LE_ADD_LCANCEL_spec.
Lemma lem100903 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem100904 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem100905 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem100904 m) (@lem100903 m)). Qed.
Lemma lem100906 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem100905 m n). Qed.
Lemma lem100907 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem100924 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem100907 n m) (@lem100906 m n)). Qed.
Lemma lem100925 (p : nat) (m : nat) : (Nat.add m p) = (Nat.add p m).
Proof. exact (@lem100924 p m). Qed.
Lemma lem100926 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem100927 (p : nat) (m : nat) : (term3 m p) = (term3 p m).
Proof. exact (MK_COMB (@lem100926) (@lem100925 p m)). Qed.
Lemma lem100929 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem100907 n m) (@lem100906 m n)). Qed.
Lemma lem100930 (p : nat) (n : nat) : (Nat.add n p) = (Nat.add p n).
Proof. exact (@lem100929 p n). Qed.
Lemma lem100931 (m : nat) (p : nat) (n : nat) : (term4 m n p) = (term5 m p n).
Proof. exact (MK_COMB (@lem100927 p m) (@lem100930 p n)). Qed.
Lemma lem100932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem100933 (m : nat) (p : nat) (n : nat) : (term6 m n p) = (term7 m p n).
Proof. exact (MK_COMB (@lem100932) (@lem100931 m p n)). Qed.
Lemma lem100934 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem100935 (p : nat) (m : nat) (n : nat) : ((term4 m n p) = (Peano.le m n)) = ((term5 m p n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem100933 m p n) (@lem100934 m n)). Qed.
Lemma lem100936 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (fun_ext (fun p : nat => @lem100935 p m n)). Qed.
Lemma lem100937 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100938 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem100937) (@lem100936 m n)). Qed.
Lemma lem100939 (m : nat) : (term12 m) = (term13 m).
Proof. exact (fun_ext (fun n : nat => @lem100938 m n)). Qed.
Lemma lem100940 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100941 (m : nat) : (term14 m) = (term15 m).
Proof. exact (MK_COMB (@lem100940) (@lem100939 m)). Qed.
Lemma lem100942 : term16 = term17.
Proof. exact (fun_ext (fun m : nat => @lem100941 m)). Qed.
Lemma lem100943 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100944 : term18 = term19.
Proof. exact (MK_COMB (@lem100943) (@lem100942)). Qed.
Lemma lem100945 : term19 = term18.
Proof. exact (SYM (@lem100944)). Qed.
Lemma lem100946 (m : nat) : term20 m.
Proof. exact (@lem100902 m). Qed.
Lemma lem100947 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem100948 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem100947 m) (@lem100946 m)). Qed.
Lemma lem100949 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem100948 m n). Qed.
Lemma lem100950 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem100951 (m : nat) (n : nat) : term23 m n.
Proof. exact (EQ_MP (@lem100950 m n) (@lem100949 m n)). Qed.
Lemma lem100952 (m : nat) (n : nat) (p : nat) : term24 m n p.
Proof. exact (@lem100951 m n p). Qed.
Lemma lem100953 (m : nat) (n : nat) (p : nat) : (term24 m n p) = ((term5 n m p) = (Peano.le n p)).
Proof. exact (eq_refl (term24 m n p)). Qed.
Lemma lem100956 (m : nat) (n : nat) (p : nat) : (term5 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem100953 m n p) (@lem100952 m n p)). Qed.
Lemma lem100957 (p : nat) (m : nat) (n : nat) : (term5 m p n) = (Peano.le m n).
Proof. exact (@lem100956 p m n). Qed.
Lemma lem100962 (m : nat) (n : nat) : term11 m n.
Proof. exact (fun p : nat => @lem100957 p m n). Qed.
Lemma lem100967 (m : nat) : term15 m.
Proof. exact (fun n : nat => @lem100962 m n). Qed.
Lemma lem100972 : term19.
Proof. exact (fun m : nat => @lem100967 m). Qed.
Lemma lem100973 : term18.
Proof. exact (EQ_MP (@lem100945) (@lem100972)). Qed.
