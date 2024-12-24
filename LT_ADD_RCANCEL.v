Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_ADD_RCANCEL_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import LT_ADD_LCANCEL_spec.
Lemma lem101109 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem101110 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem101111 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem101110 m) (@lem101109 m)). Qed.
Lemma lem101112 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem101111 m n). Qed.
Lemma lem101113 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem101130 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem101113 n m) (@lem101112 m n)). Qed.
Lemma lem101131 (p : nat) (m : nat) : (Nat.add m p) = (Nat.add p m).
Proof. exact (@lem101130 p m). Qed.
Lemma lem101132 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem101133 (p : nat) (m : nat) : (term3 m p) = (term3 p m).
Proof. exact (MK_COMB (@lem101132) (@lem101131 p m)). Qed.
Lemma lem101135 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem101113 n m) (@lem101112 m n)). Qed.
Lemma lem101136 (p : nat) (n : nat) : (Nat.add n p) = (Nat.add p n).
Proof. exact (@lem101135 p n). Qed.
Lemma lem101137 (m : nat) (p : nat) (n : nat) : (term4 m n p) = (term5 m p n).
Proof. exact (MK_COMB (@lem101133 p m) (@lem101136 p n)). Qed.
Lemma lem101138 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem101139 (m : nat) (p : nat) (n : nat) : (term6 m n p) = (term7 m p n).
Proof. exact (MK_COMB (@lem101138) (@lem101137 m p n)). Qed.
Lemma lem101140 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem101141 (p : nat) (m : nat) (n : nat) : ((term4 m n p) = (Peano.lt m n)) = ((term5 m p n) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem101139 m p n) (@lem101140 m n)). Qed.
Lemma lem101142 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (fun_ext (fun p : nat => @lem101141 p m n)). Qed.
Lemma lem101143 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem101144 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem101143) (@lem101142 m n)). Qed.
Lemma lem101145 (m : nat) : (term12 m) = (term13 m).
Proof. exact (fun_ext (fun n : nat => @lem101144 m n)). Qed.
Lemma lem101146 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem101147 (m : nat) : (term14 m) = (term15 m).
Proof. exact (MK_COMB (@lem101146) (@lem101145 m)). Qed.
Lemma lem101148 : term16 = term17.
Proof. exact (fun_ext (fun m : nat => @lem101147 m)). Qed.
Lemma lem101149 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem101150 : term18 = term19.
Proof. exact (MK_COMB (@lem101149) (@lem101148)). Qed.
Lemma lem101151 : term19 = term18.
Proof. exact (SYM (@lem101150)). Qed.
Lemma lem101152 (m : nat) : term20 m.
Proof. exact (@lem101108 m). Qed.
Lemma lem101153 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem101154 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem101153 m) (@lem101152 m)). Qed.
Lemma lem101155 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem101154 m n). Qed.
Lemma lem101156 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem101157 (m : nat) (n : nat) : term23 m n.
Proof. exact (EQ_MP (@lem101156 m n) (@lem101155 m n)). Qed.
Lemma lem101158 (m : nat) (n : nat) (p : nat) : term24 m n p.
Proof. exact (@lem101157 m n p). Qed.
Lemma lem101159 (m : nat) (n : nat) (p : nat) : (term24 m n p) = ((term5 n m p) = (Peano.lt n p)).
Proof. exact (eq_refl (term24 m n p)). Qed.
Lemma lem101162 (m : nat) (n : nat) (p : nat) : (term5 n m p) = (Peano.lt n p).
Proof. exact (EQ_MP (@lem101159 m n p) (@lem101158 m n p)). Qed.
Lemma lem101163 (p : nat) (m : nat) (n : nat) : (term5 m p n) = (Peano.lt m n).
Proof. exact (@lem101162 p m n). Qed.
Lemma lem101168 (m : nat) (n : nat) : term11 m n.
Proof. exact (fun p : nat => @lem101163 p m n). Qed.
Lemma lem101173 (m : nat) : term15 m.
Proof. exact (fun n : nat => @lem101168 m n). Qed.
Lemma lem101178 : term19.
Proof. exact (fun m : nat => @lem101173 m). Qed.
Lemma lem101179 : term18.
Proof. exact (EQ_MP (@lem101151) (@lem101178)). Qed.
