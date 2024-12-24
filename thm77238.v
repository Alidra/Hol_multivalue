Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm77238_term_abbrevs.
Require Import thm77014_spec.
Require Import thm77187_spec.
Lemma lem77188 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem77189 : term1.
Proof. exact (EQ_MP (@lem77188) (@lem77014)). Qed.
Lemma lem77190 : term2.
Proof. exact (@lem77189 term3). Qed.
Lemma lem77191 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem77192 : term4.
Proof. exact (EQ_MP (@lem77191) (@lem77190)). Qed.
Lemma lem77193 (h1 : Nat.add = term5) : Nat.add = term5.
Proof. exact (h1). Qed.
Lemma lem77194 (h1 : Nat.add = term5) : term5 = Nat.add.
Proof. exact (SYM (@lem77193 h1)). Qed.
Lemma lem77195 (h1 : term5 = Nat.add) : term5 = Nat.add.
Proof. exact (h1). Qed.
Lemma lem77196 (h1 : term5 = Nat.add) : Nat.add = term5.
Proof. exact (SYM (@lem77195 h1)). Qed.
Lemma lem77197 : (Nat.add = term5) = (term5 = Nat.add).
Proof. exact (prop_ext (fun h1 : Nat.add = term5 => @lem77194 h1) (fun h1 : term5 = Nat.add => @lem77196 h1)). Qed.
Lemma lem77200 : term5 = Nat.add.
Proof. exact (EQ_MP (@lem77197) (@lem77187)). Qed.
Lemma lem77201 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem77202 : term6 = term7.
Proof. exact (MK_COMB (@lem77200) (@lem77201)). Qed.
Lemma lem77203 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem77204 (n : nat) : (term8 n) = (term9 n).
Proof. exact (MK_COMB (@lem77202) (@lem77203 n)). Qed.
Lemma lem77205 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77206 (n : nat) : (term10 n) = (term11 n).
Proof. exact (MK_COMB (@lem77205) (@lem77204 n)). Qed.
Lemma lem77207 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem77208 (n : nat) : ((term8 n) = n) = ((term9 n) = n).
Proof. exact (MK_COMB (@lem77206 n) (@lem77207 n)). Qed.
Lemma lem77209 : term12 = term13.
Proof. exact (fun_ext (fun n : nat => @lem77208 n)). Qed.
Lemma lem77210 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77211 : term14 = term15.
Proof. exact (MK_COMB (@lem77210) (@lem77209)). Qed.
Lemma lem77212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem77213 : term16 = term17.
Proof. exact (MK_COMB (@lem77212) (@lem77211)). Qed.
Lemma lem77215 : term5 = Nat.add.
Proof. exact (EQ_MP (@lem77197) (@lem77187)). Qed.
Lemma lem77216 (m : nat) : (S m) = (S m).
Proof. exact (eq_refl (S m)). Qed.
Lemma lem77217 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem77215) (@lem77216 m)). Qed.
Lemma lem77218 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem77219 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem77217 m) (@lem77218 n)). Qed.
Lemma lem77220 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77221 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem77220) (@lem77219 m n)). Qed.
Lemma lem77223 : term5 = Nat.add.
Proof. exact (EQ_MP (@lem77197) (@lem77187)). Qed.
Lemma lem77224 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem77225 (m : nat) : (term24 m) = (Nat.add m).
Proof. exact (MK_COMB (@lem77223) (@lem77224 m)). Qed.
Lemma lem77226 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem77227 (m : nat) (n : nat) : (term25 m n) = (Nat.add m n).
Proof. exact (MK_COMB (@lem77225 m) (@lem77226 n)). Qed.
Lemma lem77228 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem77229 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (MK_COMB (@lem77228) (@lem77227 m n)). Qed.
Lemma lem77230 (m : nat) (n : nat) : ((term20 m n) = (term26 m n)) = ((term21 m n) = (term27 m n)).
Proof. exact (MK_COMB (@lem77221 m n) (@lem77229 m n)). Qed.
Lemma lem77231 (m : nat) : (term28 m) = (term29 m).
Proof. exact (fun_ext (fun n : nat => @lem77230 m n)). Qed.
Lemma lem77232 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77233 (m : nat) : (term30 m) = (term31 m).
Proof. exact (MK_COMB (@lem77232) (@lem77231 m)). Qed.
Lemma lem77234 : term32 = term33.
Proof. exact (fun_ext (fun m : nat => @lem77233 m)). Qed.
Lemma lem77235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77236 : term34 = term35.
Proof. exact (MK_COMB (@lem77235) (@lem77234)). Qed.
Lemma lem77237 : term4 = term36.
Proof. exact (MK_COMB (@lem77213) (@lem77236)). Qed.
Lemma lem77238 : term36.
Proof. exact (EQ_MP (@lem77237) (@lem77192)). Qed.
