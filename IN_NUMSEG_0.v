Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_NUMSEG_0_term_abbrevs.
Require Import IN_NUMSEG_spec.
Require Import LE_0_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem5371274 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem5371275 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem5371276 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem5371275 n) (@lem5371274 n)). Qed.
Lemma lem5371277 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem5371279 (m : nat) : term2 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem5371280 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem5371281 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem5371280 m) (@lem5371279 m)). Qed.
Lemma lem5371282 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem5371281 m n). Qed.
Lemma lem5371283 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem5371284 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem5371283 m n) (@lem5371282 m n)). Qed.
Lemma lem5371285 (m : nat) (n : nat) (p : nat) : term6 m n p.
Proof. exact (@lem5371284 m n p). Qed.
Lemma lem5371286 (m : nat) (p : nat) (n : nat) : (term6 m n p) = ((term7 p m n) = (term8 m p n)).
Proof. exact (eq_refl (term6 m n p)). Qed.
Lemma lem5371299 (m : nat) (p : nat) (n : nat) : (term7 p m n) = (term8 m p n).
Proof. exact (EQ_MP (@lem5371286 m p n) (@lem5371285 m n p)). Qed.
Lemma lem5371300 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (@lem5371299 (NUMERAL 0) m n). Qed.
Lemma lem5371304 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem5371277 n) (@lem5371276 n)). Qed.
Lemma lem5371305 (m : nat) : (term1 m) = True.
Proof. exact (@lem5371304 m). Qed.
Lemma lem5371306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5371307 (m : nat) : (term11 m) = (and True).
Proof. exact (MK_COMB (@lem5371306) (@lem5371305 m)). Qed.
Lemma lem5371308 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem5371309 (m : nat) (n : nat) : (term10 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem5371307 m) (@lem5371308 m n)). Qed.
Lemma lem5371311 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5371312 (m : nat) (n : nat) : (term12 m n) = (Peano.le m n).
Proof. exact (@lem5371311 (Peano.le m n)). Qed.
Lemma lem5371313 (m : nat) (n : nat) : (term10 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem5371309 m n) (@lem5371312 m n)). Qed.
Lemma lem5371314 (m : nat) (n : nat) : (term9 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem5371300 m n) (@lem5371313 m n)). Qed.
Lemma lem5371315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5371316 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem5371315) (@lem5371314 m n)). Qed.
Lemma lem5371317 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem5371318 (m : nat) (n : nat) : ((term9 m n) = (Peano.le m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem5371316 m n) (@lem5371317 m n)). Qed.
Lemma lem5371320 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5371321 (x : Prop) : (x = x) = True.
Proof. exact (@lem5371320 Prop x). Qed.
Lemma lem5371322 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem5371321 (Peano.le m n)). Qed.
Lemma lem5371323 (m : nat) (n : nat) : ((term9 m n) = (Peano.le m n)) = True.
Proof. exact (TRANS (@lem5371318 m n) (@lem5371322 m n)). Qed.
Lemma lem5371324 (m : nat) : (term15 m) = term16.
Proof. exact (fun_ext (fun n : nat => @lem5371323 m n)). Qed.
Lemma lem5371325 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371326 (m : nat) : (term17 m) = term18.
Proof. exact (MK_COMB (@lem5371325) (@lem5371324 m)). Qed.
Lemma lem5371328 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5371329 (t : Prop) : (term20 t) = t.
Proof. exact (@lem5371328 nat t). Qed.
Lemma lem5371330 : term18 = True.
Proof. exact (@lem5371329 True). Qed.
Lemma lem5371331 (m : nat) : (term17 m) = True.
Proof. exact (TRANS (@lem5371326 m) (@lem5371330)). Qed.
Lemma lem5371332 : term21 = term16.
Proof. exact (fun_ext (fun m : nat => @lem5371331 m)). Qed.
Lemma lem5371333 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371334 : term22 = term18.
Proof. exact (MK_COMB (@lem5371333) (@lem5371332)). Qed.
Lemma lem5371336 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5371337 (t : Prop) : (term20 t) = t.
Proof. exact (@lem5371336 nat t). Qed.
Lemma lem5371338 : term18 = True.
Proof. exact (@lem5371337 True). Qed.
Lemma lem5371339 : term22 = True.
Proof. exact (TRANS (@lem5371334) (@lem5371338)). Qed.
Lemma lem5371340 : True = term22.
Proof. exact (SYM (@lem5371339)). Qed.
Lemma lem5371341 : term22.
Proof. exact (EQ_MP (@lem5371340) (@lem0)). Qed.
