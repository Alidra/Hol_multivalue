Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm80360_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import BIT1_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75543_spec.
Lemma lem80211 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem80212 (n : nat) : (term0 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem80223 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80212 n) (@lem80211 n)). Qed.
Lemma lem80224 : (NUMERAL 0) = 0.
Proof. exact (@lem80223 0). Qed.
Lemma lem80225 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem80226 : term1 = (Nat.add 0).
Proof. exact (MK_COMB (@lem80225) (@lem80224)). Qed.
Lemma lem80227 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem80228 (n : nat) : (term2 n) = (Nat.add 0 n).
Proof. exact (MK_COMB (@lem80226) (@lem80227 n)). Qed.
Lemma lem80229 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80230 (n : nat) : (term3 n) = (term4 n).
Proof. exact (MK_COMB (@lem80229) (@lem80228 n)). Qed.
Lemma lem80231 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem80232 (n : nat) : ((term2 n) = n) = ((Nat.add 0 n) = n).
Proof. exact (MK_COMB (@lem80230 n) (@lem80231 n)). Qed.
Lemma lem80235 : term5 = term6.
Proof. exact (fun_ext (fun n : nat => @lem80232 n)). Qed.
Lemma lem80236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80237 : term7 = term8.
Proof. exact (MK_COMB (@lem80236) (@lem80235)). Qed.
Lemma lem80242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem80243 : term9 = term10.
Proof. exact (MK_COMB (@lem80242) (@lem80237)). Qed.
Lemma lem80253 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80212 n) (@lem80211 n)). Qed.
Lemma lem80254 : (NUMERAL 0) = 0.
Proof. exact (@lem80253 0). Qed.
Lemma lem80255 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem80256 (m : nat) : (term11 m) = (Nat.add m 0).
Proof. exact (MK_COMB (@lem80255 m) (@lem80254)). Qed.
Lemma lem80257 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80258 (m : nat) : (term12 m) = (term13 m).
Proof. exact (MK_COMB (@lem80257) (@lem80256 m)). Qed.
Lemma lem80259 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem80260 (m : nat) : ((term11 m) = m) = ((Nat.add m 0) = m).
Proof. exact (MK_COMB (@lem80258 m) (@lem80259 m)). Qed.
Lemma lem80263 : term14 = term15.
Proof. exact (fun_ext (fun m : nat => @lem80260 m)). Qed.
Lemma lem80264 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80265 : term16 = term17.
Proof. exact (MK_COMB (@lem80264) (@lem80263)). Qed.
Lemma lem80270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem80271 : term18 = term19.
Proof. exact (MK_COMB (@lem80270) (@lem80265)). Qed.
Lemma lem80294 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem80295 : term21 = term22.
Proof. exact (MK_COMB (@lem80271) (@lem80294)). Qed.
Lemma lem80298 : term23 = term24.
Proof. exact (MK_COMB (@lem80243) (@lem80295)). Qed.
Lemma lem80301 : term24.
Proof. exact (EQ_MP (@lem80298) (@lem77629)). Qed.
Lemma lem80302 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem80303 (n : nat) : (term0 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem80325 : term8.
Proof. exact (proj1 (@lem80301)). Qed.
Lemma lem80326 (n : nat) : term25 n.
Proof. exact (@lem80325 n). Qed.
Lemma lem80327 (n : nat) : (term25 n) = ((Nat.add 0 n) = n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem80329 (n : nat) : term26 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem80330 (n : nat) : (term26 n) = ((BIT1 n) = (term27 n)).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem80335 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80303 n) (@lem80302 n)). Qed.
Lemma lem80336 : term28 = (BIT1 0).
Proof. exact (@lem80335 (BIT1 0)). Qed.
Lemma lem80338 (n : nat) : (BIT1 n) = (term27 n).
Proof. exact (EQ_MP (@lem80330 n) (@lem80329 n)). Qed.
Lemma lem80339 : (BIT1 0) = term29.
Proof. exact (@lem80338 0). Qed.
Lemma lem80340 : term28 = term29.
Proof. exact (TRANS (@lem80336) (@lem80339)). Qed.
Lemma lem80342 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem80327 n) (@lem80326 n)). Qed.
Lemma lem80343 : (Nat.add 0 0) = 0.
Proof. exact (@lem80342 0). Qed.
Lemma lem80344 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80345 : term29 = (S 0).
Proof. exact (MK_COMB (@lem80344) (@lem80343)). Qed.
Lemma lem80346 : term28 = (S 0).
Proof. exact (TRANS (@lem80340) (@lem80345)). Qed.
Lemma lem80347 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80348 : term30 = term31.
Proof. exact (MK_COMB (@lem80347) (@lem80346)). Qed.
Lemma lem80350 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80303 n) (@lem80302 n)). Qed.
Lemma lem80351 : (NUMERAL 0) = 0.
Proof. exact (@lem80350 0). Qed.
Lemma lem80352 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80353 : term32 = (S 0).
Proof. exact (MK_COMB (@lem80352) (@lem80351)). Qed.
Lemma lem80354 : (term28 = term32) = ((S 0) = (S 0)).
Proof. exact (MK_COMB (@lem80348) (@lem80353)). Qed.
Lemma lem80356 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem80357 (x : nat) : (x = x) = True.
Proof. exact (@lem80356 nat x). Qed.
Lemma lem80358 : ((S 0) = (S 0)) = True.
Proof. exact (@lem80357 (S 0)). Qed.
Lemma lem80359 : (term28 = term32) = True.
Proof. exact (TRANS (@lem80354) (@lem80358)). Qed.
Lemma lem80360 : True = (term28 = term32).
Proof. exact (SYM (@lem80359)). Qed.
