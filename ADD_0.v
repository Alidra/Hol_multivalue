Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD_0_term_abbrevs.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm77238_spec.
Lemma lem77243 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem77244 : term1.
Proof. exact (@lem77243 term2). Qed.
Lemma lem77245 : term3 = (term4 = (NUMERAL 0)).
Proof. exact (eq_refl term3). Qed.
Lemma lem77246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem77247 : term5 = term6.
Proof. exact (MK_COMB (@lem77246) (@lem77245)). Qed.
Lemma lem77248 (m : nat) : (term7 m) = ((term8 m) = m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem77249 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem77250 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem77249) (@lem77248 m)). Qed.
Lemma lem77251 (m : nat) : (term11 m) = ((term12 m) = (S m)).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem77252 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem77250 m) (@lem77251 m)). Qed.
Lemma lem77253 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem77252 m)). Qed.
Lemma lem77254 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77255 : term17 = term18.
Proof. exact (MK_COMB (@lem77254) (@lem77253)). Qed.
Lemma lem77256 : term19 = term20.
Proof. exact (MK_COMB (@lem77247) (@lem77255)). Qed.
Lemma lem77257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem77258 : term21 = term22.
Proof. exact (MK_COMB (@lem77257) (@lem77256)). Qed.
Lemma lem77259 (m : nat) : (term7 m) = ((term8 m) = m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem77260 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem77259 m)). Qed.
Lemma lem77261 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77262 : term24 = term25.
Proof. exact (MK_COMB (@lem77261) (@lem77260)). Qed.
Lemma lem77263 : term1 = term26.
Proof. exact (MK_COMB (@lem77258) (@lem77262)). Qed.
Lemma lem77264 : term26.
Proof. exact (EQ_MP (@lem77263) (@lem77244)). Qed.
Lemma lem77273 : term27.
Proof. exact (proj1 (@lem77238)). Qed.
Lemma lem77274 (n : nat) : term28 n.
Proof. exact (@lem77273 n). Qed.
Lemma lem77275 (n : nat) : (term28 n) = ((term29 n) = n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem77280 (n : nat) : (term29 n) = n.
Proof. exact (EQ_MP (@lem77275 n) (@lem77274 n)). Qed.
Lemma lem77281 : term4 = (NUMERAL 0).
Proof. exact (@lem77280 (NUMERAL 0)). Qed.
Lemma lem77282 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77283 : term30 = term31.
Proof. exact (MK_COMB (@lem77282) (@lem77281)). Qed.
Lemma lem77284 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem77285 : (term4 = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem77283) (@lem77284)). Qed.
Lemma lem77287 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem77288 (x : nat) : (x = x) = True.
Proof. exact (@lem77287 nat x). Qed.
Lemma lem77289 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem77288 (NUMERAL 0)). Qed.
Lemma lem77290 : (term4 = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem77285) (@lem77289)). Qed.
Lemma lem77291 : True = (term4 = (NUMERAL 0)).
Proof. exact (SYM (@lem77290)). Qed.
Lemma lem77292 : term4 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem77291) (@lem0)). Qed.
Lemma lem77293 : term32.
Proof. exact (proj2 (@lem77238)). Qed.
Lemma lem77294 (m : nat) : term33 m.
Proof. exact (@lem77293 m). Qed.
Lemma lem77295 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem77296 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem77295 m) (@lem77294 m)). Qed.
Lemma lem77297 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem77296 m n). Qed.
Lemma lem77298 (m : nat) (n : nat) : (term35 m n) = ((term36 m n) = (term37 m n)).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem77307 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (EQ_MP (@lem77298 m n) (@lem77297 m n)). Qed.
Lemma lem77308 (m : nat) : (term12 m) = (term38 m).
Proof. exact (@lem77307 m (NUMERAL 0)). Qed.
Lemma lem77310 (m : nat) (h1 : (term8 m) = m) : (term8 m) = m.
Proof. exact (h1). Qed.
Lemma lem77311 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem77312 (m : nat) (h1 : (term8 m) = m) : (term38 m) = (S m).
Proof. exact (MK_COMB (@lem77311) (@lem77310 m h1)). Qed.
Lemma lem77313 (m : nat) (h1 : (term8 m) = m) : (term12 m) = (S m).
Proof. exact (TRANS (@lem77308 m) (@lem77312 m h1)). Qed.
Lemma lem77314 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77315 (m : nat) (h1 : (term8 m) = m) : (term39 m) = (term40 m).
Proof. exact (MK_COMB (@lem77314) (@lem77313 m h1)). Qed.
Lemma lem77316 (m : nat) : (S m) = (S m).
Proof. exact (eq_refl (S m)). Qed.
Lemma lem77317 (m : nat) (h1 : (term8 m) = m) : ((term12 m) = (S m)) = ((S m) = (S m)).
Proof. exact (MK_COMB (@lem77315 m h1) (@lem77316 m)). Qed.
Lemma lem77319 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem77320 (x : nat) : (x = x) = True.
Proof. exact (@lem77319 nat x). Qed.
Lemma lem77321 (m : nat) : ((S m) = (S m)) = True.
Proof. exact (@lem77320 (S m)). Qed.
Lemma lem77322 (m : nat) (h1 : (term8 m) = m) : ((term12 m) = (S m)) = True.
Proof. exact (TRANS (@lem77317 m h1) (@lem77321 m)). Qed.
Lemma lem77323 (m : nat) (h1 : (term8 m) = m) : True = ((term12 m) = (S m)).
Proof. exact (SYM (@lem77322 m h1)). Qed.
Lemma lem77324 (m : nat) (h1 : (term8 m) = m) : (term12 m) = (S m).
Proof. exact (EQ_MP (@lem77323 m h1) (@lem0)). Qed.
Lemma lem77325 (m : nat) : term14 m.
Proof. exact (fun h0 : (term8 m) = m => @lem77324 m h0). Qed.
Lemma lem77330 : term18.
Proof. exact (fun m : nat => @lem77325 m). Qed.
Lemma lem77331 : term20.
Proof. exact (conj (@lem77292) (@lem77330)). Qed.
Lemma lem77332 : term25.
Proof. exact (@lem77264 (@lem77331)). Qed.
