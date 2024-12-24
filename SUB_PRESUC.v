Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUB_PRESUC_term_abbrevs.
Require Import thm0_spec.
Require Import thm135075_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm76885_spec.
Lemma lem135233 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem135234 (m : nat) : term1 m.
Proof. exact (@lem135233 (term2 m)). Qed.
Lemma lem135235 (m : nat) : (term3 m) = ((term4 m) = (term5 m)).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem135236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem135237 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem135236) (@lem135235 m)). Qed.
Lemma lem135238 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem135239 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135240 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem135239) (@lem135238 m n)). Qed.
Lemma lem135241 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (term14 m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem135242 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (MK_COMB (@lem135240 m n) (@lem135241 m n)). Qed.
Lemma lem135243 (m : nat) : (term17 m) = (term18 m).
Proof. exact (fun_ext (fun n : nat => @lem135242 m n)). Qed.
Lemma lem135244 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135245 (m : nat) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem135244) (@lem135243 m)). Qed.
Lemma lem135246 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem135237 m) (@lem135245 m)). Qed.
Lemma lem135247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135248 (m : nat) : (term23 m) = (term24 m).
Proof. exact (MK_COMB (@lem135247) (@lem135246 m)). Qed.
Lemma lem135249 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem135250 (m : nat) : (term25 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem135249 m n)). Qed.
Lemma lem135251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135252 (m : nat) : (term26 m) = (term27 m).
Proof. exact (MK_COMB (@lem135251) (@lem135250 m)). Qed.
Lemma lem135253 (m : nat) : (term1 m) = (term28 m).
Proof. exact (MK_COMB (@lem135248 m) (@lem135252 m)). Qed.
Lemma lem135254 (m : nat) : term28 m.
Proof. exact (EQ_MP (@lem135253 m) (@lem135234 m)). Qed.
Lemma lem135256 : term29.
Proof. exact (proj2 (@lem76885)). Qed.
Lemma lem135257 (n : nat) : term30 n.
Proof. exact (@lem135256 n). Qed.
Lemma lem135258 (n : nat) : (term30 n) = ((term31 n) = n).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem135268 : term32.
Proof. exact (proj1 (@lem135075)). Qed.
Lemma lem135269 (m : nat) : term33 m.
Proof. exact (@lem135268 m). Qed.
Lemma lem135270 (m : nat) : (term33 m) = ((term5 m) = m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem135275 (m : nat) : (term5 m) = m.
Proof. exact (EQ_MP (@lem135270 m) (@lem135269 m)). Qed.
Lemma lem135276 (m : nat) : (term34 m) = (S m).
Proof. exact (@lem135275 (S m)). Qed.
Lemma lem135277 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem135278 (m : nat) : (term4 m) = (term31 m).
Proof. exact (MK_COMB (@lem135277) (@lem135276 m)). Qed.
Lemma lem135280 (n : nat) : (term31 n) = n.
Proof. exact (EQ_MP (@lem135258 n) (@lem135257 n)). Qed.
Lemma lem135281 (m : nat) : (term31 m) = m.
Proof. exact (@lem135280 m). Qed.
Lemma lem135282 (m : nat) : (term4 m) = m.
Proof. exact (TRANS (@lem135278 m) (@lem135281 m)). Qed.
Lemma lem135283 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135284 (m : nat) : (term35 m) = (@eq nat m).
Proof. exact (MK_COMB (@lem135283) (@lem135282 m)). Qed.
Lemma lem135286 (m : nat) : (term5 m) = m.
Proof. exact (EQ_MP (@lem135270 m) (@lem135269 m)). Qed.
Lemma lem135287 (m : nat) : ((term4 m) = (term5 m)) = (m = m).
Proof. exact (MK_COMB (@lem135284 m) (@lem135286 m)). Qed.
Lemma lem135289 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135290 (x : nat) : (x = x) = True.
Proof. exact (@lem135289 nat x). Qed.
Lemma lem135291 (m : nat) : (m = m) = True.
Proof. exact (@lem135290 m). Qed.
Lemma lem135292 (m : nat) : ((term4 m) = (term5 m)) = True.
Proof. exact (TRANS (@lem135287 m) (@lem135291 m)). Qed.
Lemma lem135293 (m : nat) : True = ((term4 m) = (term5 m)).
Proof. exact (SYM (@lem135292 m)). Qed.
Lemma lem135294 (m : nat) : (term4 m) = (term5 m).
Proof. exact (EQ_MP (@lem135293 m) (@lem0)). Qed.
Lemma lem135300 : term36.
Proof. exact (proj2 (@lem135075)). Qed.
Lemma lem135301 (m : nat) : term37 m.
Proof. exact (@lem135300 m). Qed.
Lemma lem135302 (m : nat) : (term37 m) = (term38 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem135303 (m : nat) : term38 m.
Proof. exact (EQ_MP (@lem135302 m) (@lem135301 m)). Qed.
Lemma lem135304 (m : nat) (n : nat) : term39 m n.
Proof. exact (@lem135303 m n). Qed.
Lemma lem135305 (m : nat) (n : nat) : (term39 m n) = ((term14 m n) = (term40 m n)).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem135314 (m : nat) (n : nat) : (term14 m n) = (term40 m n).
Proof. exact (EQ_MP (@lem135305 m n) (@lem135304 m n)). Qed.
Lemma lem135315 (m : nat) (n : nat) : (term41 m n) = (term9 m n).
Proof. exact (@lem135314 (S m) n). Qed.
Lemma lem135317 (m : nat) (n : nat) (h1 : (term9 m n) = (Nat.sub m n)) : (term9 m n) = (Nat.sub m n).
Proof. exact (h1). Qed.
Lemma lem135318 (m : nat) (n : nat) (h1 : (term9 m n) = (Nat.sub m n)) : (term41 m n) = (Nat.sub m n).
Proof. exact (TRANS (@lem135315 m n) (@lem135317 m n h1)). Qed.
Lemma lem135319 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem135320 (m : nat) (n : nat) (h1 : (term9 m n) = (Nat.sub m n)) : (term13 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem135319) (@lem135318 m n h1)). Qed.
Lemma lem135321 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135322 (m : nat) (n : nat) (h1 : (term9 m n) = (Nat.sub m n)) : (term42 m n) = (term43 m n).
Proof. exact (MK_COMB (@lem135321) (@lem135320 m n h1)). Qed.
Lemma lem135324 (m : nat) (n : nat) : (term14 m n) = (term40 m n).
Proof. exact (EQ_MP (@lem135305 m n) (@lem135304 m n)). Qed.
Lemma lem135325 (m : nat) (n : nat) (h1 : (term9 m n) = (Nat.sub m n)) : ((term13 m n) = (term14 m n)) = ((term40 m n) = (term40 m n)).
Proof. exact (MK_COMB (@lem135322 m n h1) (@lem135324 m n)). Qed.
Lemma lem135327 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135328 (x : nat) : (x = x) = True.
Proof. exact (@lem135327 nat x). Qed.
Lemma lem135329 (m : nat) (n : nat) : ((term40 m n) = (term40 m n)) = True.
Proof. exact (@lem135328 (term40 m n)). Qed.
Lemma lem135330 (m : nat) (n : nat) (h1 : (term9 m n) = (Nat.sub m n)) : ((term13 m n) = (term14 m n)) = True.
Proof. exact (TRANS (@lem135325 m n h1) (@lem135329 m n)). Qed.
Lemma lem135331 (m : nat) (n : nat) (h1 : (term9 m n) = (Nat.sub m n)) : True = ((term13 m n) = (term14 m n)).
Proof. exact (SYM (@lem135330 m n h1)). Qed.
Lemma lem135332 (m : nat) (n : nat) (h1 : (term9 m n) = (Nat.sub m n)) : (term13 m n) = (term14 m n).
Proof. exact (EQ_MP (@lem135331 m n h1) (@lem0)). Qed.
Lemma lem135333 (m : nat) (n : nat) : term16 m n.
Proof. exact (fun h0 : (term9 m n) = (Nat.sub m n) => @lem135332 m n h0). Qed.
Lemma lem135338 (m : nat) : term20 m.
Proof. exact (fun n : nat => @lem135333 m n). Qed.
Lemma lem135339 (m : nat) : term22 m.
Proof. exact (conj (@lem135294 m) (@lem135338 m)). Qed.
Lemma lem135340 (m : nat) : term27 m.
Proof. exact (@lem135254 m (@lem135339 m)). Qed.
Lemma lem135345 : term44.
Proof. exact (fun m : nat => @lem135340 m). Qed.
