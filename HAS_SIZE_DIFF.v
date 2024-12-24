Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_DIFF_term_abbrevs.
Require Import CARD_DIFF_spec.
Require Import FINITE_DIFF_spec.
Require Import HAS_SIZE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem3868181 {_99873 : Type'} (s : _99873 -> Prop) : term0 _99873 s.
Proof. exact (@lem3854223 _99873 s). Qed.
Lemma lem3868182 {_99873 : Type'} (s : _99873 -> Prop) : (term0 _99873 s) = (term1 _99873 s).
Proof. exact (eq_refl (term0 _99873 s)). Qed.
Lemma lem3868183 {_99873 : Type'} (s : _99873 -> Prop) : term1 _99873 s.
Proof. exact (EQ_MP (@lem3868182 _99873 s) (@lem3868181 _99873 s)). Qed.
Lemma lem3868184 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : term2 _99873 s t.
Proof. exact (@lem3868183 _99873 s t). Qed.
Lemma lem3868185 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : (term2 _99873 s t) = (term3 _99873 s t).
Proof. exact (eq_refl (term2 _99873 s t)). Qed.
Lemma lem3868186 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : term3 _99873 s t.
Proof. exact (EQ_MP (@lem3868185 _99873 s t) (@lem3868184 _99873 s t)). Qed.
Lemma lem3868187 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term4 _99873 t s) : term4 _99873 t s.
Proof. exact (h1). Qed.
Lemma lem3868188 {_99873 : Type'} (t : _99873 -> Prop) (s : _99873 -> Prop) (h1 : term4 _99873 t s) : (term5 _99873 s t) = (term6 _99873 s t).
Proof. exact (@lem3868186 _99873 s t (@lem3868187 _99873 t s h1)). Qed.
Lemma lem3868194 {_97970 : Type'} (s : _97970 -> Prop) : term7 _97970 s.
Proof. exact (@lem3734933 _97970 s). Qed.
Lemma lem3868195 {_97970 : Type'} (s : _97970 -> Prop) : (term7 _97970 s) = (term8 _97970 s).
Proof. exact (eq_refl (term7 _97970 s)). Qed.
Lemma lem3868196 {_97970 : Type'} (s : _97970 -> Prop) : term8 _97970 s.
Proof. exact (EQ_MP (@lem3868195 _97970 s) (@lem3868194 _97970 s)). Qed.
Lemma lem3868197 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term9 _97970 s t.
Proof. exact (@lem3868196 _97970 s t). Qed.
Lemma lem3868198 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term9 _97970 s t) = (term10 _97970 s t).
Proof. exact (eq_refl (term9 _97970 s t)). Qed.
Lemma lem3868199 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term10 _97970 s t.
Proof. exact (EQ_MP (@lem3868198 _97970 s t) (@lem3868197 _97970 s t)). Qed.
Lemma lem3868200 {_97970 : Type'} (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : @FINITE _97970 s.
Proof. exact (h1). Qed.
Lemma lem3868201 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : term11 _97970 s t.
Proof. exact (@lem3868199 _97970 s t (@lem3868200 _97970 s h1)). Qed.
Lemma lem3868202 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : (term11 _97970 s t) = ((term11 _97970 s t) = True).
Proof. exact (@lem7 (term11 _97970 s t)). Qed.
Lemma lem3868203 {_97970 : Type'} (t : _97970 -> Prop) (s : _97970 -> Prop) (h1 : @FINITE _97970 s) : (term11 _97970 s t) = True.
Proof. exact (EQ_MP (@lem3868202 _97970 s t) (@lem3868201 _97970 t s h1)). Qed.
Lemma lem3868209 {_100044 : Type'} (s : _100044 -> Prop) : term12 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem3868210 {_100044 : Type'} (s : _100044 -> Prop) : (term12 _100044 s) = (term13 _100044 s).
Proof. exact (eq_refl (term12 _100044 s)). Qed.
Lemma lem3868211 {_100044 : Type'} (s : _100044 -> Prop) : term13 _100044 s.
Proof. exact (EQ_MP (@lem3868210 _100044 s) (@lem3868209 _100044 s)). Qed.
Lemma lem3868212 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term14 _100044 s n.
Proof. exact (@lem3868211 _100044 s n). Qed.
Lemma lem3868213 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term14 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term15 _100044 s n)).
Proof. exact (eq_refl (term14 _100044 s n)). Qed.
Lemma lem3868234 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term16 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3868235 (p : Prop) (q : Prop) (p' : Prop) : term17 p q p'.
Proof. exact (fun q' : Prop => @lem3868234 p q p' q'). Qed.
Lemma lem3868236 (p : Prop) (q : Prop) : term18 p q.
Proof. exact (fun p' : Prop => @lem3868235 p q p'). Qed.
Lemma lem3868237 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) (n : nat) : term19 _100233 s t m n.
Proof. exact (@lem3868236 (term20 _100233 m n t s) (term21 _100233 s t m n)). Qed.
Lemma lem3868238 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) (n : nat) (p' : Prop) : term22 _100233 s t m n p'.
Proof. exact (@lem3868237 _100233 s t m n p'). Qed.
Lemma lem3868239 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) (n : nat) (p' : Prop) : (term22 _100233 s t m n p') = (term23 _100233 s t m n p').
Proof. exact (eq_refl (term22 _100233 s t m n p')). Qed.
Lemma lem3868240 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) (n : nat) (p' : Prop) : term23 _100233 s t m n p'.
Proof. exact (EQ_MP (@lem3868239 _100233 s t m n p') (@lem3868238 _100233 s t m n p')). Qed.
Lemma lem3868241 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term24 _100233 s t m n p' q'.
Proof. exact (@lem3868240 _100233 s t m n p' q'). Qed.
Lemma lem3868242 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term24 _100233 s t m n p' q') = (term25 _100233 s t m n p' q').
Proof. exact (eq_refl (term24 _100233 s t m n p' q')). Qed.
Lemma lem3868243 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term25 _100233 s t m n p' q'.
Proof. exact (EQ_MP (@lem3868242 _100233 s t m n p' q') (@lem3868241 _100233 s t m n p' q')). Qed.
Lemma lem3868247 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term15 _100044 s n).
Proof. exact (EQ_MP (@lem3868213 _100044 s n) (@lem3868212 _100044 s n)). Qed.
Lemma lem3868248 {_100233 : Type'} (s : _100233 -> Prop) (n : nat) : (@HAS_SIZE _100233 s n) = (term15 _100233 s n).
Proof. exact (@lem3868247 _100233 s n). Qed.
Lemma lem3868249 {_100233 : Type'} (s : _100233 -> Prop) (m : nat) : (@HAS_SIZE _100233 s m) = (term15 _100233 s m).
Proof. exact (@lem3868248 _100233 s m). Qed.
Lemma lem3868254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3868255 {_100233 : Type'} (s : _100233 -> Prop) (m : nat) : (term26 _100233 s m) = (term27 _100233 s m).
Proof. exact (MK_COMB (@lem3868254) (@lem3868249 _100233 s m)). Qed.
Lemma lem3868263 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term15 _100044 s n).
Proof. exact (EQ_MP (@lem3868213 _100044 s n) (@lem3868212 _100044 s n)). Qed.
Lemma lem3868264 {_100233 : Type'} (s : _100233 -> Prop) (n : nat) : (@HAS_SIZE _100233 s n) = (term15 _100233 s n).
Proof. exact (@lem3868263 _100233 s n). Qed.
Lemma lem3868265 {_100233 : Type'} (t : _100233 -> Prop) (n : nat) : (@HAS_SIZE _100233 t n) = (term15 _100233 t n).
Proof. exact (@lem3868264 _100233 t n). Qed.
Lemma lem3868270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3868271 {_100233 : Type'} (t : _100233 -> Prop) (n : nat) : (term26 _100233 t n) = (term27 _100233 t n).
Proof. exact (MK_COMB (@lem3868270) (@lem3868265 _100233 t n)). Qed.
Lemma lem3868276 {_100233 : Type'} (t : _100233 -> Prop) (s : _100233 -> Prop) : (@SUBSET _100233 t s) = (@SUBSET _100233 t s).
Proof. exact (eq_refl (@SUBSET _100233 t s)). Qed.
Lemma lem3868277 {_100233 : Type'} (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) : (term28 _100233 n t s) = (term29 _100233 n t s).
Proof. exact (MK_COMB (@lem3868271 _100233 t n) (@lem3868276 _100233 t s)). Qed.
Lemma lem3868284 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) : (term20 _100233 m n t s) = (term30 _100233 m n t s).
Proof. exact (MK_COMB (@lem3868255 _100233 s m) (@lem3868277 _100233 n t s)). Qed.
Lemma lem3868297 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (q' : Prop) : term31 _100233 m n t s q'.
Proof. exact (@lem3868243 _100233 s t m n (term30 _100233 m n t s) q'). Qed.
Lemma lem3868298 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (q' : Prop) : term32 _100233 m n t s q'.
Proof. exact (@lem3868297 _100233 m n t s q' (@lem3868284 _100233 m n t s)). Qed.
Lemma lem3868299 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : term30 _100233 m n t s.
Proof. exact (h1). Qed.
Lemma lem3868300 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : term29 _100233 n t s.
Proof. exact (proj2 (@lem3868299 _100233 m n t s h1)). Qed.
Lemma lem3868301 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : @SUBSET _100233 t s.
Proof. exact (proj2 (@lem3868300 _100233 m n t s h1)). Qed.
Lemma lem3868302 {_100233 : Type'} (t : _100233 -> Prop) (s : _100233 -> Prop) : (@SUBSET _100233 t s) = ((@SUBSET _100233 t s) = True).
Proof. exact (@lem7 (@SUBSET _100233 t s)). Qed.
Lemma lem3868304 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : term15 _100233 t n.
Proof. exact (proj1 (@lem3868300 _100233 m n t s h1)). Qed.
Lemma lem3868309 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : term15 _100233 s m.
Proof. exact (proj1 (@lem3868299 _100233 m n t s h1)). Qed.
Lemma lem3868311 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : @FINITE _100233 s.
Proof. exact (proj1 (@lem3868309 _100233 m n t s h1)). Qed.
Lemma lem3868312 {_100233 : Type'} (s : _100233 -> Prop) : (@FINITE _100233 s) = ((@FINITE _100233 s) = True).
Proof. exact (@lem7 (@FINITE _100233 s)). Qed.
Lemma lem3868315 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term15 _100044 s n).
Proof. exact (EQ_MP (@lem3868213 _100044 s n) (@lem3868212 _100044 s n)). Qed.
Lemma lem3868316 {_100233 : Type'} (s : _100233 -> Prop) (n : nat) : (@HAS_SIZE _100233 s n) = (term15 _100233 s n).
Proof. exact (@lem3868315 _100233 s n). Qed.
Lemma lem3868317 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) (n : nat) : (term21 _100233 s t m n) = (term33 _100233 s t m n).
Proof. exact (@lem3868316 _100233 (@DIFF _100233 s t) (Nat.sub m n)). Qed.
Lemma lem3868321 {_97970 : Type'} (s : _97970 -> Prop) (t : _97970 -> Prop) : term34 _97970 s t.
Proof. exact (fun h0 : @FINITE _97970 s => @lem3868203 _97970 t s h0). Qed.
Lemma lem3868322 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) : term34 _100233 s t.
Proof. exact (@lem3868321 _100233 s t). Qed.
Lemma lem3868324 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (@FINITE _100233 s) = True.
Proof. exact (EQ_MP (@lem3868312 _100233 s) (@lem3868311 _100233 m n t s h1)). Qed.
Lemma lem3868325 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : True = (@FINITE _100233 s).
Proof. exact (SYM (@lem3868324 _100233 m n t s h1)). Qed.
Lemma lem3868326 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : @FINITE _100233 s.
Proof. exact (EQ_MP (@lem3868325 _100233 m n t s h1) (@lem0)). Qed.
Lemma lem3868327 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term11 _100233 s t) = True.
Proof. exact (@lem3868322 _100233 s t (@lem3868326 _100233 m n t s h1)). Qed.
Lemma lem3868328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3868329 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term35 _100233 s t) = (and True).
Proof. exact (MK_COMB (@lem3868328) (@lem3868327 _100233 m n t s h1)). Qed.
Lemma lem3868333 {_99873 : Type'} (s : _99873 -> Prop) (t : _99873 -> Prop) : term3 _99873 s t.
Proof. exact (fun h0 : term4 _99873 t s => @lem3868188 _99873 t s h0). Qed.
Lemma lem3868334 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) : term3 _100233 s t.
Proof. exact (@lem3868333 _100233 s t). Qed.
Lemma lem3868338 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (@FINITE _100233 s) = True.
Proof. exact (EQ_MP (@lem3868312 _100233 s) (@lem3868311 _100233 m n t s h1)). Qed.
Lemma lem3868339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3868340 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term36 _100233 s) = (and True).
Proof. exact (MK_COMB (@lem3868339) (@lem3868338 _100233 m n t s h1)). Qed.
Lemma lem3868342 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (@SUBSET _100233 t s) = True.
Proof. exact (EQ_MP (@lem3868302 _100233 t s) (@lem3868301 _100233 m n t s h1)). Qed.
Lemma lem3868343 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term4 _100233 t s) = (True /\ True).
Proof. exact (MK_COMB (@lem3868340 _100233 m n t s h1) (@lem3868342 _100233 m n t s h1)). Qed.
Lemma lem3868345 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3868346 : (True /\ True) = True.
Proof. exact (@lem3868345 True). Qed.
Lemma lem3868347 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term4 _100233 t s) = True.
Proof. exact (TRANS (@lem3868343 _100233 m n t s h1) (@lem3868346)). Qed.
Lemma lem3868348 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : True = (term4 _100233 t s).
Proof. exact (SYM (@lem3868347 _100233 m n t s h1)). Qed.
Lemma lem3868349 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : term4 _100233 t s.
Proof. exact (EQ_MP (@lem3868348 _100233 m n t s h1) (@lem0)). Qed.
Lemma lem3868350 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term5 _100233 s t) = (term6 _100233 s t).
Proof. exact (@lem3868334 _100233 s t (@lem3868349 _100233 m n t s h1)). Qed.
Lemma lem3868352 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (@CARD _100233 s) = m.
Proof. exact (proj2 (@lem3868309 _100233 m n t s h1)). Qed.
Lemma lem3868353 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem3868354 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term37 _100233 s) = (Nat.sub m).
Proof. exact (MK_COMB (@lem3868353) (@lem3868352 _100233 m n t s h1)). Qed.
Lemma lem3868356 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (@CARD _100233 t) = n.
Proof. exact (proj2 (@lem3868304 _100233 m n t s h1)). Qed.
Lemma lem3868357 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term6 _100233 s t) = (Nat.sub m n).
Proof. exact (MK_COMB (@lem3868354 _100233 m n t s h1) (@lem3868356 _100233 m n t s h1)). Qed.
Lemma lem3868358 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term5 _100233 s t) = (Nat.sub m n).
Proof. exact (TRANS (@lem3868350 _100233 m n t s h1) (@lem3868357 _100233 m n t s h1)). Qed.
Lemma lem3868359 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3868360 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term38 _100233 s t) = (term39 m n).
Proof. exact (MK_COMB (@lem3868359) (@lem3868358 _100233 m n t s h1)). Qed.
Lemma lem3868361 (m : nat) (n : nat) : (Nat.sub m n) = (Nat.sub m n).
Proof. exact (eq_refl (Nat.sub m n)). Qed.
Lemma lem3868362 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : ((term5 _100233 s t) = (Nat.sub m n)) = ((Nat.sub m n) = (Nat.sub m n)).
Proof. exact (MK_COMB (@lem3868360 _100233 m n t s h1) (@lem3868361 m n)). Qed.
Lemma lem3868364 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3868365 (x : nat) : (x = x) = True.
Proof. exact (@lem3868364 nat x). Qed.
Lemma lem3868366 (m : nat) (n : nat) : ((Nat.sub m n) = (Nat.sub m n)) = True.
Proof. exact (@lem3868365 (Nat.sub m n)). Qed.
Lemma lem3868367 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : ((term5 _100233 s t) = (Nat.sub m n)) = True.
Proof. exact (TRANS (@lem3868362 _100233 m n t s h1) (@lem3868366 m n)). Qed.
Lemma lem3868368 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term33 _100233 s t m n) = (True /\ True).
Proof. exact (MK_COMB (@lem3868329 _100233 m n t s h1) (@lem3868367 _100233 m n t s h1)). Qed.
Lemma lem3868370 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3868371 : (True /\ True) = True.
Proof. exact (@lem3868370 True). Qed.
Lemma lem3868372 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term33 _100233 s t m n) = True.
Proof. exact (TRANS (@lem3868368 _100233 m n t s h1) (@lem3868371)). Qed.
Lemma lem3868373 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) (h1 : term30 _100233 m n t s) : (term21 _100233 s t m n) = True.
Proof. exact (TRANS (@lem3868317 _100233 s t m n) (@lem3868372 _100233 m n t s h1)). Qed.
Lemma lem3868374 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) (n : nat) : term40 _100233 s t m n.
Proof. exact (fun h0 : term30 _100233 m n t s => @lem3868373 _100233 m n t s h0). Qed.
Lemma lem3868375 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) : term41 _100233 m n t s.
Proof. exact (@lem3868298 _100233 m n t s True). Qed.
Lemma lem3868376 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) : (term42 _100233 s t m n) = (term43 _100233 m n t s).
Proof. exact (@lem3868375 _100233 m n t s (@lem3868374 _100233 s t m n)). Qed.
Lemma lem3868378 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3868379 {_100233 : Type'} (m : nat) (n : nat) (t : _100233 -> Prop) (s : _100233 -> Prop) : (term43 _100233 m n t s) = True.
Proof. exact (@lem3868378 (term30 _100233 m n t s)). Qed.
Lemma lem3868380 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) (n : nat) : (term42 _100233 s t m n) = True.
Proof. exact (TRANS (@lem3868376 _100233 m n t s) (@lem3868379 _100233 m n t s)). Qed.
Lemma lem3868381 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) : (term44 _100233 s t m) = term45.
Proof. exact (fun_ext (fun n : nat => @lem3868380 _100233 s t m n)). Qed.
Lemma lem3868382 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3868383 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) : (term46 _100233 s t m) = term47.
Proof. exact (MK_COMB (@lem3868382) (@lem3868381 _100233 s t m)). Qed.
Lemma lem3868385 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3868386 (t : Prop) : (term49 t) = t.
Proof. exact (@lem3868385 nat t). Qed.
Lemma lem3868387 : term47 = True.
Proof. exact (@lem3868386 True). Qed.
Lemma lem3868388 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) (m : nat) : (term46 _100233 s t m) = True.
Proof. exact (TRANS (@lem3868383 _100233 s t m) (@lem3868387)). Qed.
Lemma lem3868389 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) : (term50 _100233 s t) = term45.
Proof. exact (fun_ext (fun m : nat => @lem3868388 _100233 s t m)). Qed.
Lemma lem3868390 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3868391 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) : (term51 _100233 s t) = term47.
Proof. exact (MK_COMB (@lem3868390) (@lem3868389 _100233 s t)). Qed.
Lemma lem3868393 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3868394 (t : Prop) : (term49 t) = t.
Proof. exact (@lem3868393 nat t). Qed.
Lemma lem3868395 : term47 = True.
Proof. exact (@lem3868394 True). Qed.
Lemma lem3868396 {_100233 : Type'} (s : _100233 -> Prop) (t : _100233 -> Prop) : (term51 _100233 s t) = True.
Proof. exact (TRANS (@lem3868391 _100233 s t) (@lem3868395)). Qed.
Lemma lem3868397 {_100233 : Type'} (s : _100233 -> Prop) : (term52 _100233 s) = (term53 _100233).
Proof. exact (fun_ext (fun t : _100233 -> Prop => @lem3868396 _100233 s t)). Qed.
Lemma lem3868398 {_100233 : Type'} : (@all (_100233 -> Prop)) = (@all (_100233 -> Prop)).
Proof. exact (eq_refl (@all (_100233 -> Prop))). Qed.
Lemma lem3868399 {_100233 : Type'} (s : _100233 -> Prop) : (term54 _100233 s) = (term55 _100233).
Proof. exact (MK_COMB (@lem3868398 _100233) (@lem3868397 _100233 s)). Qed.
Lemma lem3868401 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3868402 {_100233 : Type'} (t : Prop) : (term56 _100233 t) = t.
Proof. exact (@lem3868401 (_100233 -> Prop) t). Qed.
Lemma lem3868403 {_100233 : Type'} : (term55 _100233) = True.
Proof. exact (@lem3868402 _100233 True). Qed.
Lemma lem3868404 {_100233 : Type'} (s : _100233 -> Prop) : (term54 _100233 s) = True.
Proof. exact (TRANS (@lem3868399 _100233 s) (@lem3868403 _100233)). Qed.
Lemma lem3868405 {_100233 : Type'} : (term57 _100233) = (term53 _100233).
Proof. exact (fun_ext (fun s : _100233 -> Prop => @lem3868404 _100233 s)). Qed.
Lemma lem3868406 {_100233 : Type'} : (@all (_100233 -> Prop)) = (@all (_100233 -> Prop)).
Proof. exact (eq_refl (@all (_100233 -> Prop))). Qed.
Lemma lem3868407 {_100233 : Type'} : (term58 _100233) = (term55 _100233).
Proof. exact (MK_COMB (@lem3868406 _100233) (@lem3868405 _100233)). Qed.
Lemma lem3868409 {A : Type'} (t : Prop) : (term48 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3868410 {_100233 : Type'} (t : Prop) : (term56 _100233 t) = t.
Proof. exact (@lem3868409 (_100233 -> Prop) t). Qed.
Lemma lem3868411 {_100233 : Type'} : (term55 _100233) = True.
Proof. exact (@lem3868410 _100233 True). Qed.
Lemma lem3868412 {_100233 : Type'} : (term58 _100233) = True.
Proof. exact (TRANS (@lem3868407 _100233) (@lem3868411 _100233)). Qed.
Lemma lem3868413 {_100233 : Type'} : True = (term58 _100233).
Proof. exact (SYM (@lem3868412 _100233)). Qed.
Lemma lem3868414 {_100233 : Type'} : term58 _100233.
Proof. exact (EQ_MP (@lem3868413 _100233) (@lem0)). Qed.
