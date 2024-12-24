Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1257676_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1257160 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1257161 (m : nat) (n : nat) : (Nat.add n m) = (Nat.add m n).
Proof. exact (@lem1257160 m n). Qed.
Lemma lem1257164 (m : nat) (n : nat) : (term0 m n) = (term0 m n).
Proof. exact (eq_refl (term0 m n)). Qed.
Lemma lem1257165 (m : nat) (n : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add m n)).
Proof. exact (MK_COMB (@lem1257164 m n) (@lem1257161 m n)). Qed.
Lemma lem1257167 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1257168 (x : nat) : (x = x) = True.
Proof. exact (@lem1257167 nat x). Qed.
Lemma lem1257169 (m : nat) (n : nat) : ((Nat.add m n) = (Nat.add m n)) = True.
Proof. exact (@lem1257168 (Nat.add m n)). Qed.
Lemma lem1257170 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = True.
Proof. exact (TRANS (@lem1257165 m n) (@lem1257169 m n)). Qed.
Lemma lem1257171 (n : nat) (m : nat) : True = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (SYM (@lem1257170 n m)). Qed.
Lemma lem1257172 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1257171 n m) (@lem0)). Qed.
Lemma lem1257176 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1257177 (m : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : (term3 m d''' n d'' d') = (term4 m d''' n d'' d').
Proof. exact (@lem1257176 (term5 m d' d'' d''') (Nat.add n d'') d'). Qed.
Lemma lem1257179 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1257180 (m : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : (term4 m d''' n d'' d') = (term6 m d''' n d'' d').
Proof. exact (@lem1257179 m (term7 d' d'' d''') (term1 n d'' d')). Qed.
Lemma lem1257187 (m : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : (term3 m d''' n d'' d') = (term6 m d''' n d'' d').
Proof. exact (TRANS (@lem1257177 m d''' n d'' d') (@lem1257180 m d''' n d'' d')). Qed.
Lemma lem1257189 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1257190 (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : (term8 d''' n d'' d') = (term9 d''' n d'' d').
Proof. exact (@lem1257189 (Nat.add d' d'') (S d''') (term1 n d'' d')). Qed.
Lemma lem1257192 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1257193 (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : (term9 d''' n d'' d') = (term10 d''' n d'' d').
Proof. exact (@lem1257192 d' d'' (term11 d''' n d'' d')). Qed.
Lemma lem1257200 (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : (term8 d''' n d'' d') = (term10 d''' n d'' d').
Proof. exact (TRANS (@lem1257190 d''' n d'' d') (@lem1257193 d''' n d'' d')). Qed.
Lemma lem1257214 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1257215 (n : nat) (d'' : nat) (d' : nat) : (term1 n d'' d') = (term2 n d'' d').
Proof. exact (@lem1257214 n d'' d'). Qed.
Lemma lem1257217 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257218 (d'' : nat) (n : nat) (d' : nat) : (term2 n d'' d') = (term2 d'' n d').
Proof. exact (@lem1257217 d'' n d'). Qed.
Lemma lem1257225 (d'' : nat) (n : nat) (d' : nat) : (term1 n d'' d') = (term2 d'' n d').
Proof. exact (TRANS (@lem1257215 n d'' d') (@lem1257218 d'' n d')). Qed.
Lemma lem1257227 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1257228 (d' : nat) (n : nat) : (Nat.add n d') = (Nat.add d' n).
Proof. exact (@lem1257227 d' n). Qed.
Lemma lem1257232 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1257233 (d'' : nat) (d' : nat) (n : nat) : (term2 d'' n d') = (term2 d'' d' n).
Proof. exact (MK_COMB (@lem1257232 d'') (@lem1257228 d' n)). Qed.
Lemma lem1257235 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257236 (d' : nat) (d'' : nat) (n : nat) : (term2 d'' d' n) = (term2 d' d'' n).
Proof. exact (@lem1257235 d' d'' n). Qed.
Lemma lem1257246 (d' : nat) (d'' : nat) (n : nat) : (term2 d'' n d') = (term2 d' d'' n).
Proof. exact (TRANS (@lem1257233 d'' d' n) (@lem1257236 d' d'' n)). Qed.
Lemma lem1257247 (d' : nat) (d'' : nat) (n : nat) : (term1 n d'' d') = (term2 d' d'' n).
Proof. exact (TRANS (@lem1257225 d'' n d') (@lem1257246 d' d'' n)). Qed.
Lemma lem1257248 (d''' : nat) : (term12 d''') = (term12 d''').
Proof. exact (eq_refl (term12 d''')). Qed.
Lemma lem1257249 (d''' : nat) (d' : nat) (d'' : nat) (n : nat) : (term11 d''' n d'' d') = (term13 d''' d' d'' n).
Proof. exact (MK_COMB (@lem1257248 d''') (@lem1257247 d' d'' n)). Qed.
Lemma lem1257251 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257252 (d' : nat) (d''' : nat) (d'' : nat) (n : nat) : (term13 d''' d' d'' n) = (term14 d' d''' d'' n).
Proof. exact (@lem1257251 d' (S d''') (Nat.add d'' n)). Qed.
Lemma lem1257260 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257261 (d'' : nat) (d''' : nat) (n : nat) : (term15 d''' d'' n) = (term16 d'' d''' n).
Proof. exact (@lem1257260 d'' (S d''') n). Qed.
Lemma lem1257269 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1257270 (n : nat) (d''' : nat) : (term17 d''' n) = (term18 n d''').
Proof. exact (@lem1257269 n (S d''')). Qed.
Lemma lem1257274 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1257275 (d'' : nat) (n : nat) (d''' : nat) : (term16 d'' d''' n) = (term19 d'' n d''').
Proof. exact (MK_COMB (@lem1257274 d'') (@lem1257270 n d''')). Qed.
Lemma lem1257282 (d'' : nat) (n : nat) (d''' : nat) : (term15 d''' d'' n) = (term19 d'' n d''').
Proof. exact (TRANS (@lem1257261 d'' d''' n) (@lem1257275 d'' n d''')). Qed.
Lemma lem1257283 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257284 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term14 d' d''' d'' n) = (term20 d' d'' n d''').
Proof. exact (MK_COMB (@lem1257283 d') (@lem1257282 d'' n d''')). Qed.
Lemma lem1257291 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term13 d''' d' d'' n) = (term20 d' d'' n d''').
Proof. exact (TRANS (@lem1257252 d' d''' d'' n) (@lem1257284 d' d'' n d''')). Qed.
Lemma lem1257292 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term11 d''' n d'' d') = (term20 d' d'' n d''').
Proof. exact (TRANS (@lem1257249 d''' d' d'' n) (@lem1257291 d' d'' n d''')). Qed.
Lemma lem1257293 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1257294 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term21 d''' n d'' d') = (term22 d' d'' n d''').
Proof. exact (MK_COMB (@lem1257293 d'') (@lem1257292 d' d'' n d''')). Qed.
Lemma lem1257296 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257297 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term22 d' d'' n d''') = (term23 d' d'' n d''').
Proof. exact (@lem1257296 d' d'' (term19 d'' n d''')). Qed.
Lemma lem1257319 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term21 d''' n d'' d') = (term23 d' d'' n d''').
Proof. exact (TRANS (@lem1257294 d' d'' n d''') (@lem1257297 d' d'' n d''')). Qed.
Lemma lem1257320 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257321 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term10 d''' n d'' d') = (term24 d' d'' n d''').
Proof. exact (MK_COMB (@lem1257320 d') (@lem1257319 d' d'' n d''')). Qed.
Lemma lem1257328 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term8 d''' n d'' d') = (term24 d' d'' n d''').
Proof. exact (TRANS (@lem1257200 d''' n d'' d') (@lem1257321 d' d'' n d''')). Qed.
Lemma lem1257329 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1257330 (m : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term6 m d''' n d'' d') = (term25 m d' d'' n d''').
Proof. exact (MK_COMB (@lem1257329 m) (@lem1257328 d' d'' n d''')). Qed.
Lemma lem1257332 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257333 (m : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term25 m d' d'' n d''') = (term26 m d' d'' n d''').
Proof. exact (@lem1257332 d' m (term23 d' d'' n d''')). Qed.
Lemma lem1257341 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257342 (d' : nat) (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term27 m d' d'' n d''') = (term27 d' m d'' n d''').
Proof. exact (@lem1257341 d' m (term28 d'' n d''')). Qed.
Lemma lem1257350 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257351 (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term23 m d'' n d''') = (term22 m d'' n d''').
Proof. exact (@lem1257350 d'' m (term19 d'' n d''')). Qed.
Lemma lem1257359 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257360 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term20 m d'' n d''') = (term20 d'' m n d''').
Proof. exact (@lem1257359 d'' m (term18 n d''')). Qed.
Lemma lem1257376 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1257377 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term22 m d'' n d''') = (term29 d'' m n d''').
Proof. exact (MK_COMB (@lem1257376 d'') (@lem1257360 d'' m n d''')). Qed.
Lemma lem1257384 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term23 m d'' n d''') = (term29 d'' m n d''').
Proof. exact (TRANS (@lem1257351 m d'' n d''') (@lem1257377 d'' m n d''')). Qed.
Lemma lem1257385 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257386 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term27 d' m d'' n d''') = (term30 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1257385 d') (@lem1257384 d'' m n d''')). Qed.
Lemma lem1257393 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term27 m d' d'' n d''') = (term30 d' d'' m n d''').
Proof. exact (TRANS (@lem1257342 d' m d'' n d''') (@lem1257386 d' d'' m n d''')). Qed.
Lemma lem1257394 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257395 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term26 m d' d'' n d''') = (term31 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1257394 d') (@lem1257393 d' d'' m n d''')). Qed.
Lemma lem1257402 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term25 m d' d'' n d''') = (term31 d' d'' m n d''').
Proof. exact (TRANS (@lem1257333 m d' d'' n d''') (@lem1257395 d' d'' m n d''')). Qed.
Lemma lem1257403 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term6 m d''' n d'' d') = (term31 d' d'' m n d''').
Proof. exact (TRANS (@lem1257330 m d' d'' n d''') (@lem1257402 d' d'' m n d''')). Qed.
Lemma lem1257404 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term3 m d''' n d'' d') = (term31 d' d'' m n d''').
Proof. exact (TRANS (@lem1257187 m d''' n d'' d') (@lem1257403 d' d'' m n d''')). Qed.
Lemma lem1257405 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1257406 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term32 m d''' n d'' d') = (term33 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1257405) (@lem1257404 d' d'' m n d''')). Qed.
Lemma lem1257408 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257409 (m : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term34 n m d'' d' d''') = (term34 m n d'' d' d''').
Proof. exact (@lem1257408 m n (term35 d'' d' d''')). Qed.
Lemma lem1257417 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257418 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term36 n d'' d' d''') = (term37 n d'' d' d''').
Proof. exact (@lem1257417 d'' n (term38 d'' d' d''')). Qed.
Lemma lem1257426 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257427 (d'' : nat) (n : nat) (d' : nat) (d''' : nat) : (term39 n d'' d' d''') = (term39 d'' n d' d''').
Proof. exact (@lem1257426 d'' n (term40 d' d''')). Qed.
Lemma lem1257435 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257436 (n : nat) (d' : nat) (d''' : nat) : (term38 n d' d''') = (term41 n d' d''').
Proof. exact (@lem1257435 d' n (term18 d' d''')). Qed.
Lemma lem1257444 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257445 (d' : nat) (n : nat) (d''' : nat) : (term19 n d' d''') = (term19 d' n d''').
Proof. exact (@lem1257444 d' n (S d''')). Qed.
Lemma lem1257455 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257456 (d' : nat) (n : nat) (d''' : nat) : (term41 n d' d''') = (term28 d' n d''').
Proof. exact (MK_COMB (@lem1257455 d') (@lem1257445 d' n d''')). Qed.
Lemma lem1257463 (d' : nat) (n : nat) (d''' : nat) : (term38 n d' d''') = (term28 d' n d''').
Proof. exact (TRANS (@lem1257436 n d' d''') (@lem1257456 d' n d''')). Qed.
Lemma lem1257464 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1257465 (d'' : nat) (d' : nat) (n : nat) (d''' : nat) : (term39 d'' n d' d''') = (term23 d'' d' n d''').
Proof. exact (MK_COMB (@lem1257464 d'') (@lem1257463 d' n d''')). Qed.
Lemma lem1257467 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257468 (d'' : nat) (d' : nat) (n : nat) (d''' : nat) : (term23 d'' d' n d''') = (term22 d'' d' n d''').
Proof. exact (@lem1257467 d' d'' (term19 d' n d''')). Qed.
Lemma lem1257476 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257477 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term20 d'' d' n d''') = (term20 d' d'' n d''').
Proof. exact (@lem1257476 d' d'' (term18 n d''')). Qed.
Lemma lem1257493 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257494 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term22 d'' d' n d''') = (term29 d' d'' n d''').
Proof. exact (MK_COMB (@lem1257493 d') (@lem1257477 d' d'' n d''')). Qed.
Lemma lem1257501 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term23 d'' d' n d''') = (term29 d' d'' n d''').
Proof. exact (TRANS (@lem1257468 d'' d' n d''') (@lem1257494 d' d'' n d''')). Qed.
Lemma lem1257502 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term39 d'' n d' d''') = (term29 d' d'' n d''').
Proof. exact (TRANS (@lem1257465 d'' d' n d''') (@lem1257501 d' d'' n d''')). Qed.
Lemma lem1257503 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term39 n d'' d' d''') = (term29 d' d'' n d''').
Proof. exact (TRANS (@lem1257427 d'' n d' d''') (@lem1257502 d' d'' n d''')). Qed.
Lemma lem1257504 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1257505 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term37 n d'' d' d''') = (term42 d' d'' n d''').
Proof. exact (MK_COMB (@lem1257504 d'') (@lem1257503 d' d'' n d''')). Qed.
Lemma lem1257507 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257508 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term42 d' d'' n d''') = (term43 d' d'' n d''').
Proof. exact (@lem1257507 d' d'' (term20 d' d'' n d''')). Qed.
Lemma lem1257516 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257517 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term22 d' d'' n d''') = (term23 d' d'' n d''').
Proof. exact (@lem1257516 d' d'' (term19 d'' n d''')). Qed.
Lemma lem1257539 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257540 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term43 d' d'' n d''') = (term24 d' d'' n d''').
Proof. exact (MK_COMB (@lem1257539 d') (@lem1257517 d' d'' n d''')). Qed.
Lemma lem1257547 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term42 d' d'' n d''') = (term24 d' d'' n d''').
Proof. exact (TRANS (@lem1257508 d' d'' n d''') (@lem1257540 d' d'' n d''')). Qed.
Lemma lem1257548 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term37 n d'' d' d''') = (term24 d' d'' n d''').
Proof. exact (TRANS (@lem1257505 d' d'' n d''') (@lem1257547 d' d'' n d''')). Qed.
Lemma lem1257549 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term36 n d'' d' d''') = (term24 d' d'' n d''').
Proof. exact (TRANS (@lem1257418 n d'' d' d''') (@lem1257548 d' d'' n d''')). Qed.
Lemma lem1257550 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1257551 (m : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term34 m n d'' d' d''') = (term25 m d' d'' n d''').
Proof. exact (MK_COMB (@lem1257550 m) (@lem1257549 d' d'' n d''')). Qed.
Lemma lem1257553 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257554 (m : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term25 m d' d'' n d''') = (term26 m d' d'' n d''').
Proof. exact (@lem1257553 d' m (term23 d' d'' n d''')). Qed.
Lemma lem1257562 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257563 (d' : nat) (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term27 m d' d'' n d''') = (term27 d' m d'' n d''').
Proof. exact (@lem1257562 d' m (term28 d'' n d''')). Qed.
Lemma lem1257571 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257572 (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term23 m d'' n d''') = (term22 m d'' n d''').
Proof. exact (@lem1257571 d'' m (term19 d'' n d''')). Qed.
Lemma lem1257580 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257581 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term20 m d'' n d''') = (term20 d'' m n d''').
Proof. exact (@lem1257580 d'' m (term18 n d''')). Qed.
Lemma lem1257597 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1257598 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term22 m d'' n d''') = (term29 d'' m n d''').
Proof. exact (MK_COMB (@lem1257597 d'') (@lem1257581 d'' m n d''')). Qed.
Lemma lem1257605 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term23 m d'' n d''') = (term29 d'' m n d''').
Proof. exact (TRANS (@lem1257572 m d'' n d''') (@lem1257598 d'' m n d''')). Qed.
Lemma lem1257606 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257607 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term27 d' m d'' n d''') = (term30 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1257606 d') (@lem1257605 d'' m n d''')). Qed.
Lemma lem1257614 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term27 m d' d'' n d''') = (term30 d' d'' m n d''').
Proof. exact (TRANS (@lem1257563 d' m d'' n d''') (@lem1257607 d' d'' m n d''')). Qed.
Lemma lem1257615 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257616 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term26 m d' d'' n d''') = (term31 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1257615 d') (@lem1257614 d' d'' m n d''')). Qed.
Lemma lem1257623 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term25 m d' d'' n d''') = (term31 d' d'' m n d''').
Proof. exact (TRANS (@lem1257554 m d' d'' n d''') (@lem1257616 d' d'' m n d''')). Qed.
Lemma lem1257624 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term34 m n d'' d' d''') = (term31 d' d'' m n d''').
Proof. exact (TRANS (@lem1257551 m d' d'' n d''') (@lem1257623 d' d'' m n d''')). Qed.
Lemma lem1257625 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term34 n m d'' d' d''') = (term31 d' d'' m n d''').
Proof. exact (TRANS (@lem1257409 m n d'' d' d''') (@lem1257624 d' d'' m n d''')). Qed.
Lemma lem1257626 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : ((term3 m d''' n d'' d') = (term34 n m d'' d' d''')) = ((term31 d' d'' m n d''') = (term31 d' d'' m n d''')).
Proof. exact (MK_COMB (@lem1257406 d' d'' m n d''') (@lem1257625 d' d'' m n d''')). Qed.
Lemma lem1257628 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1257629 (x : nat) : (x = x) = True.
Proof. exact (@lem1257628 nat x). Qed.
Lemma lem1257630 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : ((term31 d' d'' m n d''') = (term31 d' d'' m n d''')) = True.
Proof. exact (@lem1257629 (term31 d' d'' m n d''')). Qed.
Lemma lem1257631 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term3 m d''' n d'' d') = (term34 n m d'' d' d''')) = True.
Proof. exact (TRANS (@lem1257626 d' d'' m n d''') (@lem1257630 d' d'' m n d''')). Qed.
Lemma lem1257632 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term3 m d''' n d'' d') = (term34 n m d'' d' d''')).
Proof. exact (SYM (@lem1257631 n m d'' d' d''')). Qed.
Lemma lem1257633 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term3 m d''' n d'' d') = (term34 n m d'' d' d''').
Proof. exact (EQ_MP (@lem1257632 n m d'' d' d''') (@lem0)). Qed.
Lemma lem1257634 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1257635 (n : nat) (m : nat) : (term0 m n) = (term0 n m).
Proof. exact (MK_COMB (@lem1257634) (@lem1257172 n m)). Qed.
Lemma lem1257636 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add m n) = (term3 m d''' n d'' d')) = ((Nat.add n m) = (term34 n m d'' d' d''')).
Proof. exact (MK_COMB (@lem1257635 n m) (@lem1257633 n m d'' d' d''')). Qed.
Lemma lem1257637 (m : nat) : term44 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1257638 (m : nat) : (term44 m) = (term45 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem1257639 (m : nat) : term45 m.
Proof. exact (EQ_MP (@lem1257638 m) (@lem1257637 m)). Qed.
Lemma lem1257640 (m : nat) (n : nat) : term46 m n.
Proof. exact (@lem1257639 m n). Qed.
Lemma lem1257641 (m : nat) (n : nat) : (term46 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem1257649 (m : nat) : term47 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1257650 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem1257651 (m : nat) : term48 m.
Proof. exact (EQ_MP (@lem1257650 m) (@lem1257649 m)). Qed.
Lemma lem1257652 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem1257651 m n). Qed.
Lemma lem1257653 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem1257654 (m : nat) (n : nat) : term50 m n.
Proof. exact (EQ_MP (@lem1257653 m n) (@lem1257652 m n)). Qed.
Lemma lem1257655 (m : nat) (n : nat) (p : nat) : term51 m n p.
Proof. exact (@lem1257654 m n p). Qed.
Lemma lem1257656 (m : nat) (n : nat) (p : nat) : (term51 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term51 m n p)). Qed.
Lemma lem1257659 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1257656 m n p) (@lem1257655 m n p)). Qed.
Lemma lem1257660 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add n m) = (term34 n m d'' d' d''')) = (m = (term36 m d'' d' d''')).
Proof. exact (@lem1257659 n m (term36 m d'' d' d''')). Qed.
Lemma lem1257662 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1257641 m n) (@lem1257640 m n)). Qed.
Lemma lem1257667 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : (m = (term36 m d'' d' d''')) = ((term35 d'' d' d''') = (NUMERAL 0)).
Proof. exact (@lem1257662 m (term35 d'' d' d''')). Qed.
Lemma lem1257668 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add n m) = (term34 n m d'' d' d''')) = ((term35 d'' d' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1257660 n m d'' d' d''') (@lem1257667 m d'' d' d''')). Qed.
Lemma lem1257669 (m : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : (term52 m d''' n d'' d') = (term52 m d''' n d'' d').
Proof. exact (eq_refl (term52 m d''' n d'' d')). Qed.
Lemma lem1257670 (m : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (((Nat.add m n) = (term3 m d''' n d'' d')) = ((Nat.add n m) = (term34 n m d'' d' d'''))) = (((Nat.add m n) = (term3 m d''' n d'' d')) = ((term35 d'' d' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1257669 m d''' n d'' d') (@lem1257668 n m d'' d' d''')). Qed.
Lemma lem1257671 (m : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add m n) = (term3 m d''' n d'' d')) = ((term35 d'' d' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1257670 m n d'' d' d''') (@lem1257636 n m d'' d' d''')). Qed.
Lemma lem1257672 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1257673 (m : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term53 m d''' n d'' d') = (term54 d'' d' d''').
Proof. exact (MK_COMB (@lem1257672) (@lem1257671 m n d'' d' d''')). Qed.
Lemma lem1257674 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1257675 (m : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term55 m d''' n d'' d') = (term56 d'' d' d''').
Proof. exact (MK_COMB (@lem1257673 m n d'' d' d''') (@lem1257674)). Qed.
Lemma lem1257676 (m : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : (term56 d'' d' d''') = (term55 m d''' n d'' d').
Proof. exact (SYM (@lem1257675 m n d'' d' d''')). Qed.
