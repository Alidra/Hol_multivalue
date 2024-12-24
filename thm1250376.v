Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1250376_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_LCANCEL_0_spec.
Require Import thm0_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1250097 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1250098 (p : nat) (d'' : nat) (d''' : nat) (d' : nat) : (term2 p d'' d''' d') = (term3 p d'' d''' d').
Proof. exact (@lem1250097 p (term4 d' d'' d''') d'). Qed.
Lemma lem1250106 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1250107 (d'' : nat) (d''' : nat) (d' : nat) : (term5 d'' d''' d') = (term6 d'' d''' d').
Proof. exact (@lem1250106 (Nat.add d' d'') (S d''') d'). Qed.
Lemma lem1250109 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1250110 (d'' : nat) (d''' : nat) (d' : nat) : (term6 d'' d''' d') = (term7 d'' d''' d').
Proof. exact (@lem1250109 d' d'' (term8 d''' d')). Qed.
Lemma lem1250117 (d'' : nat) (d''' : nat) (d' : nat) : (term5 d'' d''' d') = (term7 d'' d''' d').
Proof. exact (TRANS (@lem1250107 d'' d''' d') (@lem1250110 d'' d''' d')). Qed.
Lemma lem1250125 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1250126 (d' : nat) (d''' : nat) : (term8 d''' d') = (term9 d' d''').
Proof. exact (@lem1250125 d' (S d''')). Qed.
Lemma lem1250130 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1250131 (d'' : nat) (d' : nat) (d''' : nat) : (term10 d'' d''' d') = (term11 d'' d' d''').
Proof. exact (MK_COMB (@lem1250130 d'') (@lem1250126 d' d''')). Qed.
Lemma lem1250133 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250134 (d' : nat) (d'' : nat) (d''' : nat) : (term11 d'' d' d''') = (term11 d' d'' d''').
Proof. exact (@lem1250133 d' d'' (S d''')). Qed.
Lemma lem1250144 (d' : nat) (d'' : nat) (d''' : nat) : (term10 d'' d''' d') = (term11 d' d'' d''').
Proof. exact (TRANS (@lem1250131 d'' d' d''') (@lem1250134 d' d'' d''')). Qed.
Lemma lem1250145 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250146 (d' : nat) (d'' : nat) (d''' : nat) : (term7 d'' d''' d') = (term12 d' d'' d''').
Proof. exact (MK_COMB (@lem1250145 d') (@lem1250144 d' d'' d''')). Qed.
Lemma lem1250153 (d' : nat) (d'' : nat) (d''' : nat) : (term5 d'' d''' d') = (term12 d' d'' d''').
Proof. exact (TRANS (@lem1250117 d'' d''' d') (@lem1250146 d' d'' d''')). Qed.
Lemma lem1250154 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1250155 (p : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 p d'' d''' d') = (term13 p d' d'' d''').
Proof. exact (MK_COMB (@lem1250154 p) (@lem1250153 d' d'' d''')). Qed.
Lemma lem1250157 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250158 (p : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term13 p d' d'' d''') = (term14 p d' d'' d''').
Proof. exact (@lem1250157 d' p (term11 d' d'' d''')). Qed.
Lemma lem1250166 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250167 (d' : nat) (p : nat) (d'' : nat) (d''' : nat) : (term15 p d' d'' d''') = (term15 d' p d'' d''').
Proof. exact (@lem1250166 d' p (term9 d'' d''')). Qed.
Lemma lem1250175 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250176 (d'' : nat) (p : nat) (d''' : nat) : (term11 p d'' d''') = (term11 d'' p d''').
Proof. exact (@lem1250175 d'' p (S d''')). Qed.
Lemma lem1250186 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250187 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term15 d' p d'' d''') = (term15 d' d'' p d''').
Proof. exact (MK_COMB (@lem1250186 d') (@lem1250176 d'' p d''')). Qed.
Lemma lem1250194 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term15 p d' d'' d''') = (term15 d' d'' p d''').
Proof. exact (TRANS (@lem1250167 d' p d'' d''') (@lem1250187 d' d'' p d''')). Qed.
Lemma lem1250195 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250196 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term14 p d' d'' d''') = (term16 d' d'' p d''').
Proof. exact (MK_COMB (@lem1250195 d') (@lem1250194 d' d'' p d''')). Qed.
Lemma lem1250203 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term13 p d' d'' d''') = (term16 d' d'' p d''').
Proof. exact (TRANS (@lem1250158 p d' d'' d''') (@lem1250196 d' d'' p d''')). Qed.
Lemma lem1250204 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term3 p d'' d''' d') = (term16 d' d'' p d''').
Proof. exact (TRANS (@lem1250155 p d' d'' d''') (@lem1250203 d' d'' p d''')). Qed.
Lemma lem1250205 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term2 p d'' d''' d') = (term16 d' d'' p d''').
Proof. exact (TRANS (@lem1250098 p d'' d''' d') (@lem1250204 d' d'' p d''')). Qed.
Lemma lem1250206 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1250207 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term17 p d'' d''' d') = (term18 d' d'' p d''').
Proof. exact (MK_COMB (@lem1250206) (@lem1250205 d' d'' p d''')). Qed.
Lemma lem1250209 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250210 (d'' : nat) (p : nat) (d''' : nat) (d' : nat) : (term19 p d'' d''' d') = (term19 d'' p d''' d').
Proof. exact (@lem1250209 d'' p (term20 d''' d')). Qed.
Lemma lem1250224 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250225 (d''' : nat) (d' : nat) : (term20 d''' d') = (term21 d''' d').
Proof. exact (@lem1250224 d' (S d''') d'). Qed.
Lemma lem1250233 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1250234 (d' : nat) (d''' : nat) : (term8 d''' d') = (term9 d' d''').
Proof. exact (@lem1250233 d' (S d''')). Qed.
Lemma lem1250238 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250239 (d' : nat) (d''' : nat) : (term21 d''' d') = (term22 d' d''').
Proof. exact (MK_COMB (@lem1250238 d') (@lem1250234 d' d''')). Qed.
Lemma lem1250246 (d' : nat) (d''' : nat) : (term20 d''' d') = (term22 d' d''').
Proof. exact (TRANS (@lem1250225 d''' d') (@lem1250239 d' d''')). Qed.
Lemma lem1250247 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1250248 (p : nat) (d' : nat) (d''' : nat) : (term23 p d''' d') = (term24 p d' d''').
Proof. exact (MK_COMB (@lem1250247 p) (@lem1250246 d' d''')). Qed.
Lemma lem1250250 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250251 (p : nat) (d' : nat) (d''' : nat) : (term24 p d' d''') = (term25 p d' d''').
Proof. exact (@lem1250250 d' p (term9 d' d''')). Qed.
Lemma lem1250259 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250260 (d' : nat) (p : nat) (d''' : nat) : (term11 p d' d''') = (term11 d' p d''').
Proof. exact (@lem1250259 d' p (S d''')). Qed.
Lemma lem1250270 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250271 (d' : nat) (p : nat) (d''' : nat) : (term25 p d' d''') = (term12 d' p d''').
Proof. exact (MK_COMB (@lem1250270 d') (@lem1250260 d' p d''')). Qed.
Lemma lem1250278 (d' : nat) (p : nat) (d''' : nat) : (term24 p d' d''') = (term12 d' p d''').
Proof. exact (TRANS (@lem1250251 p d' d''') (@lem1250271 d' p d''')). Qed.
Lemma lem1250279 (d' : nat) (p : nat) (d''' : nat) : (term23 p d''' d') = (term12 d' p d''').
Proof. exact (TRANS (@lem1250248 p d' d''') (@lem1250278 d' p d''')). Qed.
Lemma lem1250280 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1250281 (d'' : nat) (d' : nat) (p : nat) (d''' : nat) : (term19 d'' p d''' d') = (term13 d'' d' p d''').
Proof. exact (MK_COMB (@lem1250280 d'') (@lem1250279 d' p d''')). Qed.
Lemma lem1250283 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250284 (d'' : nat) (d' : nat) (p : nat) (d''' : nat) : (term13 d'' d' p d''') = (term14 d'' d' p d''').
Proof. exact (@lem1250283 d' d'' (term11 d' p d''')). Qed.
Lemma lem1250292 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250293 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term15 d'' d' p d''') = (term15 d' d'' p d''').
Proof. exact (@lem1250292 d' d'' (term9 p d''')). Qed.
Lemma lem1250309 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250310 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term14 d'' d' p d''') = (term16 d' d'' p d''').
Proof. exact (MK_COMB (@lem1250309 d') (@lem1250293 d' d'' p d''')). Qed.
Lemma lem1250317 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term13 d'' d' p d''') = (term16 d' d'' p d''').
Proof. exact (TRANS (@lem1250284 d'' d' p d''') (@lem1250310 d' d'' p d''')). Qed.
Lemma lem1250318 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term19 d'' p d''' d') = (term16 d' d'' p d''').
Proof. exact (TRANS (@lem1250281 d'' d' p d''') (@lem1250317 d' d'' p d''')). Qed.
Lemma lem1250319 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term19 p d'' d''' d') = (term16 d' d'' p d''').
Proof. exact (TRANS (@lem1250210 d'' p d''' d') (@lem1250318 d' d'' p d''')). Qed.
Lemma lem1250320 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : ((term2 p d'' d''' d') = (term19 p d'' d''' d')) = ((term16 d' d'' p d''') = (term16 d' d'' p d''')).
Proof. exact (MK_COMB (@lem1250207 d' d'' p d''') (@lem1250319 d' d'' p d''')). Qed.
Lemma lem1250322 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1250323 (x : nat) : (x = x) = True.
Proof. exact (@lem1250322 nat x). Qed.
Lemma lem1250324 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : ((term16 d' d'' p d''') = (term16 d' d'' p d''')) = True.
Proof. exact (@lem1250323 (term16 d' d'' p d''')). Qed.
Lemma lem1250325 (p : nat) (d'' : nat) (d''' : nat) (d' : nat) : ((term2 p d'' d''' d') = (term19 p d'' d''' d')) = True.
Proof. exact (TRANS (@lem1250320 d' d'' p d''') (@lem1250324 d' d'' p d''')). Qed.
Lemma lem1250326 (p : nat) (d'' : nat) (d''' : nat) (d' : nat) : True = ((term2 p d'' d''' d') = (term19 p d'' d''' d')).
Proof. exact (SYM (@lem1250325 p d'' d''' d')). Qed.
Lemma lem1250327 (p : nat) (d'' : nat) (d''' : nat) (d' : nat) : (term2 p d'' d''' d') = (term19 p d'' d''' d').
Proof. exact (EQ_MP (@lem1250326 p d'' d''' d') (@lem0)). Qed.
Lemma lem1250329 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1250330 (x : nat) : (x = x) = True.
Proof. exact (@lem1250329 nat x). Qed.
Lemma lem1250331 (p : nat) (d'' : nat) : ((Nat.add p d'') = (Nat.add p d'')) = True.
Proof. exact (@lem1250330 (Nat.add p d'')). Qed.
Lemma lem1250332 (p : nat) (d'' : nat) : True = ((Nat.add p d'') = (Nat.add p d'')).
Proof. exact (SYM (@lem1250331 p d'')). Qed.
Lemma lem1250333 (p : nat) (d'' : nat) : (Nat.add p d'') = (Nat.add p d'').
Proof. exact (EQ_MP (@lem1250332 p d'') (@lem0)). Qed.
Lemma lem1250334 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1250335 (p : nat) (d'' : nat) (d''' : nat) (d' : nat) : (term17 p d'' d''' d') = (term26 p d'' d''' d').
Proof. exact (MK_COMB (@lem1250334) (@lem1250327 p d'' d''' d')). Qed.
Lemma lem1250336 (d''' : nat) (d' : nat) (p : nat) (d'' : nat) : ((term2 p d'' d''' d') = (Nat.add p d'')) = ((term19 p d'' d''' d') = (Nat.add p d'')).
Proof. exact (MK_COMB (@lem1250335 p d'' d''' d') (@lem1250333 p d'')). Qed.
Lemma lem1250343 (m : nat) : term27 m.
Proof. exact (@lem79890 m). Qed.
Lemma lem1250344 (m : nat) : (term27 m) = (term28 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem1250345 (m : nat) : term28 m.
Proof. exact (EQ_MP (@lem1250344 m) (@lem1250343 m)). Qed.
Lemma lem1250346 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem1250345 m n). Qed.
Lemma lem1250347 (m : nat) (n : nat) : (term29 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem1250349 (m : nat) : term30 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1250350 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem1250351 (m : nat) : term31 m.
Proof. exact (EQ_MP (@lem1250350 m) (@lem1250349 m)). Qed.
Lemma lem1250352 (m : nat) (n : nat) : term32 m n.
Proof. exact (@lem1250351 m n). Qed.
Lemma lem1250353 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1250354 (m : nat) (n : nat) : term33 m n.
Proof. exact (EQ_MP (@lem1250353 m n) (@lem1250352 m n)). Qed.
Lemma lem1250355 (m : nat) (n : nat) (p : nat) : term34 m n p.
Proof. exact (@lem1250354 m n p). Qed.
Lemma lem1250356 (m : nat) (n : nat) (p : nat) : (term34 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term34 m n p)). Qed.
Lemma lem1250359 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1250356 m n p) (@lem1250355 m n p)). Qed.
Lemma lem1250360 (p : nat) (d''' : nat) (d' : nat) (d'' : nat) : ((term19 p d'' d''' d') = (Nat.add p d'')) = ((term23 d'' d''' d') = d'').
Proof. exact (@lem1250359 p (term23 d'' d''' d') d''). Qed.
Lemma lem1250362 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1250347 m n) (@lem1250346 m n)). Qed.
Lemma lem1250367 (d'' : nat) (d''' : nat) (d' : nat) : ((term23 d'' d''' d') = d'') = ((term20 d''' d') = (NUMERAL 0)).
Proof. exact (@lem1250362 d'' (term20 d''' d')). Qed.
Lemma lem1250368 (p : nat) (d'' : nat) (d''' : nat) (d' : nat) : ((term19 p d'' d''' d') = (Nat.add p d'')) = ((term20 d''' d') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1250360 p d''' d' d'') (@lem1250367 d'' d''' d')). Qed.
Lemma lem1250369 (d''' : nat) (d' : nat) (p : nat) (d'' : nat) : (term35 d''' d' p d'') = (term35 d''' d' p d'').
Proof. exact (eq_refl (term35 d''' d' p d'')). Qed.
Lemma lem1250370 (p : nat) (d'' : nat) (d''' : nat) (d' : nat) : (((term2 p d'' d''' d') = (Nat.add p d'')) = ((term19 p d'' d''' d') = (Nat.add p d''))) = (((term2 p d'' d''' d') = (Nat.add p d'')) = ((term20 d''' d') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1250369 d''' d' p d'') (@lem1250368 p d'' d''' d')). Qed.
Lemma lem1250371 (p : nat) (d'' : nat) (d''' : nat) (d' : nat) : ((term2 p d'' d''' d') = (Nat.add p d'')) = ((term20 d''' d') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1250370 p d'' d''' d') (@lem1250336 d''' d' p d'')). Qed.
Lemma lem1250372 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1250373 (p : nat) (d'' : nat) (d''' : nat) (d' : nat) : (term36 d''' d' p d'') = (term37 d''' d').
Proof. exact (MK_COMB (@lem1250372) (@lem1250371 p d'' d''' d')). Qed.
Lemma lem1250374 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1250375 (p : nat) (d'' : nat) (d''' : nat) (d' : nat) : (term38 d''' d' p d'') = (term39 d''' d').
Proof. exact (MK_COMB (@lem1250373 p d'' d''' d') (@lem1250374)). Qed.
Lemma lem1250376 (d''' : nat) (d' : nat) (p : nat) (d'' : nat) : (term39 d''' d') = (term38 d''' d' p d'').
Proof. exact (SYM (@lem1250375 p d'' d''' d')). Qed.
