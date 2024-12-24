Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258497_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_LCANCEL_0_spec.
Require Import thm0_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1258088 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1258089 (m : nat) (d' : nat) (d''' : nat) (n : nat) (d'' : nat) : (term2 m d' d''' n d'') = (term3 m d' d''' n d'').
Proof. exact (@lem1258088 m (term4 d' d'' d''') (Nat.add n d'')). Qed.
Lemma lem1258097 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1258098 (d' : nat) (d''' : nat) (n : nat) (d'' : nat) : (term5 d' d''' n d'') = (term6 d' d''' n d'').
Proof. exact (@lem1258097 (Nat.add d' d'') (S d''') (Nat.add n d'')). Qed.
Lemma lem1258100 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1258101 (d' : nat) (d''' : nat) (n : nat) (d'' : nat) : (term6 d' d''' n d'') = (term7 d' d''' n d'').
Proof. exact (@lem1258100 d' d'' (term8 d''' n d'')). Qed.
Lemma lem1258108 (d' : nat) (d''' : nat) (n : nat) (d'' : nat) : (term5 d' d''' n d'') = (term7 d' d''' n d'').
Proof. exact (TRANS (@lem1258098 d' d''' n d'') (@lem1258101 d' d''' n d'')). Qed.
Lemma lem1258116 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258117 (n : nat) (d''' : nat) (d'' : nat) : (term8 d''' n d'') = (term9 n d''' d'').
Proof. exact (@lem1258116 n (S d''') d''). Qed.
Lemma lem1258125 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1258126 (d'' : nat) (d''' : nat) : (term10 d''' d'') = (term11 d'' d''').
Proof. exact (@lem1258125 d'' (S d''')). Qed.
Lemma lem1258130 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1258131 (n : nat) (d'' : nat) (d''' : nat) : (term9 n d''' d'') = (term12 n d'' d''').
Proof. exact (MK_COMB (@lem1258130 n) (@lem1258126 d'' d''')). Qed.
Lemma lem1258133 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258134 (d'' : nat) (n : nat) (d''' : nat) : (term12 n d'' d''') = (term12 d'' n d''').
Proof. exact (@lem1258133 d'' n (S d''')). Qed.
Lemma lem1258144 (d'' : nat) (n : nat) (d''' : nat) : (term9 n d''' d'') = (term12 d'' n d''').
Proof. exact (TRANS (@lem1258131 n d'' d''') (@lem1258134 d'' n d''')). Qed.
Lemma lem1258145 (d'' : nat) (n : nat) (d''' : nat) : (term8 d''' n d'') = (term12 d'' n d''').
Proof. exact (TRANS (@lem1258117 n d''' d'') (@lem1258144 d'' n d''')). Qed.
Lemma lem1258146 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258147 (d'' : nat) (n : nat) (d''' : nat) : (term13 d''' n d'') = (term14 d'' n d''').
Proof. exact (MK_COMB (@lem1258146 d'') (@lem1258145 d'' n d''')). Qed.
Lemma lem1258154 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1258155 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term7 d' d''' n d'') = (term15 d' d'' n d''').
Proof. exact (MK_COMB (@lem1258154 d') (@lem1258147 d'' n d''')). Qed.
Lemma lem1258162 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term5 d' d''' n d'') = (term15 d' d'' n d''').
Proof. exact (TRANS (@lem1258108 d' d''' n d'') (@lem1258155 d' d'' n d''')). Qed.
Lemma lem1258163 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1258164 (m : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term3 m d' d''' n d'') = (term16 m d' d'' n d''').
Proof. exact (MK_COMB (@lem1258163 m) (@lem1258162 d' d'' n d''')). Qed.
Lemma lem1258166 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258167 (d' : nat) (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term16 m d' d'' n d''') = (term16 d' m d'' n d''').
Proof. exact (@lem1258166 d' m (term14 d'' n d''')). Qed.
Lemma lem1258175 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258176 (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term15 m d'' n d''') = (term17 m d'' n d''').
Proof. exact (@lem1258175 d'' m (term12 d'' n d''')). Qed.
Lemma lem1258184 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258185 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term18 m d'' n d''') = (term18 d'' m n d''').
Proof. exact (@lem1258184 d'' m (term11 n d''')). Qed.
Lemma lem1258201 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258202 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term17 m d'' n d''') = (term19 d'' m n d''').
Proof. exact (MK_COMB (@lem1258201 d'') (@lem1258185 d'' m n d''')). Qed.
Lemma lem1258209 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term15 m d'' n d''') = (term19 d'' m n d''').
Proof. exact (TRANS (@lem1258176 m d'' n d''') (@lem1258202 d'' m n d''')). Qed.
Lemma lem1258210 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1258211 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term16 d' m d'' n d''') = (term20 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1258210 d') (@lem1258209 d'' m n d''')). Qed.
Lemma lem1258218 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term16 m d' d'' n d''') = (term20 d' d'' m n d''').
Proof. exact (TRANS (@lem1258167 d' m d'' n d''') (@lem1258211 d' d'' m n d''')). Qed.
Lemma lem1258219 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term3 m d' d''' n d'') = (term20 d' d'' m n d''').
Proof. exact (TRANS (@lem1258164 m d' d'' n d''') (@lem1258218 d' d'' m n d''')). Qed.
Lemma lem1258220 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term2 m d' d''' n d'') = (term20 d' d'' m n d''').
Proof. exact (TRANS (@lem1258089 m d' d''' n d'') (@lem1258219 d' d'' m n d''')). Qed.
Lemma lem1258221 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258222 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term21 m d' d''' n d'') = (term22 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1258221) (@lem1258220 d' d'' m n d''')). Qed.
Lemma lem1258224 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258225 (m : nat) (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term23 n m d' d''' d'') = (term23 m n d' d''' d'').
Proof. exact (@lem1258224 m n (term24 d' d''' d'')). Qed.
Lemma lem1258233 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258234 (d' : nat) (n : nat) (d''' : nat) (d'' : nat) : (term25 n d' d''' d'') = (term25 d' n d''' d'').
Proof. exact (@lem1258233 d' n (term26 d''' d'')). Qed.
Lemma lem1258248 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258249 (d''' : nat) (d'' : nat) : (term26 d''' d'') = (term27 d''' d'').
Proof. exact (@lem1258248 d'' (S d''') d''). Qed.
Lemma lem1258257 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1258258 (d'' : nat) (d''' : nat) : (term10 d''' d'') = (term11 d'' d''').
Proof. exact (@lem1258257 d'' (S d''')). Qed.
Lemma lem1258262 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258263 (d'' : nat) (d''' : nat) : (term27 d''' d'') = (term28 d'' d''').
Proof. exact (MK_COMB (@lem1258262 d'') (@lem1258258 d'' d''')). Qed.
Lemma lem1258270 (d'' : nat) (d''' : nat) : (term26 d''' d'') = (term28 d'' d''').
Proof. exact (TRANS (@lem1258249 d''' d'') (@lem1258263 d'' d''')). Qed.
Lemma lem1258271 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1258272 (n : nat) (d'' : nat) (d''' : nat) : (term24 n d''' d'') = (term29 n d'' d''').
Proof. exact (MK_COMB (@lem1258271 n) (@lem1258270 d'' d''')). Qed.
Lemma lem1258274 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258275 (n : nat) (d'' : nat) (d''' : nat) : (term29 n d'' d''') = (term30 n d'' d''').
Proof. exact (@lem1258274 d'' n (term11 d'' d''')). Qed.
Lemma lem1258283 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258284 (d'' : nat) (n : nat) (d''' : nat) : (term12 n d'' d''') = (term12 d'' n d''').
Proof. exact (@lem1258283 d'' n (S d''')). Qed.
Lemma lem1258294 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258295 (d'' : nat) (n : nat) (d''' : nat) : (term30 n d'' d''') = (term14 d'' n d''').
Proof. exact (MK_COMB (@lem1258294 d'') (@lem1258284 d'' n d''')). Qed.
Lemma lem1258302 (d'' : nat) (n : nat) (d''' : nat) : (term29 n d'' d''') = (term14 d'' n d''').
Proof. exact (TRANS (@lem1258275 n d'' d''') (@lem1258295 d'' n d''')). Qed.
Lemma lem1258303 (d'' : nat) (n : nat) (d''' : nat) : (term24 n d''' d'') = (term14 d'' n d''').
Proof. exact (TRANS (@lem1258272 n d'' d''') (@lem1258302 d'' n d''')). Qed.
Lemma lem1258304 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1258305 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term25 d' n d''' d'') = (term15 d' d'' n d''').
Proof. exact (MK_COMB (@lem1258304 d') (@lem1258303 d'' n d''')). Qed.
Lemma lem1258312 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term25 n d' d''' d'') = (term15 d' d'' n d''').
Proof. exact (TRANS (@lem1258234 d' n d''' d'') (@lem1258305 d' d'' n d''')). Qed.
Lemma lem1258313 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1258314 (m : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term23 m n d' d''' d'') = (term16 m d' d'' n d''').
Proof. exact (MK_COMB (@lem1258313 m) (@lem1258312 d' d'' n d''')). Qed.
Lemma lem1258316 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258317 (d' : nat) (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term16 m d' d'' n d''') = (term16 d' m d'' n d''').
Proof. exact (@lem1258316 d' m (term14 d'' n d''')). Qed.
Lemma lem1258325 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258326 (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term15 m d'' n d''') = (term17 m d'' n d''').
Proof. exact (@lem1258325 d'' m (term12 d'' n d''')). Qed.
Lemma lem1258334 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258335 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term18 m d'' n d''') = (term18 d'' m n d''').
Proof. exact (@lem1258334 d'' m (term11 n d''')). Qed.
Lemma lem1258351 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258352 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term17 m d'' n d''') = (term19 d'' m n d''').
Proof. exact (MK_COMB (@lem1258351 d'') (@lem1258335 d'' m n d''')). Qed.
Lemma lem1258359 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term15 m d'' n d''') = (term19 d'' m n d''').
Proof. exact (TRANS (@lem1258326 m d'' n d''') (@lem1258352 d'' m n d''')). Qed.
Lemma lem1258360 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1258361 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term16 d' m d'' n d''') = (term20 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1258360 d') (@lem1258359 d'' m n d''')). Qed.
Lemma lem1258368 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term16 m d' d'' n d''') = (term20 d' d'' m n d''').
Proof. exact (TRANS (@lem1258317 d' m d'' n d''') (@lem1258361 d' d'' m n d''')). Qed.
Lemma lem1258369 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term23 m n d' d''' d'') = (term20 d' d'' m n d''').
Proof. exact (TRANS (@lem1258314 m d' d'' n d''') (@lem1258368 d' d'' m n d''')). Qed.
Lemma lem1258370 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term23 n m d' d''' d'') = (term20 d' d'' m n d''').
Proof. exact (TRANS (@lem1258225 m n d' d''' d'') (@lem1258369 d' d'' m n d''')). Qed.
Lemma lem1258371 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : ((term2 m d' d''' n d'') = (term23 n m d' d''' d'')) = ((term20 d' d'' m n d''') = (term20 d' d'' m n d''')).
Proof. exact (MK_COMB (@lem1258222 d' d'' m n d''') (@lem1258370 d' d'' m n d''')). Qed.
Lemma lem1258373 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1258374 (x : nat) : (x = x) = True.
Proof. exact (@lem1258373 nat x). Qed.
Lemma lem1258375 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : ((term20 d' d'' m n d''') = (term20 d' d'' m n d''')) = True.
Proof. exact (@lem1258374 (term20 d' d'' m n d''')). Qed.
Lemma lem1258376 (n : nat) (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term2 m d' d''' n d'') = (term23 n m d' d''' d'')) = True.
Proof. exact (TRANS (@lem1258371 d' d'' m n d''') (@lem1258375 d' d'' m n d''')). Qed.
Lemma lem1258377 (n : nat) (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : True = ((term2 m d' d''' n d'') = (term23 n m d' d''' d'')).
Proof. exact (SYM (@lem1258376 n m d' d''' d'')). Qed.
Lemma lem1258378 (n : nat) (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term2 m d' d''' n d'') = (term23 n m d' d''' d'').
Proof. exact (EQ_MP (@lem1258377 n m d' d''' d'') (@lem0)). Qed.
Lemma lem1258382 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1258383 (m : nat) (n : nat) (d' : nat) : (term0 m n d') = (term1 m n d').
Proof. exact (@lem1258382 m n d'). Qed.
Lemma lem1258391 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1258392 (d' : nat) (n : nat) : (Nat.add n d') = (Nat.add d' n).
Proof. exact (@lem1258391 d' n). Qed.
Lemma lem1258396 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1258397 (m : nat) (d' : nat) (n : nat) : (term1 m n d') = (term1 m d' n).
Proof. exact (MK_COMB (@lem1258396 m) (@lem1258392 d' n)). Qed.
Lemma lem1258399 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258400 (d' : nat) (m : nat) (n : nat) : (term1 m d' n) = (term1 d' m n).
Proof. exact (@lem1258399 d' m n). Qed.
Lemma lem1258409 (d' : nat) (m : nat) (n : nat) : (term1 m n d') = (term1 d' m n).
Proof. exact (TRANS (@lem1258397 m d' n) (@lem1258400 d' m n)). Qed.
Lemma lem1258410 (d' : nat) (m : nat) (n : nat) : (term0 m n d') = (term1 d' m n).
Proof. exact (TRANS (@lem1258383 m n d') (@lem1258409 d' m n)). Qed.
Lemma lem1258411 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258412 (d' : nat) (m : nat) (n : nat) : (term31 m n d') = (term32 d' m n).
Proof. exact (MK_COMB (@lem1258411) (@lem1258410 d' m n)). Qed.
Lemma lem1258414 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258415 (m : nat) (n : nat) (d' : nat) : (term1 n m d') = (term1 m n d').
Proof. exact (@lem1258414 m n d'). Qed.
Lemma lem1258423 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1258424 (d' : nat) (n : nat) : (Nat.add n d') = (Nat.add d' n).
Proof. exact (@lem1258423 d' n). Qed.
Lemma lem1258428 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1258429 (m : nat) (d' : nat) (n : nat) : (term1 m n d') = (term1 m d' n).
Proof. exact (MK_COMB (@lem1258428 m) (@lem1258424 d' n)). Qed.
Lemma lem1258431 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258432 (d' : nat) (m : nat) (n : nat) : (term1 m d' n) = (term1 d' m n).
Proof. exact (@lem1258431 d' m n). Qed.
Lemma lem1258441 (d' : nat) (m : nat) (n : nat) : (term1 m n d') = (term1 d' m n).
Proof. exact (TRANS (@lem1258429 m d' n) (@lem1258432 d' m n)). Qed.
Lemma lem1258442 (d' : nat) (m : nat) (n : nat) : (term1 n m d') = (term1 d' m n).
Proof. exact (TRANS (@lem1258415 m n d') (@lem1258441 d' m n)). Qed.
Lemma lem1258443 (d' : nat) (m : nat) (n : nat) : ((term0 m n d') = (term1 n m d')) = ((term1 d' m n) = (term1 d' m n)).
Proof. exact (MK_COMB (@lem1258412 d' m n) (@lem1258442 d' m n)). Qed.
Lemma lem1258445 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1258446 (x : nat) : (x = x) = True.
Proof. exact (@lem1258445 nat x). Qed.
Lemma lem1258447 (d' : nat) (m : nat) (n : nat) : ((term1 d' m n) = (term1 d' m n)) = True.
Proof. exact (@lem1258446 (term1 d' m n)). Qed.
Lemma lem1258448 (n : nat) (m : nat) (d' : nat) : ((term0 m n d') = (term1 n m d')) = True.
Proof. exact (TRANS (@lem1258443 d' m n) (@lem1258447 d' m n)). Qed.
Lemma lem1258449 (n : nat) (m : nat) (d' : nat) : True = ((term0 m n d') = (term1 n m d')).
Proof. exact (SYM (@lem1258448 n m d')). Qed.
Lemma lem1258450 (n : nat) (m : nat) (d' : nat) : (term0 m n d') = (term1 n m d').
Proof. exact (EQ_MP (@lem1258449 n m d') (@lem0)). Qed.
Lemma lem1258451 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258452 (n : nat) (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term21 m d' d''' n d'') = (term33 n m d' d''' d'').
Proof. exact (MK_COMB (@lem1258451) (@lem1258378 n m d' d''' d'')). Qed.
Lemma lem1258453 (d''' : nat) (d'' : nat) (n : nat) (m : nat) (d' : nat) : ((term2 m d' d''' n d'') = (term0 m n d')) = ((term23 n m d' d''' d'') = (term1 n m d')).
Proof. exact (MK_COMB (@lem1258452 n m d' d''' d'') (@lem1258450 n m d')). Qed.
Lemma lem1258460 (m : nat) : term34 m.
Proof. exact (@lem79890 m). Qed.
Lemma lem1258461 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1258462 (m : nat) : term35 m.
Proof. exact (EQ_MP (@lem1258461 m) (@lem1258460 m)). Qed.
Lemma lem1258463 (m : nat) (n : nat) : term36 m n.
Proof. exact (@lem1258462 m n). Qed.
Lemma lem1258464 (m : nat) (n : nat) : (term36 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem1258466 (m : nat) : term37 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1258467 (m : nat) : (term37 m) = (term38 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem1258468 (m : nat) : term38 m.
Proof. exact (EQ_MP (@lem1258467 m) (@lem1258466 m)). Qed.
Lemma lem1258469 (m : nat) (n : nat) : term39 m n.
Proof. exact (@lem1258468 m n). Qed.
Lemma lem1258470 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem1258471 (m : nat) (n : nat) : term40 m n.
Proof. exact (EQ_MP (@lem1258470 m n) (@lem1258469 m n)). Qed.
Lemma lem1258472 (m : nat) (n : nat) (p : nat) : term41 m n p.
Proof. exact (@lem1258471 m n p). Qed.
Lemma lem1258473 (m : nat) (n : nat) (p : nat) : (term41 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term41 m n p)). Qed.
Lemma lem1258476 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1258473 m n p) (@lem1258472 m n p)). Qed.
Lemma lem1258477 (n : nat) (d''' : nat) (d'' : nat) (m : nat) (d' : nat) : ((term23 n m d' d''' d'') = (term1 n m d')) = ((term25 m d' d''' d'') = (Nat.add m d')).
Proof. exact (@lem1258476 n (term25 m d' d''' d'') (Nat.add m d')). Qed.
Lemma lem1258479 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1258473 m n p) (@lem1258472 m n p)). Qed.
Lemma lem1258480 (m : nat) (d''' : nat) (d'' : nat) (d' : nat) : ((term25 m d' d''' d'') = (Nat.add m d')) = ((term24 d' d''' d'') = d').
Proof. exact (@lem1258479 m (term24 d' d''' d'') d'). Qed.
Lemma lem1258482 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1258464 m n) (@lem1258463 m n)). Qed.
Lemma lem1258487 (d' : nat) (d''' : nat) (d'' : nat) : ((term24 d' d''' d'') = d') = ((term26 d''' d'') = (NUMERAL 0)).
Proof. exact (@lem1258482 d' (term26 d''' d'')). Qed.
Lemma lem1258488 (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term25 m d' d''' d'') = (Nat.add m d')) = ((term26 d''' d'') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1258480 m d''' d'' d') (@lem1258487 d' d''' d'')). Qed.
Lemma lem1258489 (n : nat) (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term23 n m d' d''' d'') = (term1 n m d')) = ((term26 d''' d'') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1258477 n d''' d'' m d') (@lem1258488 m d' d''' d'')). Qed.
Lemma lem1258490 (d''' : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : (term42 d''' d'' m n d') = (term42 d''' d'' m n d').
Proof. exact (eq_refl (term42 d''' d'' m n d')). Qed.
Lemma lem1258491 (m : nat) (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (((term2 m d' d''' n d'') = (term0 m n d')) = ((term23 n m d' d''' d'') = (term1 n m d'))) = (((term2 m d' d''' n d'') = (term0 m n d')) = ((term26 d''' d'') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1258490 d''' d'' m n d') (@lem1258489 n m d' d''' d'')). Qed.
Lemma lem1258492 (m : nat) (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term2 m d' d''' n d'') = (term0 m n d')) = ((term26 d''' d'') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1258491 m n d' d''' d'') (@lem1258453 d''' d'' n m d')). Qed.
Lemma lem1258493 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1258494 (m : nat) (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term43 d''' d'' m n d') = (term44 d''' d'').
Proof. exact (MK_COMB (@lem1258493) (@lem1258492 m n d' d''' d'')). Qed.
Lemma lem1258495 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1258496 (m : nat) (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term45 d''' d'' m n d') = (term46 d''' d'').
Proof. exact (MK_COMB (@lem1258494 m n d' d''' d'') (@lem1258495)). Qed.
Lemma lem1258497 (d''' : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : (term46 d''' d'') = (term45 d''' d'' m n d').
Proof. exact (SYM (@lem1258496 m n d' d''' d'')). Qed.
