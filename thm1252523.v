Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1252523_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1252111 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1252112 (p : nat) (d' : nat) (n : nat) : (term0 p d' n) = (term1 p d' n).
Proof. exact (@lem1252111 p d' n). Qed.
Lemma lem1252114 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252115 (d' : nat) (p : nat) (n : nat) : (term1 p d' n) = (term1 d' p n).
Proof. exact (@lem1252114 d' p n). Qed.
Lemma lem1252122 (d' : nat) (p : nat) (n : nat) : (term0 p d' n) = (term1 d' p n).
Proof. exact (TRANS (@lem1252112 p d' n) (@lem1252115 d' p n)). Qed.
Lemma lem1252124 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1252125 (n : nat) (p : nat) : (Nat.add p n) = (Nat.add n p).
Proof. exact (@lem1252124 n p). Qed.
Lemma lem1252129 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252130 (d' : nat) (n : nat) (p : nat) : (term1 d' p n) = (term1 d' n p).
Proof. exact (MK_COMB (@lem1252129 d') (@lem1252125 n p)). Qed.
Lemma lem1252137 (d' : nat) (n : nat) (p : nat) : (term0 p d' n) = (term1 d' n p).
Proof. exact (TRANS (@lem1252122 d' p n) (@lem1252130 d' n p)). Qed.
Lemma lem1252138 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1252139 (d' : nat) (n : nat) (p : nat) : (term2 p d' n) = (term3 d' n p).
Proof. exact (MK_COMB (@lem1252138) (@lem1252137 d' n p)). Qed.
Lemma lem1252141 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252142 (n : nat) (p : nat) (d' : nat) : (term1 p n d') = (term1 n p d').
Proof. exact (@lem1252141 n p d'). Qed.
Lemma lem1252150 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1252151 (d' : nat) (p : nat) : (Nat.add p d') = (Nat.add d' p).
Proof. exact (@lem1252150 d' p). Qed.
Lemma lem1252155 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1252156 (n : nat) (d' : nat) (p : nat) : (term1 n p d') = (term1 n d' p).
Proof. exact (MK_COMB (@lem1252155 n) (@lem1252151 d' p)). Qed.
Lemma lem1252158 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252159 (d' : nat) (n : nat) (p : nat) : (term1 n d' p) = (term1 d' n p).
Proof. exact (@lem1252158 d' n p). Qed.
Lemma lem1252169 (d' : nat) (n : nat) (p : nat) : (term1 n p d') = (term1 d' n p).
Proof. exact (TRANS (@lem1252156 n d' p) (@lem1252159 d' n p)). Qed.
Lemma lem1252170 (d' : nat) (n : nat) (p : nat) : (term1 p n d') = (term1 d' n p).
Proof. exact (TRANS (@lem1252142 n p d') (@lem1252169 d' n p)). Qed.
Lemma lem1252171 (d' : nat) (n : nat) (p : nat) : ((term0 p d' n) = (term1 p n d')) = ((term1 d' n p) = (term1 d' n p)).
Proof. exact (MK_COMB (@lem1252139 d' n p) (@lem1252170 d' n p)). Qed.
Lemma lem1252173 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1252174 (x : nat) : (x = x) = True.
Proof. exact (@lem1252173 nat x). Qed.
Lemma lem1252175 (d' : nat) (n : nat) (p : nat) : ((term1 d' n p) = (term1 d' n p)) = True.
Proof. exact (@lem1252174 (term1 d' n p)). Qed.
Lemma lem1252176 (p : nat) (n : nat) (d' : nat) : ((term0 p d' n) = (term1 p n d')) = True.
Proof. exact (TRANS (@lem1252171 d' n p) (@lem1252175 d' n p)). Qed.
Lemma lem1252177 (p : nat) (n : nat) (d' : nat) : True = ((term0 p d' n) = (term1 p n d')).
Proof. exact (SYM (@lem1252176 p n d')). Qed.
Lemma lem1252178 (p : nat) (n : nat) (d' : nat) : (term0 p d' n) = (term1 p n d').
Proof. exact (EQ_MP (@lem1252177 p n d') (@lem0)). Qed.
Lemma lem1252182 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1252183 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term4 p n d' d'' d''') = (term5 p n d' d'' d''').
Proof. exact (@lem1252182 p (Nat.add n d'') (term6 d' d'' d''')). Qed.
Lemma lem1252191 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1252192 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term7 n d' d'' d''') = (term8 n d' d'' d''').
Proof. exact (@lem1252191 n d'' (term6 d' d'' d''')). Qed.
Lemma lem1252194 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252195 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term8 n d' d'' d''') = (term9 n d' d'' d''').
Proof. exact (@lem1252194 d'' n (term6 d' d'' d''')). Qed.
Lemma lem1252202 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term7 n d' d'' d''') = (term9 n d' d'' d''').
Proof. exact (TRANS (@lem1252192 n d' d'' d''') (@lem1252195 n d' d'' d''')). Qed.
Lemma lem1252210 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1252211 (d' : nat) (d'' : nat) (d''' : nat) : (term6 d' d'' d''') = (term10 d' d'' d''').
Proof. exact (@lem1252210 d' d'' (S d''')). Qed.
Lemma lem1252221 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1252222 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term11 n d' d'' d''') = (term12 n d' d'' d''').
Proof. exact (MK_COMB (@lem1252221 n) (@lem1252211 d' d'' d''')). Qed.
Lemma lem1252224 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252225 (d' : nat) (n : nat) (d'' : nat) (d''' : nat) : (term12 n d' d'' d''') = (term12 d' n d'' d''').
Proof. exact (@lem1252224 d' n (term13 d'' d''')). Qed.
Lemma lem1252233 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252234 (d'' : nat) (n : nat) (d''' : nat) : (term10 n d'' d''') = (term10 d'' n d''').
Proof. exact (@lem1252233 d'' n (S d''')). Qed.
Lemma lem1252244 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252245 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term12 d' n d'' d''') = (term12 d' d'' n d''').
Proof. exact (MK_COMB (@lem1252244 d') (@lem1252234 d'' n d''')). Qed.
Lemma lem1252252 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term12 n d' d'' d''') = (term12 d' d'' n d''').
Proof. exact (TRANS (@lem1252225 d' n d'' d''') (@lem1252245 d' d'' n d''')). Qed.
Lemma lem1252253 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term11 n d' d'' d''') = (term12 d' d'' n d''').
Proof. exact (TRANS (@lem1252222 n d' d'' d''') (@lem1252252 d' d'' n d''')). Qed.
Lemma lem1252254 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1252255 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term9 n d' d'' d''') = (term14 d' d'' n d''').
Proof. exact (MK_COMB (@lem1252254 d'') (@lem1252253 d' d'' n d''')). Qed.
Lemma lem1252257 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252258 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term14 d' d'' n d''') = (term15 d' d'' n d''').
Proof. exact (@lem1252257 d' d'' (term10 d'' n d''')). Qed.
Lemma lem1252280 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term9 n d' d'' d''') = (term15 d' d'' n d''').
Proof. exact (TRANS (@lem1252255 d' d'' n d''') (@lem1252258 d' d'' n d''')). Qed.
Lemma lem1252281 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term7 n d' d'' d''') = (term15 d' d'' n d''').
Proof. exact (TRANS (@lem1252202 n d' d'' d''') (@lem1252280 d' d'' n d''')). Qed.
Lemma lem1252282 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1252283 (p : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term5 p n d' d'' d''') = (term16 p d' d'' n d''').
Proof. exact (MK_COMB (@lem1252282 p) (@lem1252281 d' d'' n d''')). Qed.
Lemma lem1252285 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252286 (d' : nat) (p : nat) (d'' : nat) (n : nat) (d''' : nat) : (term16 p d' d'' n d''') = (term16 d' p d'' n d''').
Proof. exact (@lem1252285 d' p (term17 d'' n d''')). Qed.
Lemma lem1252294 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252295 (p : nat) (d'' : nat) (n : nat) (d''' : nat) : (term15 p d'' n d''') = (term14 p d'' n d''').
Proof. exact (@lem1252294 d'' p (term10 d'' n d''')). Qed.
Lemma lem1252303 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252304 (d'' : nat) (p : nat) (n : nat) (d''' : nat) : (term12 p d'' n d''') = (term12 d'' p n d''').
Proof. exact (@lem1252303 d'' p (term13 n d''')). Qed.
Lemma lem1252312 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252313 (n : nat) (p : nat) (d''' : nat) : (term10 p n d''') = (term10 n p d''').
Proof. exact (@lem1252312 n p (S d''')). Qed.
Lemma lem1252323 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1252324 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term12 d'' p n d''') = (term12 d'' n p d''').
Proof. exact (MK_COMB (@lem1252323 d'') (@lem1252313 n p d''')). Qed.
Lemma lem1252331 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term12 p d'' n d''') = (term12 d'' n p d''').
Proof. exact (TRANS (@lem1252304 d'' p n d''') (@lem1252324 d'' n p d''')). Qed.
Lemma lem1252332 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1252333 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term14 p d'' n d''') = (term18 d'' n p d''').
Proof. exact (MK_COMB (@lem1252332 d'') (@lem1252331 d'' n p d''')). Qed.
Lemma lem1252340 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term15 p d'' n d''') = (term18 d'' n p d''').
Proof. exact (TRANS (@lem1252295 p d'' n d''') (@lem1252333 d'' n p d''')). Qed.
Lemma lem1252341 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252342 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term16 d' p d'' n d''') = (term19 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1252341 d') (@lem1252340 d'' n p d''')). Qed.
Lemma lem1252349 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term16 p d' d'' n d''') = (term19 d' d'' n p d''').
Proof. exact (TRANS (@lem1252286 d' p d'' n d''') (@lem1252342 d' d'' n p d''')). Qed.
Lemma lem1252350 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term5 p n d' d'' d''') = (term19 d' d'' n p d''').
Proof. exact (TRANS (@lem1252283 p d' d'' n d''') (@lem1252349 d' d'' n p d''')). Qed.
Lemma lem1252351 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term4 p n d' d'' d''') = (term19 d' d'' n p d''').
Proof. exact (TRANS (@lem1252183 p n d' d'' d''') (@lem1252350 d' d'' n p d''')). Qed.
Lemma lem1252352 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1252353 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term20 p n d' d'' d''') = (term21 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1252352) (@lem1252351 d' d'' n p d''')). Qed.
Lemma lem1252355 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252356 (n : nat) (p : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term22 p n d' d'' d''') = (term22 n p d' d'' d''').
Proof. exact (@lem1252355 n p (term23 d' d'' d''')). Qed.
Lemma lem1252364 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252365 (d' : nat) (p : nat) (d'' : nat) (d''' : nat) : (term24 p d' d'' d''') = (term24 d' p d'' d''').
Proof. exact (@lem1252364 d' p (term25 d'' d''')). Qed.
Lemma lem1252373 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252374 (p : nat) (d'' : nat) (d''' : nat) : (term23 p d'' d''') = (term26 p d'' d''').
Proof. exact (@lem1252373 d'' p (term13 d'' d''')). Qed.
Lemma lem1252382 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252383 (d'' : nat) (p : nat) (d''' : nat) : (term10 p d'' d''') = (term10 d'' p d''').
Proof. exact (@lem1252382 d'' p (S d''')). Qed.
Lemma lem1252393 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1252394 (d'' : nat) (p : nat) (d''' : nat) : (term26 p d'' d''') = (term17 d'' p d''').
Proof. exact (MK_COMB (@lem1252393 d'') (@lem1252383 d'' p d''')). Qed.
Lemma lem1252401 (d'' : nat) (p : nat) (d''' : nat) : (term23 p d'' d''') = (term17 d'' p d''').
Proof. exact (TRANS (@lem1252374 p d'' d''') (@lem1252394 d'' p d''')). Qed.
Lemma lem1252402 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252403 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term24 d' p d'' d''') = (term15 d' d'' p d''').
Proof. exact (MK_COMB (@lem1252402 d') (@lem1252401 d'' p d''')). Qed.
Lemma lem1252410 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term24 p d' d'' d''') = (term15 d' d'' p d''').
Proof. exact (TRANS (@lem1252365 d' p d'' d''') (@lem1252403 d' d'' p d''')). Qed.
Lemma lem1252411 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1252412 (n : nat) (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term22 n p d' d'' d''') = (term16 n d' d'' p d''').
Proof. exact (MK_COMB (@lem1252411 n) (@lem1252410 d' d'' p d''')). Qed.
Lemma lem1252414 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252415 (d' : nat) (n : nat) (d'' : nat) (p : nat) (d''' : nat) : (term16 n d' d'' p d''') = (term16 d' n d'' p d''').
Proof. exact (@lem1252414 d' n (term17 d'' p d''')). Qed.
Lemma lem1252423 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252424 (n : nat) (d'' : nat) (p : nat) (d''' : nat) : (term15 n d'' p d''') = (term14 n d'' p d''').
Proof. exact (@lem1252423 d'' n (term10 d'' p d''')). Qed.
Lemma lem1252432 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252433 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term12 n d'' p d''') = (term12 d'' n p d''').
Proof. exact (@lem1252432 d'' n (term13 p d''')). Qed.
Lemma lem1252449 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1252450 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term14 n d'' p d''') = (term18 d'' n p d''').
Proof. exact (MK_COMB (@lem1252449 d'') (@lem1252433 d'' n p d''')). Qed.
Lemma lem1252457 (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term15 n d'' p d''') = (term18 d'' n p d''').
Proof. exact (TRANS (@lem1252424 n d'' p d''') (@lem1252450 d'' n p d''')). Qed.
Lemma lem1252458 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252459 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term16 d' n d'' p d''') = (term19 d' d'' n p d''').
Proof. exact (MK_COMB (@lem1252458 d') (@lem1252457 d'' n p d''')). Qed.
Lemma lem1252466 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term16 n d' d'' p d''') = (term19 d' d'' n p d''').
Proof. exact (TRANS (@lem1252415 d' n d'' p d''') (@lem1252459 d' d'' n p d''')). Qed.
Lemma lem1252467 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term22 n p d' d'' d''') = (term19 d' d'' n p d''').
Proof. exact (TRANS (@lem1252412 n d' d'' p d''') (@lem1252466 d' d'' n p d''')). Qed.
Lemma lem1252468 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : (term22 p n d' d'' d''') = (term19 d' d'' n p d''').
Proof. exact (TRANS (@lem1252356 n p d' d'' d''') (@lem1252467 d' d'' n p d''')). Qed.
Lemma lem1252469 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : ((term4 p n d' d'' d''') = (term22 p n d' d'' d''')) = ((term19 d' d'' n p d''') = (term19 d' d'' n p d''')).
Proof. exact (MK_COMB (@lem1252353 d' d'' n p d''') (@lem1252468 d' d'' n p d''')). Qed.
Lemma lem1252471 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1252472 (x : nat) : (x = x) = True.
Proof. exact (@lem1252471 nat x). Qed.
Lemma lem1252473 (d' : nat) (d'' : nat) (n : nat) (p : nat) (d''' : nat) : ((term19 d' d'' n p d''') = (term19 d' d'' n p d''')) = True.
Proof. exact (@lem1252472 (term19 d' d'' n p d''')). Qed.
Lemma lem1252474 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term4 p n d' d'' d''') = (term22 p n d' d'' d''')) = True.
Proof. exact (TRANS (@lem1252469 d' d'' n p d''') (@lem1252473 d' d'' n p d''')). Qed.
Lemma lem1252475 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : True = ((term4 p n d' d'' d''') = (term22 p n d' d'' d''')).
Proof. exact (SYM (@lem1252474 p n d' d'' d''')). Qed.
Lemma lem1252476 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term4 p n d' d'' d''') = (term22 p n d' d'' d''').
Proof. exact (EQ_MP (@lem1252475 p n d' d'' d''') (@lem0)). Qed.
Lemma lem1252477 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1252478 (p : nat) (n : nat) (d' : nat) : (term2 p d' n) = (term3 p n d').
Proof. exact (MK_COMB (@lem1252477) (@lem1252178 p n d')). Qed.
Lemma lem1252479 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term0 p d' n) = (term4 p n d' d'' d''')) = ((term1 p n d') = (term22 p n d' d'' d''')).
Proof. exact (MK_COMB (@lem1252478 p n d') (@lem1252476 p n d' d'' d''')). Qed.
Lemma lem1252480 (m : nat) : term27 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1252481 (m : nat) : (term27 m) = (term28 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem1252482 (m : nat) : term28 m.
Proof. exact (EQ_MP (@lem1252481 m) (@lem1252480 m)). Qed.
Lemma lem1252483 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem1252482 m n). Qed.
Lemma lem1252484 (m : nat) (n : nat) : (term29 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem1252492 (m : nat) : term30 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1252493 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem1252494 (m : nat) : term31 m.
Proof. exact (EQ_MP (@lem1252493 m) (@lem1252492 m)). Qed.
Lemma lem1252495 (m : nat) (n : nat) : term32 m n.
Proof. exact (@lem1252494 m n). Qed.
Lemma lem1252496 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1252497 (m : nat) (n : nat) : term33 m n.
Proof. exact (EQ_MP (@lem1252496 m n) (@lem1252495 m n)). Qed.
Lemma lem1252498 (m : nat) (n : nat) (p : nat) : term34 m n p.
Proof. exact (@lem1252497 m n p). Qed.
Lemma lem1252499 (m : nat) (n : nat) (p : nat) : (term34 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term34 m n p)). Qed.
Lemma lem1252502 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1252499 m n p) (@lem1252498 m n p)). Qed.
Lemma lem1252503 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term1 p n d') = (term22 p n d' d'' d''')) = ((Nat.add n d') = (term24 n d' d'' d''')).
Proof. exact (@lem1252502 p (Nat.add n d') (term24 n d' d'' d''')). Qed.
Lemma lem1252505 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1252499 m n p) (@lem1252498 m n p)). Qed.
Lemma lem1252506 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((Nat.add n d') = (term24 n d' d'' d''')) = (d' = (term23 d' d'' d''')).
Proof. exact (@lem1252505 n d' (term23 d' d'' d''')). Qed.
Lemma lem1252508 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1252484 m n) (@lem1252483 m n)). Qed.
Lemma lem1252513 (d' : nat) (d'' : nat) (d''' : nat) : (d' = (term23 d' d'' d''')) = ((term25 d'' d''') = (NUMERAL 0)).
Proof. exact (@lem1252508 d' (term25 d'' d''')). Qed.
Lemma lem1252514 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((Nat.add n d') = (term24 n d' d'' d''')) = ((term25 d'' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1252506 n d' d'' d''') (@lem1252513 d' d'' d''')). Qed.
Lemma lem1252515 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term1 p n d') = (term22 p n d' d'' d''')) = ((term25 d'' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1252503 p n d' d'' d''') (@lem1252514 n d' d'' d''')). Qed.
Lemma lem1252516 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term35 p n d' d'' d''') = (term35 p n d' d'' d''').
Proof. exact (eq_refl (term35 p n d' d'' d''')). Qed.
Lemma lem1252517 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (((term0 p d' n) = (term4 p n d' d'' d''')) = ((term1 p n d') = (term22 p n d' d'' d'''))) = (((term0 p d' n) = (term4 p n d' d'' d''')) = ((term25 d'' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1252516 p n d' d'' d''') (@lem1252515 p n d' d'' d''')). Qed.
Lemma lem1252518 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term0 p d' n) = (term4 p n d' d'' d''')) = ((term25 d'' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1252517 p n d' d'' d''') (@lem1252479 p n d' d'' d''')). Qed.
Lemma lem1252519 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1252520 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term36 p n d' d'' d''') = (term37 d'' d''').
Proof. exact (MK_COMB (@lem1252519) (@lem1252518 p n d' d'' d''')). Qed.
Lemma lem1252521 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1252522 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term38 p n d' d'' d''') = (term39 d'' d''').
Proof. exact (MK_COMB (@lem1252520 p n d' d'' d''') (@lem1252521)). Qed.
Lemma lem1252523 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term39 d'' d''') = (term38 p n d' d'' d''').
Proof. exact (SYM (@lem1252522 p n d' d'' d''')). Qed.
