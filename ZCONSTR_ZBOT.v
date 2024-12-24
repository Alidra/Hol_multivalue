Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ZCONSTR_ZBOT_term_abbrevs.
Require Import INJN_INJ_spec.
Require Import INJP_INJ_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import ZCONSTR_spec.
Require Import thm0_spec.
Require Import thm1058213_spec.
Require Import thm1058227_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1844_spec.
Require Import thm82_spec.
Lemma lem1058229 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1058230 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1058231 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1058230 n) (@lem1058229 n)). Qed.
Lemma lem1058232 (n : nat) : term2 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1058245 {A : Type'} (n1 : nat) : term3 A n1.
Proof. exact (@lem1055573 A n1). Qed.
Lemma lem1058246 {A : Type'} (n1 : nat) : (term3 A n1) = (term4 A n1).
Proof. exact (eq_refl (term3 A n1)). Qed.
Lemma lem1058247 {A : Type'} (n1 : nat) : term4 A n1.
Proof. exact (EQ_MP (@lem1058246 A n1) (@lem1058245 A n1)). Qed.
Lemma lem1058248 {A : Type'} (n1 : nat) (n2 : nat) : term5 A n1 n2.
Proof. exact (@lem1058247 A n1 n2). Qed.
Lemma lem1058249 {A : Type'} (n1 : nat) (n2 : nat) : (term5 A n1 n2) = (((@INJN A n1) = (@INJN A n2)) = (n1 = n2)).
Proof. exact (eq_refl (term5 A n1 n2)). Qed.
Lemma lem1058251 {A : Type'} (f1 : type1597 A) : term6 A f1.
Proof. exact (@lem1057571 A f1). Qed.
Lemma lem1058252 {A : Type'} (f1 : type1597 A) : (term6 A f1) = (term7 A f1).
Proof. exact (eq_refl (term6 A f1)). Qed.
Lemma lem1058253 {A : Type'} (f1 : type1597 A) : term7 A f1.
Proof. exact (EQ_MP (@lem1058252 A f1) (@lem1058251 A f1)). Qed.
Lemma lem1058254 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) : term8 A f1 f1'.
Proof. exact (@lem1058253 A f1 f1'). Qed.
Lemma lem1058255 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) : (term8 A f1 f1') = (term9 A f1 f1').
Proof. exact (eq_refl (term8 A f1 f1')). Qed.
Lemma lem1058256 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) : term9 A f1 f1'.
Proof. exact (EQ_MP (@lem1058255 A f1 f1') (@lem1058254 A f1 f1')). Qed.
Lemma lem1058257 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) : term10 A f1 f1' f2.
Proof. exact (@lem1058256 A f1 f1' f2). Qed.
Lemma lem1058258 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) : (term10 A f1 f1' f2) = (term11 A f1 f1' f2).
Proof. exact (eq_refl (term10 A f1 f1' f2)). Qed.
Lemma lem1058259 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) : term11 A f1 f1' f2.
Proof. exact (EQ_MP (@lem1058258 A f1 f1' f2) (@lem1058257 A f1 f1' f2)). Qed.
Lemma lem1058260 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : term12 A f1 f1' f2 f2'.
Proof. exact (@lem1058259 A f1 f1' f2 f2'). Qed.
Lemma lem1058261 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : (term12 A f1 f1' f2 f2') = (((@INJP A f1 f2) = (@INJP A f1' f2')) = (term13 A f1 f1' f2 f2')).
Proof. exact (eq_refl (term12 A f1 f1' f2 f2')). Qed.
Lemma lem1058263 {A : Type'} (c : nat) : term14 A c.
Proof. exact (@lem1057928 A c). Qed.
Lemma lem1058264 {A : Type'} (c : nat) : (term14 A c) = (term15 A c).
Proof. exact (eq_refl (term14 A c)). Qed.
Lemma lem1058265 {A : Type'} (c : nat) : term15 A c.
Proof. exact (EQ_MP (@lem1058264 A c) (@lem1058263 A c)). Qed.
Lemma lem1058266 {A : Type'} (c : nat) (i : A) : term16 A c i.
Proof. exact (@lem1058265 A c i). Qed.
Lemma lem1058267 {A : Type'} (c : nat) (i : A) : (term16 A c i) = (term17 A c i).
Proof. exact (eq_refl (term16 A c i)). Qed.
Lemma lem1058268 {A : Type'} (c : nat) (i : A) : term17 A c i.
Proof. exact (EQ_MP (@lem1058267 A c i) (@lem1058266 A c i)). Qed.
Lemma lem1058269 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term18 A c i r.
Proof. exact (@lem1058268 A c i r). Qed.
Lemma lem1058270 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term18 A c i r) = ((@ZCONSTR A c i r) = (term19 A c i r)).
Proof. exact (eq_refl (term18 A c i r)). Qed.
Lemma lem1058287 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (@ZCONSTR A c i r) = (term19 A c i r).
Proof. exact (EQ_MP (@lem1058270 A c i r) (@lem1058269 A c i r)). Qed.
Lemma lem1058288 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (@ZCONSTR A c i r) = (term19 A c i r).
Proof. exact (@lem1058287 A c i r). Qed.
Lemma lem1058289 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1058290 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term20 A c i r) = (term21 A c i r).
Proof. exact (MK_COMB (@lem1058289 A) (@lem1058288 A c i r)). Qed.
Lemma lem1058292 {A : Type'} : (@ZBOT A) = (term22 A).
Proof. exact (TRANS (@lem1058213 A) (@lem1058227 A)). Qed.
Lemma lem1058293 {A : Type'} (c : nat) (i : A) (r : type1600 A) : ((@ZCONSTR A c i r) = (@ZBOT A)) = ((term19 A c i r) = (term22 A)).
Proof. exact (MK_COMB (@lem1058290 A c i r) (@lem1058292 A)). Qed.
Lemma lem1058295 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : ((@INJP A f1 f2) = (@INJP A f1' f2')) = (term13 A f1 f1' f2 f2').
Proof. exact (EQ_MP (@lem1058261 A f1 f1' f2 f2') (@lem1058260 A f1 f1' f2 f2')). Qed.
Lemma lem1058296 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : ((@INJP A f1 f2) = (@INJP A f1' f2')) = (term13 A f1 f1' f2 f2').
Proof. exact (@lem1058295 A f1 f1' f2 f2'). Qed.
Lemma lem1058297 {A : Type'} (c : nat) (i : A) (r : type1600 A) : ((term19 A c i r) = (term22 A)) = (term23 A c i r).
Proof. exact (@lem1058296 A (term24 A c) (term25 A) (term26 A i r) (term27 A)). Qed.
Lemma lem1058301 {A : Type'} (n1 : nat) (n2 : nat) : ((@INJN A n1) = (@INJN A n2)) = (n1 = n2).
Proof. exact (EQ_MP (@lem1058249 A n1 n2) (@lem1058248 A n1 n2)). Qed.
Lemma lem1058302 {A : Type'} (c : nat) : ((term24 A c) = (term25 A)) = ((S c) = (NUMERAL 0)).
Proof. exact (@lem1058301 A (S c) (NUMERAL 0)). Qed.
Lemma lem1058304 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1058232 n (@lem1058231 n)). Qed.
Lemma lem1058305 (c : nat) : ((S c) = (NUMERAL 0)) = False.
Proof. exact (@lem1058304 c). Qed.
Lemma lem1058306 {A : Type'} (c : nat) : ((term24 A c) = (term25 A)) = False.
Proof. exact (TRANS (@lem1058302 A c) (@lem1058305 c)). Qed.
Lemma lem1058307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1058308 {A : Type'} (c : nat) : (term28 A c) = (and False).
Proof. exact (MK_COMB (@lem1058307) (@lem1058306 A c)). Qed.
Lemma lem1058311 {A : Type'} (i : A) (r : type1600 A) : ((term26 A i r) = (term27 A)) = ((term26 A i r) = (term27 A)).
Proof. exact (eq_refl ((term26 A i r) = (term27 A))). Qed.
Lemma lem1058312 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term23 A c i r) = (term29 A i r).
Proof. exact (MK_COMB (@lem1058308 A c) (@lem1058311 A i r)). Qed.
Lemma lem1058314 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1058315 {A : Type'} (i : A) (r : type1600 A) : (term29 A i r) = False.
Proof. exact (@lem1058314 ((term26 A i r) = (term27 A))). Qed.
Lemma lem1058316 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term23 A c i r) = False.
Proof. exact (TRANS (@lem1058312 A c i r) (@lem1058315 A i r)). Qed.
Lemma lem1058317 {A : Type'} (c : nat) (i : A) (r : type1600 A) : ((term19 A c i r) = (term22 A)) = False.
Proof. exact (TRANS (@lem1058297 A c i r) (@lem1058316 A c i r)). Qed.
Lemma lem1058318 {A : Type'} (c : nat) (i : A) (r : type1600 A) : ((@ZCONSTR A c i r) = (@ZBOT A)) = False.
Proof. exact (TRANS (@lem1058293 A c i r) (@lem1058317 A c i r)). Qed.
Lemma lem1058319 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1058320 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term30 A c i r) = (~ False).
Proof. exact (MK_COMB (@lem1058319) (@lem1058318 A c i r)). Qed.
Lemma lem1058322 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1058323 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term30 A c i r) = True.
Proof. exact (TRANS (@lem1058320 A c i r) (@lem1058322)). Qed.
Lemma lem1058324 {A : Type'} (c : nat) (i : A) : (term31 A c i) = (term32 A).
Proof. exact (fun_ext (fun r : type1600 A => @lem1058323 A c i r)). Qed.
Lemma lem1058325 {A : Type'} : (@all (nat -> nat -> A -> Prop)) = (@all (nat -> nat -> A -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> A -> Prop))). Qed.
Lemma lem1058326 {A : Type'} (c : nat) (i : A) : (term33 A c i) = (term34 A).
Proof. exact (MK_COMB (@lem1058325 A) (@lem1058324 A c i)). Qed.
Lemma lem1058328 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1058329 {A : Type'} (t : Prop) : (term36 A t) = t.
Proof. exact (@lem1058328 (type1600 A) t). Qed.
Lemma lem1058330 {A : Type'} : (term34 A) = True.
Proof. exact (@lem1058329 A True). Qed.
Lemma lem1058331 {A : Type'} (c : nat) (i : A) : (term33 A c i) = True.
Proof. exact (TRANS (@lem1058326 A c i) (@lem1058330 A)). Qed.
Lemma lem1058332 {A : Type'} (c : nat) : (term37 A c) = (term38 A).
Proof. exact (fun_ext (fun i : A => @lem1058331 A c i)). Qed.
Lemma lem1058333 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1058334 {A : Type'} (c : nat) : (term39 A c) = (term40 A).
Proof. exact (MK_COMB (@lem1058333 A) (@lem1058332 A c)). Qed.
Lemma lem1058336 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1058337 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (@lem1058336 A t). Qed.
Lemma lem1058338 {A : Type'} : (term40 A) = True.
Proof. exact (@lem1058337 A True). Qed.
Lemma lem1058339 {A : Type'} (c : nat) : (term39 A c) = True.
Proof. exact (TRANS (@lem1058334 A c) (@lem1058338 A)). Qed.
Lemma lem1058340 {A : Type'} : (term41 A) = term42.
Proof. exact (fun_ext (fun c : nat => @lem1058339 A c)). Qed.
Lemma lem1058341 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1058342 {A : Type'} : (term43 A) = term44.
Proof. exact (MK_COMB (@lem1058341) (@lem1058340 A)). Qed.
Lemma lem1058344 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1058345 (t : Prop) : (term45 t) = t.
Proof. exact (@lem1058344 nat t). Qed.
Lemma lem1058346 : term44 = True.
Proof. exact (@lem1058345 True). Qed.
Lemma lem1058347 {A : Type'} : (term43 A) = True.
Proof. exact (TRANS (@lem1058342 A) (@lem1058346)). Qed.
Lemma lem1058348 {A : Type'} : True = (term43 A).
Proof. exact (SYM (@lem1058347 A)). Qed.
Lemma lem1058349 {A : Type'} : term43 A.
Proof. exact (EQ_MP (@lem1058348 A) (@lem0)). Qed.
