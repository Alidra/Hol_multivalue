Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7932263_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7637206_spec.
Require Import thm7640378_spec.
Require Import thm7931473_spec.
Require Import thm7931474_spec.
Require Import thm7931479_spec.
Require Import thm7931480_spec.
Require Import thm7931484_spec.
Require Import thm7931485_spec.
Require Import thm7931514_spec.
Require Import thm7931515_spec.
Require Import thm7931603_spec.
Require Import thm7932146_spec.
Lemma lem7932148 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term0 A B f s n.
Proof. exact (EQ_MP (@lem7931515 A B f s n) (@lem7931514 A B f s n)). Qed.
Lemma lem7932149 {A : Type'} (f : type46 A) (s : type48 A) (n : nat) : term1 A f s n.
Proof. exact (@lem7932148 (finite_sum A A) (tybit0 A) f s n). Qed.
Lemma lem7932150 {A : Type'} : term2 A.
Proof. exact (@lem7932149 A (@mktybit0 A) (@UNIV (finite_sum A A)) (term3 A)). Qed.
Lemma lem7932166 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7931485 A x) (@lem7931484 A x)). Qed.
Lemma lem7932167 {A : Type'} (x : finite_sum A A) : (@IN (finite_sum A A) x (@UNIV (finite_sum A A))) = True.
Proof. exact (@lem7932166 (finite_sum A A) x). Qed.
Lemma lem7932168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7932169 {A : Type'} (x : finite_sum A A) : (term4 A x) = (and True).
Proof. exact (MK_COMB (@lem7932168) (@lem7932167 A x)). Qed.
Lemma lem7932173 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7931485 A x) (@lem7931484 A x)). Qed.
Lemma lem7932174 {A : Type'} (x : finite_sum A A) : (@IN (finite_sum A A) x (@UNIV (finite_sum A A))) = True.
Proof. exact (@lem7932173 (finite_sum A A) x). Qed.
Lemma lem7932175 {A : Type'} (y : finite_sum A A) : (@IN (finite_sum A A) y (@UNIV (finite_sum A A))) = True.
Proof. exact (@lem7932174 A y). Qed.
Lemma lem7932176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7932177 {A : Type'} (y : finite_sum A A) : (term4 A y) = (and True).
Proof. exact (MK_COMB (@lem7932176) (@lem7932175 A y)). Qed.
Lemma lem7932179 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) : ((@mktybit0 A a) = (@mktybit0 A a')) = (a = a').
Proof. exact (EQ_MP (@lem7931480 A a a') (@lem7931479 A a a')). Qed.
Lemma lem7932180 {A : Type'} (a : finite_sum A A) (a' : finite_sum A A) : ((@mktybit0 A a) = (@mktybit0 A a')) = (a = a').
Proof. exact (@lem7932179 A a a'). Qed.
Lemma lem7932181 {A : Type'} (x : finite_sum A A) (y : finite_sum A A) : ((@mktybit0 A x) = (@mktybit0 A y)) = (x = y).
Proof. exact (@lem7932180 A x y). Qed.
Lemma lem7932184 {A : Type'} (x : finite_sum A A) (y : finite_sum A A) : (term5 A x y) = (term6 A x y).
Proof. exact (MK_COMB (@lem7932177 A y) (@lem7932181 A x y)). Qed.
Lemma lem7932186 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7932187 {A : Type'} (x : finite_sum A A) (y : finite_sum A A) : (term6 A x y) = (x = y).
Proof. exact (@lem7932186 (x = y)). Qed.
Lemma lem7932190 {A : Type'} (x : finite_sum A A) (y : finite_sum A A) : (term5 A x y) = (x = y).
Proof. exact (TRANS (@lem7932184 A x y) (@lem7932187 A x y)). Qed.
Lemma lem7932191 {A : Type'} (x : finite_sum A A) (y : finite_sum A A) : (term7 A x y) = (term6 A x y).
Proof. exact (MK_COMB (@lem7932169 A x) (@lem7932190 A x y)). Qed.
Lemma lem7932193 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7932194 {A : Type'} (x : finite_sum A A) (y : finite_sum A A) : (term6 A x y) = (x = y).
Proof. exact (@lem7932193 (x = y)). Qed.
Lemma lem7932197 {A : Type'} (x : finite_sum A A) (y : finite_sum A A) : (term7 A x y) = (x = y).
Proof. exact (TRANS (@lem7932191 A x y) (@lem7932194 A x y)). Qed.
Lemma lem7932198 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7932199 {A : Type'} (x : finite_sum A A) (y : finite_sum A A) : (term8 A x y) = (term9 A x y).
Proof. exact (MK_COMB (@lem7932198) (@lem7932197 A x y)). Qed.
Lemma lem7932202 {A : Type'} (x : finite_sum A A) (y : finite_sum A A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem7932203 {A : Type'} (x : finite_sum A A) (y : finite_sum A A) : (term10 A x y) = (term11 A x y).
Proof. exact (MK_COMB (@lem7932199 A x y) (@lem7932202 A x y)). Qed.
Lemma lem7932207 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7932208 {A : Type'} (x : finite_sum A A) (y : finite_sum A A) : (term11 A x y) = True.
Proof. exact (@lem7932207 (x = y)). Qed.
Lemma lem7932209 {A : Type'} (x : finite_sum A A) (y : finite_sum A A) : (term10 A x y) = True.
Proof. exact (TRANS (@lem7932203 A x y) (@lem7932208 A x y)). Qed.
Lemma lem7932210 {A : Type'} (x : finite_sum A A) : (term12 A x) = (term13 A).
Proof. exact (fun_ext (fun y : finite_sum A A => @lem7932209 A x y)). Qed.
Lemma lem7932211 {A : Type'} : (@all (finite_sum A A)) = (@all (finite_sum A A)).
Proof. exact (eq_refl (@all (finite_sum A A))). Qed.
Lemma lem7932212 {A : Type'} (x : finite_sum A A) : (term14 A x) = (term15 A).
Proof. exact (MK_COMB (@lem7932211 A) (@lem7932210 A x)). Qed.
Lemma lem7932214 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7932215 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (@lem7932214 (finite_sum A A) t). Qed.
Lemma lem7932216 {A : Type'} : (term15 A) = True.
Proof. exact (@lem7932215 A True). Qed.
Lemma lem7932217 {A : Type'} (x : finite_sum A A) : (term14 A x) = True.
Proof. exact (TRANS (@lem7932212 A x) (@lem7932216 A)). Qed.
Lemma lem7932218 {A : Type'} : (term18 A) = (term13 A).
Proof. exact (fun_ext (fun x : finite_sum A A => @lem7932217 A x)). Qed.
Lemma lem7932219 {A : Type'} : (@all (finite_sum A A)) = (@all (finite_sum A A)).
Proof. exact (eq_refl (@all (finite_sum A A))). Qed.
Lemma lem7932220 {A : Type'} : (term19 A) = (term15 A).
Proof. exact (MK_COMB (@lem7932219 A) (@lem7932218 A)). Qed.
Lemma lem7932222 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7932223 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (@lem7932222 (finite_sum A A) t). Qed.
Lemma lem7932224 {A : Type'} : (term15 A) = True.
Proof. exact (@lem7932223 A True). Qed.
Lemma lem7932225 {A : Type'} : (term19 A) = True.
Proof. exact (TRANS (@lem7932220 A) (@lem7932224 A)). Qed.
Lemma lem7932226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7932227 {A : Type'} : (term20 A) = (and True).
Proof. exact (MK_COMB (@lem7932226) (@lem7932225 A)). Qed.
Lemma lem7932228 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (eq_refl (term21 A)). Qed.
Lemma lem7932229 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (MK_COMB (@lem7932227 A) (@lem7932228 A)). Qed.
Lemma lem7932231 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7932232 {A : Type'} : (term23 A) = (term21 A).
Proof. exact (@lem7932231 (term21 A)). Qed.
Lemma lem7932233 {A : Type'} : (term22 A) = (term21 A).
Proof. exact (TRANS (@lem7932229 A) (@lem7932232 A)). Qed.
Lemma lem7932234 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (SYM (@lem7932233 A)). Qed.
Lemma lem7932236 {M N : Type'} : term24 M N.
Proof. exact (EQ_MP (@lem7637206 M N) (@lem7640378 M N)). Qed.
Lemma lem7932237 {A : Type'} : term25 A.
Proof. exact (@lem7932236 A A). Qed.
Lemma lem7932241 (n : nat) : (Nat.add n n) = (term26 n).
Proof. exact (EQ_MP (@lem7931474 n) (@lem7931473 n)). Qed.
Lemma lem7932242 {A : Type'} : (term27 A) = (term3 A).
Proof. exact (@lem7932241 (@dimindex A (@UNIV A))). Qed.
Lemma lem7932245 {A : Type'} : (@HAS_SIZE (finite_sum A A) (@UNIV (finite_sum A A))) = (@HAS_SIZE (finite_sum A A) (@UNIV (finite_sum A A))).
Proof. exact (eq_refl (@HAS_SIZE (finite_sum A A) (@UNIV (finite_sum A A)))). Qed.
Lemma lem7932246 {A : Type'} : (term25 A) = (term21 A).
Proof. exact (MK_COMB (@lem7932245 A) (@lem7932242 A)). Qed.
Lemma lem7932247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7932248 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (MK_COMB (@lem7932247) (@lem7932246 A)). Qed.
Lemma lem7932251 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (eq_refl (term21 A)). Qed.
Lemma lem7932252 {A : Type'} : (term30 A) = (term31 A).
Proof. exact (MK_COMB (@lem7932248 A) (@lem7932251 A)). Qed.
Lemma lem7932254 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7932255 {A : Type'} : (term31 A) = True.
Proof. exact (@lem7932254 (term21 A)). Qed.
Lemma lem7932256 {A : Type'} : (term30 A) = True.
Proof. exact (TRANS (@lem7932252 A) (@lem7932255 A)). Qed.
Lemma lem7932257 {A : Type'} : True = (term30 A).
Proof. exact (SYM (@lem7932256 A)). Qed.
Lemma lem7932258 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem7932257 A) (@lem0)). Qed.
Lemma lem7932259 {A : Type'} : term21 A.
Proof. exact (@lem7932258 A (@lem7932237 A)). Qed.
Lemma lem7932260 {A : Type'} : term22 A.
Proof. exact (EQ_MP (@lem7932234 A) (@lem7932259 A)). Qed.
Lemma lem7932261 {A : Type'} : term32 A.
Proof. exact (@lem7932150 A (@lem7932260 A)). Qed.
Lemma lem7932262 {A : Type'} (h1 : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A)))) : term33 A.
Proof. exact (EQ_MP (@lem7931603 A h1) (@lem7932261 A)). Qed.
Lemma lem7932263 {A : Type'} : ((@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A)))) = (term33 A).
Proof. exact (prop_ext (fun h1 : (@UNIV (tybit0 A)) = (@IMAGE (finite_sum A A) (tybit0 A) (@mktybit0 A) (@UNIV (finite_sum A A))) => @lem7932262 A h1) (fun h1 : term33 A => @lem7932146 A)). Qed.
